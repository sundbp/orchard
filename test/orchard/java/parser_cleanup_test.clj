(ns orchard.java.parser-cleanup-test
  "Regression coverage for the temporary resources each Java source parse
  allocates: a temporary directory, the Java source copied into it, and a
  compiler file manager.

  For every `orchard.java.parser-next/source-info` invocation the parser owns
  exactly these artifacts and must release all of them, on success and on
  every failure path, without shortening the lifetime that the returned
  doclet environment needs.

  The checks observe the parser's actual allocations through a narrow
  observer on `clojure.java.io/file` construction: the original `File` value
  is returned unchanged, and only the current test thread's parser-owned
  paths (temporary directories named like the parser's `tmp*` prefix and the
  source file inside them) are recorded. There is no shared temporary
  directory census anywhere in this namespace. When the unpatched parser
  leaks, the harness deletes exactly the recorded artifacts in its teardown,
  after the assertions have captured their state; that teardown is not the
  parser fix.

  Self-contained: this namespace uses only Clojure, the JDK, and Orchard, so
  it runs both in orchard's own test suite and in the resident REPL of an
  embedding application. It resolves parser vars at call time, so it works
  with any implementation version loaded into the namespace, and the tests
  are order-independent."
  (:require
   [clojure.java.io :as io]
   [clojure.test :refer [deftest is testing]]
   [orchard.java.parser-next :as parser]
   [orchard.java.source-files :as src-files]
   [orchard.misc :as misc])
  (:import
   (java.io File)
   (java.nio.file Files)
   (java.nio.file.attribute FileAttribute)))

(def ^:private jdk11+?
  "The parser requires JDK 11 or newer."
  (>= misc/java-api-version 11))

(def ^:private lru-map-class-sym
  "A class whose Java source ships inside the Orchard artifact itself."
  'mx.cider.orchard.LruMap)

(def ^:private jdk-sources-present?
  "True when the running JDK ships readable sources, in which case the
  module-backed source lookup can be exercised end to end."
  (some? (src-files/class->source-file-url java.util.HashMap)))

(when (and jdk11+? (not jdk-sources-present?))
  (println "orchard.java.parser-cleanup-test: module-backed source lookup not"
           "exercised - no readable JDK sources (src.zip) on this machine;"
           "recorded as a coverage limitation, not a pass."))

(defn- new-fixture-root
  "Create a fresh temporary root directory for this namespace's own fixture
  files. The harness owns and removes exactly this directory."
  ^File [prefix]
  (.toFile (Files/createTempDirectory prefix (into-array FileAttribute []))))

(defn- delete-tree!
  "Delete `f`, recursively when it is a directory. Used only on paths this
  namespace itself created or recorded."
  [^File f]
  (when (.isDirectory f)
    (doseq [^File child (.listFiles f)]
      (delete-tree! child)))
  (.delete f))

(defn- owned-path-order
  "Order recorded paths deepest first, so teardown removes a recorded file
  before the directory that contains it."
  [^File a ^File b]
  (compare (.getAbsolutePath b) (.getAbsolutePath a)))

(defn- observe-owned-paths
  "Run `f` and return `[result owned-paths]`. While `f` runs, record every
  parser-owned path constructed through `clojure.java.io/file` on the current
  test thread: files whose parent is a directory named like the parser's
  `tmp<digits>` temporary directories, plus those parent directories
  themselves. The observer returns the original `File` unchanged and changes
  nothing about the parser's behavior or output."
  [f]
  (let [owned    (atom (sorted-set-by owned-path-order))
        me       (.getId (Thread/currentThread))
        original io/file]
    (with-redefs [io/file (fn [& args]
                            (let [file (apply original args)]
                              (when (and (= 2 (count args))
                                         (instance? File (first args))
                                         (instance? File file)
                                         (= me (.getId (Thread/currentThread)))
                                         (re-matches #"tmp\d+"
                                                     (.. ^File file getParentFile getName)))
                                (swap! owned conj file)
                                (swap! owned conj (.getParentFile ^File file)))
                              file))]
      [(f) @owned])))

(defn- harness-cleanup-owned!
  "Remove exactly the artifacts the harness recorded, and only after the
  assertions have captured their state. Baseline runs leak; this teardown
  keeps the host clean without being the parser fix."
  [owned]
  (doseq [^File path owned]
    (when (.exists path)
      (delete-tree! path))))

(defn- member-infos
  "Flatten a source-info member index to individual member info maps."
  [info]
  (mapcat vals (vals (:members info))))

(defn- assert-usable-source-info
  "Assert that `info` carries the class identity, source position,
  documentation, and member argument information that source parsing exists
  to provide."
  [info expected-class-sym]
  (testing "source-info returns usable information"
    (is (map? info))
    (is (= expected-class-sym (:class info)))
    (is (pos-int? (:line info)))
    (is (seq (:doc-fragments info)))
    (is (seq (:members info)))
    (is (some seq (map :argnames (member-infos info))))))

(defn- assert-no-owned-artifacts
  "Assert that every recorded parser-owned path is gone from disk."
  [owned]
  (testing "the parser-owned source file and directory are gone"
    (is (seq owned) "the harness observed the parser's temporary paths")
    (is (every? #(not (.exists ^File %)) owned))))

(when jdk11+?
  (deftest success-releases-owned-temporary-resources
    (testing "successful source-info"
      (dotimes [_ 2]
        (let [[info owned] (observe-owned-paths #(parser/source-info lru-map-class-sym))]
          (try
            (assert-usable-source-info info lru-map-class-sym)
            (assert-no-owned-artifacts owned)
            (finally (harness-cleanup-owned! owned)))))))

  (deftest invalid-source-fails-informatively-and-releases-owned-resources
    (testing "invalid Java source"
      (let [fixture-root (new-fixture-root "orchard-parser-cleanup-invalid")
            invalid-file (io/file fixture-root "Broken.java")
            _            (spit invalid-file "class Broken { void f() { int x = ; } }")
            broken-url   (-> invalid-file .toURI .toURL)
            [result owned] (observe-owned-paths
                            #(try
                               (parser/source-info clojure.lang.PersistentVector broken-url)
                               ::no-throw
                               (catch Exception e
                                 {:message (ex-message e)
                                  :data (ex-data e)})))]
        (try
          (testing "the real compiler reports the parse failure"
            (is (map? result))
            (is (= "Failed to parse Java source code" (:message result)))
            (is (map? (:data result)))
            (is (re-find #"(?i)error" (str (:out (:data result))))))
          (assert-no-owned-artifacts owned)
          (finally
            (harness-cleanup-owned! owned)
            (delete-tree! fixture-root))))))

  (deftest unreadable-source-fails-and-releases-owned-resources
    (testing "source read/copy failure after directory creation"
      (let [fixture-root (new-fixture-root "orchard-parser-cleanup-unreadable")
            ;; A directory URL fails deterministically when the parser tries to
            ;; read the source, without depending on filesystem permissions.
            dir-url      (-> fixture-root .toURI .toURL)
            [result owned] (observe-owned-paths
                            #(try
                               (parser/source-info clojure.lang.PersistentVector dir-url)
                               ::no-throw
                               (catch Exception e
                                 {:message (ex-message e)
                                  :type (class e)})))]
        (try
          (testing "the original read failure propagates"
            (is (map? result))
            (is (not= ::no-throw result))
            (is (isa? (:type result) java.io.IOException)))
          (assert-no-owned-artifacts owned)
          (finally
            (harness-cleanup-owned! owned)
            (delete-tree! fixture-root))))))

  (deftest traversal-failure-preserves-primary-error-and-releases-owned-resources
    (testing "failure during source-info traversal"
      (let [[result owned]
            (observe-owned-paths
             #(try
                (with-redefs [parser/parse-info (fn [_element _env]
                                                  (throw (ex-info "injected traversal failure"
                                                                  {:injected? true})))]
                  (parser/source-info lru-map-class-sym)
                  ::no-throw)
                (catch Exception e
                  {:message (ex-message e)
                   :data (ex-data e)})))]
        (try
          (testing "the primary traversal error is preserved"
            (is (map? result))
            (is (= "injected traversal failure" (:message result)))
            (is (true? (get-in result [:data :injected?]))))
          (assert-no-owned-artifacts owned)
          (finally (harness-cleanup-owned! owned))))))

  (when jdk-sources-present?
    (deftest module-backed-lookup-releases-owned-temporary-resources
      (testing "module-backed source lookup"
        (let [[info owned] (observe-owned-paths #(parser/source-info 'java.util.HashMap))]
          (try
            (assert-usable-source-info info 'java.util.HashMap)
            (assert-no-owned-artifacts owned)
            (finally (harness-cleanup-owned! owned))))))))

;; Run from a REPL with: (clojure.test/run-tests 'orchard.java.parser-cleanup-test)
