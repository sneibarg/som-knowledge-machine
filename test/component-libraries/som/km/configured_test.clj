(ns som.km.configured-test
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.configured :as configured]
            [som.km.frame :as frame]
            [som.km.repl :as repl]
            [som.km.startup :as startup]))

(defn- slash [path]
  (str/replace (str path) "\\" "/"))

(defn- delete-tree [^java.io.File file]
  (when (.isDirectory file)
    (doseq [child (.listFiles file)]
      (delete-tree child)))
  (.delete file))

(defn- write-km [dir name text]
  (let [file (io/file dir name)]
    (io/make-parents file)
    (spit file text :encoding "UTF-8")))

(deftest the-component-libraries-stay-in-order
  (let [entries (configured/libraries
                 (configured/read-config
                  "{:component-libraries [\"one\\\\two\" \"three\"]}"))]
    (is (= ["component library one/two" "component library three"]
           (mapv :label entries)))
    (is (= ["(load-lib \"one/two\" :silent t)"
            "(load-lib \"three\" :silent t)"]
           (mapv :expression entries)))))

(deftest an-empty-section-names-no-libraries
  (is (= [] (configured/libraries
             (configured/read-config "{:component-libraries []}")))))

(deftest other-sections-stay-on-the-configuration
  (is (= 1 (:later (configured/read-config
                    "{:component-libraries [] :later 1}")))))

(deftest a-configuration-without-the-section-is-refused
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo
       #"needs a :component-libraries section"
       (configured/read-config "{}"))))

(deftest a-string-is-not-a-sequence-of-directories
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo
       #"sequence of directory paths"
       (configured/read-config "{:component-libraries \"src\"}"))))

(deftest an-entry-that-is-not-a-path-is-refused
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo
       #"directory path"
       (configured/read-config "{:component-libraries [1]}"))))

(deftest unreadable-text-is-refused
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo
       #"not readable EDN"
       (configured/read-config "{"))))

(def ^:private all-build
  ["src/resources/km-component-library/rkf-clib/components/core"
   "src/resources/km-component-library/rkf-clib/components/specs"
   "src/resources/km-component-library/rkf-clib/components/science/shared"
   "src/resources/km-component-library/rkf-clib/components/science/biology"
   "src/resources/km-component-library/rkf-clib/components/science/physics"
   "src/resources/km-component-library/rkf-clib/components/science/chemistry"
   "src/resources/km-component-library/rkf-clib/components/bsp"
   "src/resources/som-component-library"])

(deftest the-shipped-configuration-is-config-edn
  (is (str/ends-with? (slash configured/config-path) "src/resources/config.edn"))
  (is (= all-build (:component-libraries (configured/read-shipped-config)))))

(deftest a-missing-file-is-refused
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo
       #"No configuration file"
       (configured/read-config-file "target/no-such-km-config.edn"))))

(deftest a-component-library-is-walked-recursively
  (let [root (.toFile (java.nio.file.Files/createTempDirectory
                       "km-config-"
                       (into-array java.nio.file.attribute.FileAttribute [])))
        config (io/file root "startup.edn")
        first-lib (io/file root "first")
        second-lib (io/file root "second")
        left-out (io/file root "left-out")]
    (try
      (write-km first-lib "Dog.km" "(Dog has (color (green)))\n")
      (write-km first-lib "nested/Cat.km" "(Cat has (color (green)))\n")
      (write-km second-lib "Bird.km" "(Bird has (color (green)))\n")
      (write-km left-out "Fish.km" "(Fish has (color (green)))\n")
      (spit config
            (str "{:component-libraries [\""
                 (slash first-lib) "\" \""
                 (slash second-lib) "\"]}\n")
            :encoding "UTF-8")
      (let [session (repl/session)
            entries (configured/libraries (configured/read-config-file config))]
        (startup/load-libraries session entries)
        (is (frame/known-frame? (:kb @session) (symbol "Dog")))
        (is (frame/known-frame? (:kb @session) (symbol "Cat")))
        (is (frame/known-frame? (:kb @session) (symbol "Bird")))
        (is (not (frame/known-frame? (:kb @session) (symbol "Fish")))))
      (finally
        (delete-tree root)))))
