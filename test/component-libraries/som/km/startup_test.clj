(ns som.km.startup-test
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.kb :as kb]
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

(deftest the-startup-expressions-name-both-libraries
  (let [[shipped som] (startup/libraries)]
    (is (= "the shipped component library" (:label shipped)))
    (is (= "(load-lib :silent t)" (:expression shipped)))
    (is (= "the Springs of MUD component library" (:label som)))
    (is (str/starts-with? (:expression som) "(load-lib \""))
    (is (str/ends-with? (:expression som) "\" :silent t)"))
    (is (str/includes? (:expression som) "som-component-library/"))
    (is (not (str/includes? (:expression som) "\\")))))

(deftest som-components-path-points-at-the-library
  (is (str/ends-with? (slash kb/som-components-path) "som-component-library/"))
  (is (.isFile (io/file kb/som-components-path "README.md")))
  (is (.isFile (io/file kb/som-components-path "Som-Level-Goal.km"))))

(deftest a-loaded-expression-stays-in-the-prompt-session
  (let [first-dir (.toFile (java.nio.file.Files/createTempDirectory
                            "km-start-a-"
                            (into-array java.nio.file.attribute.FileAttribute [])))
        second-dir (.toFile (java.nio.file.Files/createTempDirectory
                             "km-start-b-"
                             (into-array java.nio.file.attribute.FileAttribute [])))]
    (try
      (write-km first-dir "Red.km" "(Red has (color (green)))\n")
      (write-km second-dir "Blue.km" "(Blue has (color (green)))\n")
      (let [session (repl/session)
            first-result (startup/load-expression
                          session
                          (str "(load-lib \"" (slash first-dir) "\" :silent t)"))
            second-result (startup/load-expression
                           session
                           (str "(load-lib \"" (slash second-dir) "\" :silent t)"))]
        (is (empty? (:errors first-result)))
        (is (empty? (:errors second-result)))
        (is (frame/known-frame? (:kb second-result) (symbol "Red")))
        (is (frame/known-frame? (:kb second-result) (symbol "Blue")))
        (is (frame/known-frame? (:kb @session) (symbol "Red")))
        (is (frame/known-frame? (:kb @session) (symbol "Blue"))))
      (finally
        (delete-tree first-dir)
        (delete-tree second-dir)))))

(deftest the-springs-library-loads-into-a-prompt-session
  (let [session (repl/session)
        expression (:expression (second (startup/libraries)))
        result (startup/load-expression session expression)]
    (is (empty? (:errors result)) (pr-str (:errors result)))
    (is (frame/known-frame? (:kb @session) (symbol "Som-Level-Goal")))
    (is (frame/known-frame? (:kb @session) (symbol "Som-Goal-View")))))
