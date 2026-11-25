(ns som.km.resource-library-test
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is]]
            [som.kb :as kb]
            [som.km.engine :as engine]
            [som.km.print :as print]))

(deftest load-lib-reads-a-jar-without-directory-entries
  (let [file (.toFile (java.nio.file.Files/createTempFile
                        "km-resource-library-" ".jar"
                        (make-array java.nio.file.attribute.FileAttribute 0)))
        root "resources/packaged-test"
        paths [(str root "/A.km") (str root "/nested/")
               (str root "/nested/B.km") (str root "/z.km")
               (str root "/skip.lisp")]
        entries {"META-INF/som-knowledge-machine/resources.edn" (pr-str paths)
                 (str root "/A.km") "(JarFact has (color (red)))"
                 (str root "/nested/B.km") "(JarNested has (color (blue)))"
                 (str root "/z.km") "(JarLatin has (label (\"café\")))"
                 (str root "/skip.lisp") "(error \"Must not evaluate Lisp\")"}]
    (try
      (with-open [out (java.util.jar.JarOutputStream. (io/output-stream file))]
        (doseq [[path text] entries]
          (.putNextEntry out (java.util.jar.JarEntry. path))
          (.write out (.getBytes text (if (= path (str root "/z.km"))
                                       "ISO-8859-1" "UTF-8")))
          (.closeEntry out)))
      (with-open [loader (java.net.URLClassLoader.
                         (into-array java.net.URL [(.toURL (.toURI file))])
                         (.getContextClassLoader (Thread/currentThread)))]
        (let [thread (Thread/currentThread)
              previous (.getContextClassLoader thread)]
          (try
            (.setContextClassLoader thread loader)
            (doseq [path [(str "classpath:" root) (str "src/" root)]]
              (let [session (engine/session)
                    loaded (engine/evaluate (str "(load-lib " (pr-str path) " :silent t)") session)]
                (is (= ["z" "skip" "B" "A"] (mapv :name (kb/traverse-directory path))))
                (is (empty? (:errors loaded)))
                (is (= "(red)" (print/km-format (:value (engine/evaluate "(the color of JarFact)" loaded)))))
                (is (= "(blue)" (print/km-format (:value (engine/evaluate "(the color of JarNested)" loaded)))))
                (is (= "(\"café\")" (print/km-format (:value (engine/evaluate "(the label of JarLatin)" loaded)))))
                (is (nil? (:value (engine/evaluate "(the color of JarFact)" session))))))
            (finally
              (.setContextClassLoader thread previous)))))
      (finally
        (.delete file)))))
