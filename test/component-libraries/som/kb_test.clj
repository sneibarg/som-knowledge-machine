(ns som.kb-test
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.kb :as kb]
            [som.km.engine :as engine]
            [som.km.frame :as frame]
            [som.km.loadkb :as loadkb]
            [som.km.print :as print]
            [som.km.repl :as repl]
            [som.km.term :as term]))

(defn- slash [path]
  (str/replace (str path) "\\" "/"))

(defn- delete-tree [^java.io.File file]
  (when (.isDirectory file)
    (doseq [child (.listFiles file)]
      (delete-tree child)))
  (.delete file))

(defn- write-file [dir relative text]
  (let [file (io/file dir relative)]
    (io/make-parents file)
    (spit file text :encoding "UTF-8")))

(defn- sample-library []
  (let [dir (.toFile (java.nio.file.Files/createTempDirectory
                      "km-clib-"
                      (into-array java.nio.file.attribute.FileAttribute [])))]
    (write-file dir "M.km" "(Jade has (color (green)))\n")
    (write-file dir "Skip.KM" "(SkipMarker has (color (skip)))\n")
    (write-file dir "a.km" "(Red has (color (green)))\n")
    (write-file dir "b.km" "(Blue has (color (green)))\n")
    (write-file dir "d.lisp" "(LispMarker has (color (lisp)))\n")
    (write-file dir "e.kml" "(KmlMarker has (color (kml)))\n")
    (.mkdirs (io/file dir "empty"))
    (write-file dir "sub/c.km" "(Gold has (color (green)))\n")
    (write-file dir "sub/f.lisp" "(NestedLisp has (color (nested)))\n")
    dir))

(defmacro with-library [binding & body]
  `(let [~binding (sample-library)]
     (try
       ~@body
       (finally
         (delete-tree ~binding)))))

(defn- names-of [walk]
  (mapv :name walk))

(defn- types-of [walk]
  (mapv :type walk))

(deftest the-walk-puts-a-subtree-in-front-and-reverses-sorted-siblings
  (with-library dir
    (let [plain (kb/traverse-directory dir)
          slashed (kb/traverse-directory (str (slash dir) "/"))]
      (is (= ["f" "c" "empty" "e" "d" "b" "a" "Skip" "M"]
             (names-of plain)))
      (is (= ["lisp" "km" nil "kml" "lisp" "km" "km" "KM" "km"]
             (types-of plain)))
      (is (= (names-of plain) (names-of slashed)))
      (is (= [] (kb/traverse-directory (io/file dir "missing")))))))

(defn- earlier?
  "True when left occurs before right in text."
  [text left right]
  (let [at-left (str/index-of text left)
        at-right (str/index-of text right)]
    (and (some? at-left) (some? at-right) (< at-left at-right))))

(deftest load-lib-loads-km-files-and-leaves-lisp-unevaluated
  (with-library dir
    (let [session (engine/session)
          loaded (kb/load-lib (:kb session) (:query session) dir)
          text (:text loaded)]
      (is (= (term/km-list "M" "a" "b" "c") (:value loaded)))
      (is (frame/known-frame? (:kb loaded) (symbol "Gold")))
      (is (frame/known-frame? (:kb loaded) (symbol "Blue")))
      (is (frame/known-frame? (:kb loaded) (symbol "Red")))
      (is (frame/known-frame? (:kb loaded) (symbol "Jade")))
      (is (earlier? text "c.km loaded!" "b.km loaded!"))
      (is (earlier? text "b.km loaded!" "a.km loaded!"))
      (is (earlier? text "a.km loaded!" "M.km loaded!"))
      (is (= 2 (count (:lisp loaded))))
      (is (str/ends-with? (first (:lisp loaded)) "sub/f.lisp"))
      (is (str/ends-with? (second (:lisp loaded)) "d.lisp"))
      (is (not (str/includes? text "f.lisp loaded!")))
      (is (not (str/includes? text "d.lisp loaded!")))
      (is (not (frame/known-frame? (:kb loaded) (symbol "LispMarker"))))
      (is (not (frame/known-frame? (:kb loaded) (symbol "NestedLisp"))))
      (is (not (frame/known-frame? (:kb loaded) (symbol "KmlMarker"))))
      (is (not (frame/known-frame? (:kb loaded) (symbol "SkipMarker")))))))

(deftest a-loaded-file-prints-the-loading-line
  (with-library dir
    (let [one (io/file dir "only")
          _ (.mkdirs one)
          _ (write-file one "Only.km" "(Fred has (color (red)))\n")
          session (engine/session)
          loaded (kb/load-lib (:kb session) (:query session) one)
          color (:value (frame/get-vals (:kb loaded) (symbol "Fred")
                                        (symbol "color")))]
      (is (= (term/km-list "Only") (:value loaded)))
      (is (= (term/km-list (symbol "red")) color))
      (is (str/includes? (:text loaded) "Loading "))
      (is (str/includes? (:text loaded) "Only.km loaded!\n"))
      (is (= [] (:lisp loaded))))))

(deftest a-missing-directory-records-an-error
  (with-library dir
    (let [session (engine/session)
          file (io/file dir "a.km")
          missing (kb/load-lib (:kb session) (:query session)
                               (io/file dir "no-such-components"))
          not-dir (kb/load-lib (:kb session) (:query session) file)]
      (is (nil? (:value missing)))
      (is (= [] (:lisp missing)))
      (is (some #(str/includes? % "No such directory") (:errors missing)))
      (is (nil? (:value not-dir)))
      (is (some #(str/includes? % "No such directory") (:errors not-dir)))
      (is (not (frame/known-frame? (:kb missing) (symbol "Marker")))))))

(deftest load-lib-at-the-prompt-keeps-the-loaded-knowledge-base
  (with-library dir
    (let [session (engine/session)
          loaded (engine/evaluate
                  (str "(load-lib \"" (slash dir) "\" :silent t)")
                  session)
          color (engine/evaluate "(the color of Jade)"
                                 {:kb (:kb loaded) :query (:query loaded)})]
      (is (:ok loaded))
      (is (= (term/km-list "M" "a" "b" "c") (:value loaded)))
      (is (frame/known-frame? (:kb loaded) (symbol "Jade")))
      (is (frame/known-frame? (:kb loaded) (symbol "Gold")))
      (is (not (frame/known-frame? (:kb loaded) (symbol "LispMarker"))))
      (is (not (frame/known-frame? (:kb loaded) (symbol "SkipMarker"))))
      (is (not (str/includes? (str (:text loaded)) "Loading")))
      (is (empty? (:errors loaded)))
      (is (str/includes? (:statistics loaded) "inferences"))
      (is (= (term/km-list (symbol "green")) (:value color))))))

(deftest load-lib-accepts-silentp-and-a-quoted-path
  (with-library dir
    (let [session (engine/session)
          loaded (engine/evaluate
                  (str "(load-lib '\"" (slash dir) "\" :silentp t)")
                  session)]
      (is (:ok loaded))
      (is (= (term/km-list "M" "a" "b" "c") (:value loaded)))
      (is (frame/known-frame? (:kb loaded) (symbol "Blue")))
      (is (not (str/includes? (str (:text loaded)) "Loading")))
      (is (empty? (:errors loaded))))))

(deftest silent-false-prints-each-file-as-it-loads
  (with-library dir
    (let [box (atom nil)
          printed (with-out-str
                    (loadkb/with-echo-text
                      (fn []
                        (reset! box (engine/evaluate
                                     (str "(load-lib \"" (slash dir) "\" :silent f)")
                                     (engine/session)))
                        (let [reply (repl/reply-text @box)]
                          (is (str/includes? reply (print/km-format (:value @box))))
                          (is (not (str/includes? reply "Loading")))
                          (is (not (str/includes? reply "loaded!")))))))
          loaded @box]
      (is (:ok loaded))
      (is (str/includes? (:text loaded) "Loading "))
      (is (str/includes? (:text loaded) "c.km loaded!"))
      (is (earlier? printed "c.km loaded!" "b.km loaded!"))
      (is (earlier? printed "b.km loaded!" "a.km loaded!"))
      (is (earlier? printed "a.km loaded!" "M.km loaded!"))
      (is (earlier? printed (str "Loading " (slash dir)) "c.km loaded!"))
      (is (= "" (with-out-str
                  (loadkb/with-echo-text
                    (fn []
                      (engine/evaluate
                       (str "(load-lib \"" (slash dir) "\" :silent t)")
                       (engine/session))))))))))

(deftest load-lib-at-the-prompt-records-a-missing-directory
  (let [session (engine/session)
        missing (engine/evaluate "(load-lib \"no-such-km-components\")" session)
        bad (engine/evaluate "(load-lib 1)" session)]
    (is (:ok missing))
    (is (nil? (:value missing)))
    (is (some #(str/includes? % "No such directory") (:errors missing)))
    (is (str/includes? (:statistics missing) "inferences"))
    (is (:ok bad))
    (is (nil? (:value bad)))
    (is (some #(str/includes? % "No such directory") (:errors bad)))
    (is (not (frame/known-frame? (:kb bad) (symbol "Jade"))))))

(deftest components-path-is-the-shipped-library
  (let [readme (io/file kb/components-path "Readme.txt")]
    (is (str/ends-with? (slash kb/components-path) "rkf-clib/components/"))
    (is (.isFile readme))
    (is (str/includes? (slurp readme :encoding "UTF-8") "(defun load-lib"))))

(defn- file-type
  "The text after the last dot, or nil when the name has no type."
  [file-name]
  (let [dot (str/last-index-of file-name ".")]
    (when (and dot (pos? dot) (< dot (dec (count file-name))))
      (subs file-name (inc dot)))))

(defn- pathname-name [file-name]
  (let [dot (str/last-index-of file-name ".")]
    (if (or (nil? dot) (<= dot 0) (= dot (dec (count file-name))))
      file-name
      (subs file-name 0 dot))))

(defn- files-of-type
  "Every file under root whose type is exactly type.

  This walk is independent of som.kb. It lists each directory's
  children and descends into every subdirectory."
  [root type]
  (loop [pending [(io/file root)]
         found []]
    (if (empty? pending)
      found
      (let [dir (first pending)
            children (vec (or (.listFiles dir) []))
            matches (filterv #(and (.isFile %)
                                    (= type (file-type (.getName %))))
                              children)
            dirs (filterv #(.isDirectory %) children)]
        (recur (into (vec (rest pending)) dirs)
               (into found matches))))))

(defn- ends-with-path?
  [path suffix]
  (str/ends-with? (slash path) suffix))

(defn- km-elements
  "The elements of a proper Knowledge Machine list."
  [value]
  (loop [value value
         acc []]
    (cond
      (nil? value) acc
      (term/cons? value) (recur (term/cdr value) (conj acc (term/car value)))
      :else (throw (ex-info "Expected a proper list." {:value value})))))

(deftest the-shipped-library-walk-reaches-every-nested-file
  (let [root kb/components-path
        walk (kb/traverse-directory root)
        km-files (files-of-type root "km")
        lisp-files (files-of-type root "lisp")
        kml-files (files-of-type root "kml")
        walked-km (filterv #(= "km" (:type %)) walk)]
    (is (= (set (map #(slash (.getAbsolutePath %)) km-files))
           (set (map :path walked-km))))
    (is (= (set (map #(slash (.getAbsolutePath %)) lisp-files))
           (set (map :path (filter #(= "lisp" (:type %)) walk)))))
    (is (= (count kml-files)
           (count (filter #(= "kml" (:type %)) walk))))
    (is (some #(ends-with-path? (:path %)
                                "science/chem-halo/Concentration-Value.km")
              walked-km))
    (is (some #(str/includes? (slash (:path %)) "science/biology/")
              walked-km))
    (is (some #(ends-with-path? (:path %)
                                "tools/shaken-ui-hidden-slot.km")
              walk))
    (is (some #(ends-with-path? (:path %)
                                "tools/tester/tester.lisp")
              walk))
    (is (some #(ends-with-path? (:path %)
                                "databases/allelements.lisp")
              walk))))

;; Disabled because loading the entire shipped KM library makes routine runs too slow.
;; Remove the reader-discard marker to re-enable this integration test.
#_
(deftest load-lib-loads-the-shipped-component-library
  (let [root kb/components-path
        km-files (files-of-type root "km")
        lisp-files (files-of-type root "lisp")
        session (engine/session)
        loaded (kb/load-lib (:kb session) (:query session) root :silent true)
        names (km-elements (:value loaded))]
    (is (= (frequencies (map #(pathname-name (.getName %)) km-files))
           (frequencies names)))
    (is (= (set (map #(slash (.getAbsolutePath %)) lisp-files))
           (set (:lisp loaded))))
    (is (frame/known-frame? (:kb loaded) (symbol "Concentration-Value")))
    (is (frame/known-frame? (:kb loaded) (symbol "Chloroplast")))
    (is (frame/known-frame? (:kb loaded) (symbol "Engine")))
    (is (frame/known-frame? (:kb loaded) (symbol "shaken-ui-hidden-slot")))
    (is (frame/known-frame? (:kb loaded) (symbol "results_in_transportation_of")))
    (is (not (some #(str/ends-with? % ".kml") (:lisp loaded))))
    (is (every? #(str/starts-with? % "Loading of ")
                (remove str/blank? (str/split-lines (str (:text loaded))))))))
