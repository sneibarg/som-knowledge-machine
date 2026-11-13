(ns som.km.license
  "The text (license) prints.

  The text is the repository LICENSE file: the port preamble and the
  Simplified BSD Licence, copyright 1994-2015, with the allenai.org
  address. licence.lisp still says 1994-2011 and vulcan.com. This
  command does not print that older body. The copy is read when this
  namespace loads, from the source tree, so a later call does not depend
  on the working directory."
  (:require [clojure.java.io :as io]))

(defn- slurp-file
  [file]
  (when (and (some? file) (.isFile file))
    (slurp file :encoding "UTF-8")))

(defn- parent-file
  [file]
  (when (some? file) (.getParentFile file)))

(defn- source-license
  "LICENSE beside the project that contains this source file.

  A source path shorter than four parents yields nothing here. The
  working-directory copy is the next place the text is read."
  []
  (when (some? *file*)
    (slurp-file
     (io/file (-> (io/file *file*)
                  parent-file
                  parent-file
                  parent-file
                  parent-file)
              "LICENSE"))))

(def fallback-text
  "The licence text captured as this namespace loaded.

  It is the LICENSE file beside the source tree when that file can be
  read. The short contact lines are only the last resort."
  (or (source-license)
      (slurp-file (io/file "LICENSE"))
      (str "Copyright (c) 1994-2015 Peter Clark and Bruce Porter.\n"
           "Peter Clark (peterc@allenai.org)\n"
           "Bruce Porter (porter@cs.utexas.edu)\n")))

(defn text
  "The Simplified BSD text, including the port preamble and the closing newline."
  []
  fallback-text)
