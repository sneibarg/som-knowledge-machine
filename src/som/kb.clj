(ns som.kb
  "Load the KM component library.

  load-lib and traverse-directory are the Lisp at the end of
  src/resources/km-component-library/rkf-clib/components/Readme.txt.
  A .km file is loaded with load-kb. A .lisp file is recorded and left
  unevaluated: this port has no Common Lisp load. The knowledge base
  is a value the caller passes in. The KM command (load-lib) uses
  this same walk on the session's knowledge base.

  This namespace does not require the interpreter. The interpreter
  requires this namespace, and load-lib resolves km-int when a file
  is loaded."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [som.km.errors :as errors]
            [som.km.loadkb :as loadkb]
            [som.km.print :as print]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(defn- slash
  [path]
  (str/replace (str path) "\\" "/"))

(defn- with-slash
  [^java.io.File dir]
  (let [text (slash (.getAbsolutePath dir))]
    (if (str/ends-with? text "/") text (str text "/"))))

(defn- shipped-components
  "The components directory beside this source file, when it is visible.

  *file* is bound while the namespace loads. A file URL on the
  classpath is the next place. A jar URL has no directory to list."
  []
  (or (when (some? *file*)
        (let [dir (io/file (.getParentFile (.getParentFile (io/file *file*)))
                           "resources"
                           "km-component-library"
                           "rkf-clib"
                           "components")]
          (when (.isDirectory dir) dir)))
      (when-let [url (io/resource
                      "resources/km-component-library/rkf-clib/components/Readme.txt")]
        (when (= "file" (.getProtocol url))
          (.getParentFile (io/as-file url))))))

(def components-path
  "The components directory shipped with this build.

  The Lisp load-lib defaults to ./components/. This is that directory
  in the source tree, with a trailing separator, captured when this
  namespace loads. The Lisp default is kept when the tree is not visible."
  (if-let [dir (shipped-components)]
    (with-slash dir)
    "./components/"))

(defn- som-components
  "The Springs of MUD component directory beside this source file.

  *file* is bound while the namespace loads. A file URL on the
  classpath is the next place. A jar URL has no directory to list."
  []
  (or (when (some? *file*)
        (let [dir (io/file (.getParentFile (.getParentFile (io/file *file*)))
                           "resources"
                           "som-component-library")]
          (when (.isDirectory dir) dir)))
      (when-let [url (io/resource "resources/som-component-library/README.md")]
        (when (= "file" (.getProtocol url))
          (.getParentFile (io/as-file url))))))

(def som-components-path
  "The Springs of MUD component directory shipped with this build.

  This is src/resources/som-component-library, with a trailing
  separator, captured when this namespace loads. The relative path is
  kept when the tree is not visible."
  (if-let [dir (som-components)]
    (with-slash dir)
    "src/resources/som-component-library/"))

(defn- pathname-parts
  "pathname-name and pathname-type.

  The type is the text after the last dot. A name with no dot, or a
  leading dot and no other dot, has no type."
  [file-name]
  (let [dot (str/last-index-of file-name ".")]
    (if (or (nil? dot) (<= dot 0) (= dot (dec (count file-name))))
      {:name file-name :type nil}
      {:name (subs file-name 0 dot)
       :type (subs file-name (inc dot))})))

(defn- listed-directory?
  "True when path is a directory whose listing is non-empty.

  The Lisp test is (directory path). That call returns nil for a
  missing path and for an empty directory, and both are files to the
  walker."
  [^java.io.File path]
  (and (.isDirectory path)
       (when-let [names (.list path)]
         (pos? (count names)))))

(defn- entry
  [^java.io.File file parts]
  {:path (slash (.getAbsolutePath file))
   :name (:name parts)
   :type (:type parts)})

(defn traverse-directory
  "The files load-lib visits, in the order it visits them.

  root is a directory path, with or without a trailing separator. A
  child is a directory when root joined with its pathname-name names a
  non-empty directory, so Thing.km is probed as Thing/. That child's
  contents are placed in front of the entries already collected, and a
  file is placed in front, the way the Lisp append and cons do.
  Children of one directory are sorted with string<, upper case before
  lower case, because Allegro's directory has no one order. An empty
  directory is visited as a file. Each item is {:path :name :type}.
  :type is nil when the name has no type. A missing root is empty."
  [root]
  (let [^java.io.File dir (io/file root)
        names (vec (sort compare (or (seq (.list dir)) [])))
        total (count names)]
    (loop [index 0
           result []]
      (if (= index total)
        result
        (let [name (nth names index)
              parts (pathname-parts name)
              ;; pathname-name only: Thing.km probes the directory Thing/.
              probe (io/file dir (:name parts))]
          (recur (inc index)
                 (if (listed-directory? probe)
                   (into (traverse-directory probe) result)
                   (into [(entry (io/file dir name) parts)] result))))))))

(defn- km-int
  "The interpreter function, resolved when a file is loaded.

  A caller may pass :km-int. Otherwise this is
  som.km.interpreter/km-int, looked up here so the interpreter can
  require this namespace."
  [options]
  (or (:km-int options)
      (requiring-resolve 'som.km.interpreter/km-int)))

(defn- load-component
  [state path options]
  (loadkb/load-file state path (km-int options)
                    :verbose (:verbose options)
                    :with-morphism (:with-morphism options)
                    :eval-instances (:eval-instances options)
                    :load-patterns (:load-patterns options)
                    :print-statistics (:print-statistics options)
                    :silent (:silent options)))

(defn- load-into
  "Load comp-path into state.

  state already holds :kb and :query. The returned map is that state
  with the loaded knowledge base, :value, and :lisp."
  [state comp-path options]
  (let [^java.io.File dir (io/file comp-path)
        options (or options {})]
    (if-not (.isDirectory dir)
      (assoc (errors/report-error state :user-error "No such directory %s!"
                                  (slash (.getAbsolutePath dir)))
             :value nil
             :lisp [])
      (let [components (traverse-directory dir)
            total (count components)]
        (loop [index 0
               state state
               names ()
               lisp []]
          (if (= index total)
            (assoc state
                   :value (term/build-list names nil)
                   :lisp lisp)
            (let [component (nth components index)
                  type (:type component)]
              (cond
                (= "km" type)
                (recur (inc index)
                       (load-component state (:path component) options)
                       (conj names (:name component))
                       lisp)

                (= "lisp" type)
                (recur (inc index)
                       state
                       names
                       (conj lisp (:path component)))

                :else
                (recur (inc index) state names lisp)))))))))

(defn load-lib
  "Load the .km files under comp-path.

  comp-path defaults to components-path. The caller passes the
  knowledge base and the query and uses the returned :kb and :query.
  Each .km file is loaded with load-kb, which resets the inference
  engine at the start of that file. A form that is not ported yet
  follows the query's :on-error. :value is the list of pathname-names
  of the .km files, consed as the Lisp conses them, so the list is the
  reverse of the order traverse-directory visits those files. :lisp
  is the vector of .lisp paths, in visit order. Those files are left
  unevaluated. A .kml file, a fasl, and any other type are skipped.
  The type test is case-sensitive. A missing comp-path records
  \"No such directory %s!\" and :value is nil.

  Keyword arguments are the load-kb options :silent, :verbose,
  :with-morphism, :eval-instances, :load-patterns, and
  :print-statistics. The Lisp call passes none of them. The KM
  command (load-lib) uses this same load on the session's knowledge
  base. On that command, :silent t and :silentp t are the same flag.

  Loading the shipped library reads every .km file under it. Some of
  those files still use forms this port refuses."
  ([kb query]
   (load-lib kb query components-path))
  ([kb query comp-path & {:as options}]
   (load-into {:kb kb
               :query query
               :errors []
               :error-structures []
               :warnings []}
              comp-path
              options)))

(defn- option-name
  "The lower-case name of a keyword or a symbol, or nil."
  [value]
  (cond
    (keyword? value) (str/lower-case (name value))
    (term/km-symbol? value) (str/lower-case (term/symbol-name value))
    :else nil))

(defn- unwrap-arg
  "The value inside (quote value). Any other value stays as it is."
  [value]
  (if (and (utils/quote? value) (term/singleton? (term/cdr value)))
    (term/car (term/cdr value))
    value))

(defn- keyword-map
  "Pairs on a command tail, keyed by the lower-case keyword name.

  A keyword with no following value is stored as nil. A value that is
  not a keyword is skipped."
  [tail]
  (loop [tail tail
         acc {}]
    (cond
      (nil? tail) acc
      (not (term/cons? tail)) acc
      :else
      (let [key (option-name (term/car tail))
            rest (term/cdr tail)]
        (cond
          (and key (term/cons? rest))
          (recur (term/cdr rest) (assoc acc key (term/car rest)))
          key (assoc acc key nil)
          :else (recur rest acc))))))

(defn- load-arguments
  "The directory and the keyword pairs of a (load-lib ...) form.

  A string, quoted or bare, is the directory and it comes first.
  No argument, or a leading keyword, uses components-path."
  [expr]
  (let [tail (term/cdr expr)
        first (when (term/cons? tail) (term/car tail))]
    (if (and (some? first) (nil? (option-name first)))
      {:path (unwrap-arg first)
       :options (keyword-map (term/cdr tail))}
      {:path components-path
       :options (keyword-map tail)})))

(defn- command-options
  "The load-kb flags on a (load-lib ...) form.

  :silent and :silentp set the same flag. :silent is kept when both
  are present."
  [options]
  {:silent (cond
             (contains? options "silent") (get options "silent")
             (contains? options "silentp") (get options "silentp")
             :else nil)
   :verbose (get options "verbose")
   :with-morphism (get options "with-morphism")
   :eval-instances (get options "eval-instances")
   :load-patterns (get options "load-patterns")
   :print-statistics (get options "print-statistics")})

(defn load-command
  "Run a (load-lib) form on the knowledge base in state.

  The directory is the first argument when that argument is a string.
  A quoted string is unwrapped. No directory, or a leading keyword,
  loads components-path. The pairs after the directory are load-kb
  options. :value is the list of .km pathname-names. The returned
  :kb and :query hold the loaded library. A directory argument that
  is not a string records \"No such directory %s!\" and :value is nil."
  [state expr]
  (let [{:keys [path options]} (load-arguments expr)]
    (if (string? path)
      (load-into state path (command-options options))
      (assoc (errors/report-error state :user-error "No such directory %s!"
                                  (print/km-format path))
             :value nil
             :lisp []))))
