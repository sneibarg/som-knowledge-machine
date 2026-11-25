(ns som.km.configured
  "Start the KM> prompt from the shipped configuration file.

  The file is src/resources/config.edn. Its :component-libraries
  section names directories. Each directory is one (load-lib) through
  som.km.startup/load-expression, and load-lib walks that directory
  recursively. clojure -M:configured runs this main."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [som.km.repl :as repl]
            [som.km.startup :as startup])
  (:gen-class))

(defn- slash
  [path]
  (str/replace (str path) "\\" "/"))

(defn- shipped-config
  "The configuration file beside this source file, when it is visible.

  *file* is src/som/km/configured.clj while the namespace loads, and
  three parents reach src/. A file URL on the classpath is the next
  place. A jar URL is returned as that URL."
  []
  (or (when (some? *file*)
        (let [file (io/file (-> (io/file *file*)
                                .getParentFile
                                .getParentFile
                                .getParentFile)
                           "resources"
                           "config.edn")]
          (when (.isFile file) file)))
      (io/resource "resources/config.edn")))

(def config-source
  "The configuration this startup reads.

  A file when the source tree is visible, otherwise a classpath
  resource. Nil when neither is visible. Captured when this namespace
  loads."
  (shipped-config))

(def config-path
  "The path or URL of config-source.

  src/resources/config.edn when the file is not visible."
  (cond
    (instance? java.io.File config-source) (slash (.getAbsolutePath config-source))
    (some? config-source) (str config-source)
    :else "src/resources/config.edn"))

(defn- problem
  [message]
  (throw (ex-info message {:type :config})))

(defn read-config
  "The configuration in text.

  Returns the map, with :component-libraries as a vector of directory
  paths. A value that is not a map, a missing section, or an entry that
  is not a directory path throws with a message that names the problem."
  [text]
  (let [value (try
                (edn/read-string text)
                (catch Exception _
                  (problem "The configuration is not readable EDN.")))]
    (when-not (map? value)
      (problem "The configuration must be a map."))
    (when-not (contains? value :component-libraries)
      (problem "The configuration needs a :component-libraries section."))
    (let [libraries (:component-libraries value)]
      ;; A string is sequential, and its characters are not directories.
      (when-not (and (sequential? libraries) (not (string? libraries)))
        (problem ":component-libraries must be a sequence of directory paths."))
      (when-not (every? string? libraries)
        (problem "Each component library must be a directory path."))
      (assoc value :component-libraries (vec libraries)))))

(defn read-config-file
  "The configuration at path.

  path is a file of EDN. A missing file throws with a message that
  names the path."
  [path]
  (let [file (io/file path)]
    (when-not (.isFile file)
      (problem (str "No configuration file " path)))
    (read-config (slurp file :encoding "UTF-8"))))

(defn read-shipped-config
  "The configuration at config-path.

  A missing file throws with a message that names that path."
  []
  (if (nil? config-source)
    (problem (str "No configuration file " config-path))
    (read-config (slurp config-source :encoding "UTF-8"))))

(defn- library-expression
  "A (load-lib) form for one directory, with forward slashes."
  [path]
  (str "(load-lib " (pr-str (str/replace path "\\" "/")) " :silent t)"))

(defn libraries
  "The component libraries in config, in the file's order.

  config is a map from read-config. Each returned map has :label and
  :expression. :expression is (load-lib \"path\" :silent t)."
  [config]
  (mapv (fn [path]
          {:label (str "component library " (str/replace path "\\" "/"))
           :expression (library-expression path)})
        (:component-libraries config)))

(defn -main
  "Load src/resources/config.edn, load its component libraries, and run the prompt.

  A missing file, or a file that is not the configuration map, stops
  before the prompt."
  [& _]
  (try
    (let [config (read-shipped-config)
          session (repl/session)]
      (print (repl/banner))
      (flush)
      (startup/load-libraries session (libraries config))
      (repl/run session))
    (catch clojure.lang.ExceptionInfo e
      (println (.getMessage e))
      (flush)
      (System/exit 1))))
