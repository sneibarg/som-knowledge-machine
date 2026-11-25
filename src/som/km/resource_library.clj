(ns som.km.resource-library
  "Directory listings for component libraries packaged on the classpath."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]))

(defn- directory-index []
  (when-let [url (io/resource "META-INF/som-knowledge-machine/resources.edn")]
    (reduce
     (fn [directories path]
       (let [directory? (str/ends-with? path "/")
             path (str/replace path #"/$" "")
             slash (str/last-index-of path "/")
             parent (subs path 0 slash)
             name (subs path (inc slash))]
         (cond-> (update directories parent (fnil conj []) name)
           directory? (update path #(or % [])))))
     {}
     (edn/read-string (slurp url :encoding "UTF-8")))))

(defn directory
  "Return a classpath directory listing for path, or nil when it is absent.

  Accept classpath:resources/... and checkout paths under src/resources.
  Each result contains :path and :directories for recursive traversal."
  [path]
  (let [path (str/replace (str path) "\\" "/")
        path (cond
               (str/starts-with? path "classpath:") (subs path 10)
               (str/starts-with? path "src/resources/") (subs path 4)
               :else path)
        path (str/replace path #"/+$" "")]
    (when (str/starts-with? path "resources/")
      (let [directories (directory-index)]
        (when (contains? directories path)
          {:path path :directories directories})))))

(defn source
  "Return the URL for a classpath: path, or the original filesystem path."
  [path]
  (if (str/starts-with? (str path) "classpath:")
    (or (io/resource (subs path 10))
        (throw (ex-info "Packaged component resource is missing." {:path path})))
    path))
