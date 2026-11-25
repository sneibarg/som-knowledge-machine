(ns build
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.tools.build.api :as b]))

(def ^:private lib 'org.springy.som/som-knowledge-machine)
(def ^:private class-dir "target/classes")

(defn- artifact-version []
  (let [version (str/replace (slurp (b/resolve-path "VERSION") :encoding "UTF-8") #"\r?\n\z" "")]
    (when-not (re-matches #"[a-zA-Z0-9._-]+" version)
      (throw (ex-info "VERSION must contain a single Maven version." {})))
    version))

(defn- write-resource-index []
  (let [root (io/file (b/resolve-path (str class-dir "/resources")))
        paths (->> (file-seq root)
                   rest
                   (map (fn [file]
                          (str "resources/"
                               (str/replace (str (.relativize (.toPath root) (.toPath file)))
                                            "\\" "/")
                               (when (.isDirectory file) "/"))))
                   sort
                   vec)]
    (b/write-file {:path (str class-dir "/META-INF/som-knowledge-machine/resources.edn")
                   :string (pr-str paths)})))

(defn jar
  "Build the thin Maven library and return the inputs needed to install it."
  [_]
  (let [version (artifact-version)
        jar-file (format "target/%s-%s.jar" (name lib) version)
        basis (b/create-basis {:project "deps.edn" :user nil})
        artifact {:lib lib :version version :basis basis
                  :class-dir class-dir :jar-file jar-file}]
    (b/delete {:path class-dir})
    (b/copy-dir {:src-dirs ["src/som"]
                 :target-dir (str class-dir "/som")
                 :include "{*.clj,**/*.clj}"})
    (b/copy-dir {:src-dirs ["src/resources"]
                 :target-dir (str class-dir "/resources")})
    (write-resource-index)
    (b/copy-file {:src "LICENSE"
                  :target (str class-dir "/META-INF/som-knowledge-machine/LICENSE")})
    (b/write-pom (assoc artifact :src-pom :none :src-dirs ["src"]
                        :repos {"central" {:url "https://repo.maven.apache.org/maven2/"}}))
    (b/jar artifact)
    artifact))

(defn install
  "Build the library and install its JAR and POM in the local Maven repository."
  [opts]
  (b/install (jar opts)))
