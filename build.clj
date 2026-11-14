(ns build
  (:require [clojure.string :as str]
            [clojure.tools.build.api :as b]))

(def ^:private lib 'org.springy.som/som-knowledge-machine)
(def ^:private class-dir "target/classes")

(defn- artifact-version []
  (let [version (str/replace (slurp (b/resolve-path "VERSION") :encoding "UTF-8") #"\r?\n\z" "")]
    (when-not (re-matches #"[a-zA-Z0-9._-]+" version)
      (throw (ex-info "VERSION must contain a single Maven version." {})))
    version))

(defn jar
  "Build the thin Maven library and return the inputs needed to install it."
  [_]
  (let [version (artifact-version)
        jar-file (format "target/%s-%s.jar" (name lib) version)
        basis (b/create-basis {:project "deps.edn" :user nil})
        artifact {:lib lib :version version :basis basis
                  :class-dir class-dir :jar-file jar-file}]
    (b/delete {:path class-dir})
    (b/copy-dir {:src-dirs ["src/som/km"]
                 :target-dir (str class-dir "/som/km")
                 :include "{*.clj,**/*.clj}"})
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
