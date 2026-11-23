(ns som.km.startup
  "Start the KM> prompt with both component libraries loaded.

  The shipped library is loaded first, then the Springs of MUD library.
  Each load is one (load-lib) expression through som.km.engine/evaluate,
  the same function the prompt uses. startup.sh and startup.cmd run
  this main with a larger heap."
  (:require [clojure.string :as str]
            [som.kb :as kb]
            [som.km.engine :as engine]
            [som.km.repl :as repl])
  (:gen-class))

(defn libraries
  "The libraries to load, shipped library first.

  Each map has :label and :expression. :expression is a (load-lib)
  form with :silent t. The Springs of MUD path is som-components-path
  with forward slashes."
  []
  [{:label "the shipped component library"
    :expression "(load-lib :silent t)"}
   {:label "the Springs of MUD component library"
    :expression (str "(load-lib \""
                     (str/replace kb/som-components-path "\\" "/")
                     "\" :silent t)")}])

(defn load-expression
  "Evaluate one Knowledge Machine expression in a prompt session.

  session is an atom from som.km.repl/session. When the engine returns
  a knowledge base, that :kb and :query replace the atom's contents.
  The return value is the engine result."
  [session text]
  (let [current @session
        result (engine/evaluate text {:kb (:kb current) :query (:query current)})]
    (when (:kb result)
      (swap! session assoc :kb (:kb result) :query (:query result)))
    result))

(defn- load-summary
  "One line naming the library and how many errors the load recorded."
  [label result]
  (let [n (count (or (:errors result) []))
        head (str (str/upper-case (subs label 0 1)) (subs label 1))]
    (str head " loaded."
         (when (pos? n)
           (str " " n (if (= 1 n) " error was" " errors were") " recorded.")))))

(defn -main
  "Print the banner, load both component libraries, and run the prompt."
  [& _]
  (print (repl/banner))
  (flush)
  (let [session (repl/session)]
    (doseq [{:keys [label expression]} (libraries)]
      (println (str "Loading " label "..."))
      (flush)
      (println (load-summary label (load-expression session expression)))
      (flush))
    (repl/run session)))
