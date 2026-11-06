(ns som.km.repl
  "The KM> prompt.

  Reads a line, and either leaves the prompt or submits that line to the
  engine. q leaves, matching the Knowledge Machine read-eval-print loop.
  q is a prompt command. It is not sent to the engine, and the HTTP
  service does not treat it as a shutdown."
  (:require [clojure.string :as str]
            [som.km.engine :as engine])
  (:gen-class))

(def prompt "KM> ")

(defn leave-command?
  "True when the line is the Knowledge Machine leave command, q."
  [line]
  (= "q" (str/trim (str (or line "")))))

(defn reply-text
  "Text to print for one engine result. An answer is printed with
  Clojure's printer until the Knowledge Machine writer is ported."
  [result]
  (if (:ok result)
    (pr-str (:value result))
    (:message result)))

(defn respond
  "Turn one prompt line into a reply. :leave is true when the session ends."
  [line]
  (if (leave-command? line)
    {:leave true :text ""}
    {:leave false :text (reply-text (engine/evaluate line))}))

(defn banner
  "Opening text for an interactive session."
  []
  (let [{:keys [km-version copyright]} (engine/status)]
    (str
     "====================================================\n"
     "KM - THE KNOWLEDGE MACHINE - INFERENCE ENGINE v" km-version "\n"
     "====================================================\n"
     copyright "\n"
     "Simplified BSD Licence. See the LICENSE file.\n"
     "Evaluation is not available yet. q leaves the prompt.\n")))

(defn -main
  "Run the prompt until q or end of input."
  [& _]
  (print (banner))
  (flush)
  (loop []
    (print prompt)
    (flush)
    (when-let [line (read-line)]
      (let [{:keys [leave text]} (respond line)]
        (when (seq text)
          (println text))
        (when-not leave
          (recur))))))
