(ns som.km.repl
  "The KM> prompt.

  Reads a line through the engine and evaluates it. The prompt holds
  one knowledge base and one query for the person at the keyboard.
  q leaves, matching the Knowledge Machine read-eval-print loop. The
  prompt recognizes q by reading the line, before evaluation, and it
  prints no reply for that line. The HTTP service returns the value
  and keeps running.

  A line that is only the start of an expression is not answered yet.
  The prompt keeps reading lines until the expression is complete."
  (:require [som.km.engine :as engine]
            [som.km.print :as print]
            [som.km.read :as read])
  (:gen-class))

(def prompt "KM> ")

(defn session
  "The knowledge base and query for one prompt."
  []
  (atom (engine/session)))

(defn leave-command?
  "True when the line reads as the symbol q.

  A comment after q is ignored, because the reader discards it before
  the symbol is seen. Q is a different symbol. (q) is a list. The test
  uses the term that was read. Evaluating q returns the list (q), which
  is not this command."
  [line]
  (let [result (read/read-term line)]
    (and (:ok result) (= (symbol "q") (:value result)))))

(defn continue?
  "True when text is the start of an expression and needs another line."
  [text]
  (boolean (:incomplete (engine/evaluate text))))

(defn reply-text
  "Text to print for one engine result.

  A successful result prints :text, when the command produced some, and
  then the answer in km-format. Nil prints as nil. Errors add the
  warning on that same line. A refusal with no :text prints :message."
  [result]
  (if (or (:ok result) (some? (:text result)))
    (str (:text result)
         (print/km-format (:value result))
         (when (seq (:errors result))
           "   ; (WARNING: Errors occurred during reasoning)"))
    (:message result)))

(defn- evaluate-in
  "Evaluate one line in a session. No session starts from the vocabulary
  and discards the result."
  [line session]
  (if session
    (locking session
      (let [current @session
            result (engine/evaluate line {:kb (:kb current) :query (:query current)})]
        (when (:kb result)
          (swap! session assoc :kb (:kb result) :query (:query result)))
        result))
    (engine/evaluate line)))

(defn respond
  "Turn one prompt line into a reply. :leave is true when the session ends.

  session is an atom from session. Without it, the line is evaluated on
  a fresh vocabulary and the result is discarded."
  ([line]
   (respond line nil))
  ([line session]
   (if (leave-command? line)
     {:leave true :text ""}
     {:leave false :text (reply-text (evaluate-in line session))})))

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
     "Expressions are evaluated. q leaves the prompt.\n")))

(defn- report
  "Print the reply for one expression, reading more lines when it is unfinished."
  [text session]
  (loop [text text]
    (let [result (evaluate-in text session)]
      (if (:incomplete result)
        (do
          (print "> ")
          (flush)
          (if-let [more (read-line)]
            (recur (str text "\n" more))
            (when (seq (:message result))
              (println (:message result)))))
        (let [shown (reply-text result)]
          (when (seq shown)
            (println shown)))))))

(defn -main
  "Run the prompt until q or end of input."
  [& _]
  (print (banner))
  (flush)
  (let [session (session)]
    (loop []
      (print prompt)
      (flush)
      (when-let [line (read-line)]
        (if (leave-command? line)
          nil
          (do
            (report line session)
            (recur)))))))
