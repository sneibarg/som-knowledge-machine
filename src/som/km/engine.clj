(ns som.km.engine
  "The Knowledge Machine as a library.

  The prompt and the HTTP service both call this namespace. Neither one
  stores a knowledge base of its own. Step 0 has no knowledge base yet:
  submitting text returns a refusal, and the same refusal, from either front."
  (:require [clojure.string :as str]))

(def km-version
  "Knowledge Machine release this port is following."
  "2.5.45")

(def ^:private empty-message
  "Type a Knowledge Machine expression.")

(def ^:private not-ported-message
  "This step accepts a Knowledge Machine expression and does not evaluate it. Reading expressions is the next step.")

(defn status
  "Facts about this build. Both fronts report these same facts."
  []
  {:name "som-knowledge-machine"
   :km-version km-version
   :license "Simplified BSD"
   :copyright "Copyright (c) 1994-2015 Peter Clark and Bruce Porter."
   :evaluator "not-ported"
   :interfaces ["repl" "http"]})

(defn evaluate
  "Submit one piece of Knowledge Machine text.

  Returns a map. :ok is true only when the engine produced an answer.
  :message is plain English. :input is the trimmed text when the caller
  sent some. :value will hold the answer once evaluation exists."
  [text]
  (let [trimmed (str/trim (str (or text "")))]
    (if (str/blank? trimmed)
      {:ok false
       :error "empty"
       :message empty-message}
      {:ok false
       :error "not-ported"
       :input trimmed
       :message not-ported-message})))
