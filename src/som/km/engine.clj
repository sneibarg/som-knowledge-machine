(ns som.km.engine
  "The Knowledge Machine as a library.

  The prompt and the HTTP service both call evaluate. Each adapter
  holds the knowledge base and the query for its own caller and passes
  them back in. evaluate reads one expression and dispatches it.
  :value is the answer list. A form that is not ported yet is refused.
  reset rebuilds the built-in vocabulary in a value the caller passes
  in. It does not dispatch (reset-kb)."
  (:require [clojure.string :as str]
            [som.km.frame :as frame]
            [som.km.interpreter :as interpreter]
            [som.km.read :as read]))

(def km-version
  "Knowledge Machine release this port is following."
  "2.5.45")

(def ^:private empty-message
  "Type a Knowledge Machine expression.")

(defn status
  "Facts about this build. Both fronts report these same facts."
  []
  {:name "som-knowledge-machine"
   :km-version km-version
   :license "Simplified BSD"
   :copyright "Copyright (c) 1994-2015 Peter Clark and Bruce Porter."
   :evaluator "interpreter"
   :interfaces ["repl" "http"]})

(defn reset
  "Clear a knowledge base and rebuild the built-in vocabulary.

  :value is true. The caller passes the knowledge base in and uses the
  one returned under :kb. The returned query has an empty object stack
  and an empty goal stack. Instances being unified and the inference
  counters stay on the query. evaluate clears those at the start of a
  top-level expression, and then (reset-kb) keeps the cleared values."
  [kb & {:keys [query]}]
  (frame/reset kb :query query))

(defn session
  "A built-in vocabulary and an empty query, the way one front starts.

  Two sessions do not share assertions. The caller holds the value and
  passes :kb and :query back to evaluate."
  []
  (let [started (reset (frame/knowledge-base))]
    {:kb (:kb started) :query (:query started)}))

(defn- present
  "The public result of one interpreted expression.

  :ok is false only for a form that is not ported yet. A syntax error
  stays :ok and records the sentence under :errors. :message, :text, and
  :statistics are present only when the interpreter produced them."
  [trimmed result]
  (cond-> {:ok (not= "not-ported" (:error result))
           :input trimmed
           :value (:value result)
           :kb (:kb result)
           :query (:query result)
           :errors (vec (:errors result))
           :error-structures (vec (:error-structures result))
           :warnings (vec (:warnings result))}
    (= "not-ported" (:error result))
    (assoc :error "not-ported")

    (some? (:message result))
    (assoc :message (:message result))

    (some? (:text result))
    (assoc :text (:text result))

    (some? (:statistics result))
    (assoc :statistics (:statistics result))))

(defn evaluate
  "Read one piece of Knowledge Machine text and evaluate it.

  Returns a map. :value is the answer list. :errors,
  :error-structures, and :warnings carry the notes recorded beside
  that answer. :kb and :query are the values to pass on the next call.
  A form this step does not run has :ok false and :error \"not-ported\".

  :error is \"empty\" when there is nothing to read, and \"read\" when
  the text is not a term. Those two results have no :kb. :incomplete
  is true on a read error when the text is only a prefix of a term.
  :input is the trimmed text when the caller sent some.

  bindings is a map from a #t name to a term. Names match without regard
  to case. The prompt and the HTTP service pass an empty map. kb and
  query default to a fresh session, so a call that omits them does not
  see an earlier call."
  ([text]
   (evaluate text {}))
  ([text {:keys [bindings kb query]}]
   (let [trimmed (str/trim (str (or text "")))]
     (if (str/blank? trimmed)
       {:ok false
        :error "empty"
        :message empty-message}
       (let [read (read/read-term trimmed {:bindings bindings})]
         (cond
           (:ok read)
           (let [kb (or kb (:kb (session)))
                 query (or query frame/empty-query)]
             (present trimmed (interpreter/interpret kb query (:value read))))

           (= "empty" (:error read))
           {:ok false
            :error "empty"
            :input trimmed
            :message empty-message}

           :else
           {:ok false
            :error "read"
            :input trimmed
            :message (:message read)
            :incomplete (boolean (:incomplete read))}))))))
