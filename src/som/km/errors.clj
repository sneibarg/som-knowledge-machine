(ns som.km.errors
  "Recorded errors for one Knowledge Machine query.

  An error is a sentence kept on the result. Nothing is printed, and the
  debugger is not entered. The continuation sentence is not added.
  :on-error of :abort or :abort-silently throws. The exception carries
  the knowledge base at the error. :continue is the default, so a query
  that does not set the mode records the error and goes on. :debug and
  :break are the same as continue: this port has no debugger.
  user-warning and nodebugger-error do not abort."
  (:require [clojure.string :as str]
            [som.km.print :as print]
            [som.km.stack :as stack]
            [som.km.term :as term]))

(def abort-type
  "The ex-info type of a Knowledge Machine abort."
  ::abort)

(defn abort-exception?
  "True when thrown is an abort from report-error."
  [thrown]
  (and (instance? clojure.lang.ExceptionInfo thrown)
       (= abort-type (:type (ex-data thrown)))))

(defn- error-structure
  [state]
  (let [goals (get-in state [:query :goal-stack])]
    (if (term/cons? goals)
      (stack/stacked-expr (term/car goals))
      (:current-expr state))))

(defn- aborting?
  [state kind]
  (and (not (#{:user-warning :nodebugger-error} kind))
       (contains? #{:abort :abort-silently}
                  (get-in state [:query :on-error]))))

(defn report-error
  "Record one error and continue, unless the query says to abort.

  user-warning is a warning. The other kinds are errors. The text is
  kept, and the expression on the goal stack is kept with it. :value
  is left as it is. Nothing is printed. :abort throws with this state."
  [state kind template & args]
  (let [prefix (case kind
                 :user-warning "WARNING! "
                 :program-error "PROGRAM ERROR! "
                 "ERROR! ")
        text (str/trim (str prefix (apply format template args)))
        recorded (if (= kind :user-warning)
                   (update state :warnings (fnil conj []) text)
                   (-> state
                       (update :errors (fnil conj []) text)
                       (update :error-structures (fnil conj []) (error-structure state))))]
    (if (aborting? recorded kind)
      (throw (ex-info text {:type abort-type :state (assoc recorded :value nil)}))
      recorded)))

(defn format-term
  "km-format of one value, for an error sentence."
  [value]
  (print/km-format value))
