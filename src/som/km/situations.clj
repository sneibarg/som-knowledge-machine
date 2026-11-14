(ns som.km.situations
  "Situations, theories, actions, and the supersituation climb.

  in-situation, new-situation, and the do family update the current
  situation on the knowledge base the caller holds. A body restores
  that situation when it returns, including a refusal. An abort leaves
  the temporary situation in force. This is the Lisp prog1, so the
  situation is not restored with try/finally.

  Classification is turned off for the dynamic extent of an action and
  restored on a normal return and on an abort. The KM 1.4 fluent-status
  banner is not printed.

  This namespace does not require the slot reader or the interpreter.
  Both are passed in. Projection asks the previous situation for a slot
  by evaluating (in-situation prev (the slot of instance))."
  (:require [som.km.errors :as errors]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.print :as print]
            [som.km.prototypes :as prototypes]
            [som.km.taxonomy :as taxonomy]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(def ^:private own-properties (symbol "own-properties"))
(def ^:private own-definition (symbol "own-definition"))
(def ^:private appending (symbol "appending"))

(def ^:private inverted-comparison
  {(symbol "<") (symbol ">=")
   (symbol ">") (symbol "<=")
   (symbol ">=") (symbol "<")
   (symbol "<=") (symbol ">")
   (symbol "/=") (symbol "=")})

(defn- refused?
  [state]
  (= "not-ported" (:error state)))

(defn- dotted!
  [tail]
  (throw (ex-info "This list is dotted." {:tail tail})))

(defn- adopt
  "Take the knowledge base and the notes a store call recorded.

  An empty error vector is a real value. It replaces the previous notes.
  :text stays unless the store call recorded some."
  [state stored]
  (cond-> (assoc state
                 :kb (:kb stored)
                 :query (or (:query stored) (:query state)))
    (contains? stored :errors) (assoc :errors (vec (:errors stored)))
    (contains? stored :warnings) (assoc :warnings (vec (:warnings stored)))
    (contains? stored :error-structures)
    (assoc :error-structures (vec (:error-structures stored)))
    (contains? stored :text) (assoc :text (:text stored))
    (contains? stored :error)
    (assoc :error (:error stored) :message (:message stored) :value nil)))

(defn- user-error
  [state template & args]
  (-> (apply errors/report-error state :user-error template args)
      (assoc :value nil)))

(defn- add-text
  [state text]
  (assoc state :text (str (:text state) text)))

(defn- km-length
  [value]
  (loop [value value
         seen 0]
    (cond
      (nil? value) seen
      (term/cons? value) (recur (term/cdr value) (inc seen))
      :else seen)))

(defn answer-one
  "Wrap one situation atom as an answer list.

  Nil becomes the one-element list (NIL). A refusal is unchanged."
  [state]
  (if (refused? state)
    state
    (assoc state :value (term/km-list (:value state)))))

(defn- unique
  "One value of expr. Several values keep the first and record the error.

  :value is that element, not a list. No value stays nil."
  [state expr km-int]
  (let [found (km-int state expr)]
    (cond
      (refused? found) found
      (or (nil? (:value found)) (term/singleton? (:value found)))
      (assoc found :value (when (term/cons? (:value found)) (term/car (:value found))))
      :else
      (-> (errors/report-error found :user-error
                               "Expression %s was expected to return a single value,%nbut it returned multiple values %s!%nJust taking the first...(%s) "
                               (print/km-format expr)
                               (print/km-format (:value found))
                               (print/km-format (term/car (:value found))))
          (assoc :value (term/car (:value found)))))))

(defn- change-to
  "Make situation current.

  A Theory instance is recorded on :theories. The class test reads
  instance-of in *Global, so a theory is recognized before it is entered."
  [state situation]
  (let [theory? (frame/theory-situation? (:kb state) situation)]
    (assoc state :kb (frame/set-situation (:kb state) situation :theory? theory?))))

(defn- entry-form
  [situation-expr body theory?]
  (cond
    (and theory? (some? body)) (term/km-list (symbol "in-theory") situation-expr body)
    (some? body) (term/km-list (symbol "in-situation") situation-expr body)
    theory? (term/km-list (symbol "in-theory") situation-expr)
    :else (term/km-list (symbol "in-situation") situation-expr)))

(defn in-situation
  "Evaluate body in the situation situation-expr names, then restore.

  No body leaves that situation current and answers a one-element list
  of its name. The same situation, including while a prototype is open,
  runs the body without saving and restoring. A refusal from the
  situation expression is returned before situations mode is turned on.
  Any other non-global situation that is not a theory turns the mode on,
  including one that then fails the class check. theory? selects the
  Theory class and skips the mode."
  [state situation-expr body km-int & {:keys [theory?]}]
  (let [unique (unique state situation-expr km-int)]
    (if (refused? unique)
      unique
      (let [structure (:value unique)
            situation (if (and (not theory?) (kb/km-args? structure))
                        (kb/arg1 structure)
                        structure)
            state (if (and (not theory?)
                           (not (utils/eql? situation-expr term/global-situation)))
                    (assoc unique :kb (frame/set-situations-mode (:kb unique)))
                    unique)
            class-name (if theory? (symbol "Theory") (symbol "Situation"))
            current (frame/current-situation (:kb state))
            raw (:situation (:kb state))]
        (cond
          (utils/eql? situation current)
          (let [state (if (utils/eql? raw current) state (change-to state current))]
            (if (some? body)
              (km-int state body)
              (assoc state :value (term/km-list current))))

          (some? (frame/curr-prototype (:kb state)))
          (user-error state
                      "Trying to do %s: Can't enter a %s when you're in prototype mode!"
                      (print/km-format (entry-form situation-expr body theory?))
                      (print/km-format class-name))

          (not (kb/kb-object? situation))
          (user-error state
                      "%s doesn't evaluate to a %s (results in %s instead)!"
                      (print/km-format situation-expr)
                      (print/km-format class-name)
                      (print/km-format structure))

          :else
          (let [classed (taxonomy/isa? (:kb state) situation class-name)
                state (assoc state :kb (:kb classed))]
            (if-not (:value classed)
              (user-error state
                          "%s doesn't evaluate to a %s (%s isn't declared an instance of %s)!"
                          (print/km-format situation-expr)
                          (print/km-format class-name)
                          (print/km-format situation)
                          (print/km-format class-name))
              (if (nil? body)
                (let [entered (change-to state situation)]
                  (assoc entered :value (term/km-list situation)))
                (let [saved (frame/current-situation (:kb state))
                      entered (change-to state situation)
                      result (km-int entered body)]
                  (change-to result saved))))))))))

(defn- situation-pair
  [slot values]
  (term/km-list slot values))

(defn- make-next
  "Create the next situation and link it to the current one.

  The link is asserted here, in the situation that is current now.
  The current situation is not changed. A caller in *Global is an error."
  [state action supplied km-int]
  (if (utils/eql? (frame/current-situation (:kb state)) term/global-situation)
    (user-error state "You must be in a Situation to create a next-situation!")
    (let [current (frame/current-situation (:kb state))
          created (if (some? supplied)
                    (assoc state :value supplied)
                    (prototypes/create-instance
                     state (symbol "Situation")
                     (term/km-list
                      (situation-pair (symbol "supersituations")
                                      (term/km-list term/global-situation)))))]
      (cond
        (refused? created) created
        (nil? (:value created)) created
        :else
        (let [next-name (:value created)
              link (situation-pair (symbol "prev-situation")
                                   (term/km-list (term/km-list :args current action)))
              pairs (if (some? supplied)
                      (term/km-list
                       (situation-pair (symbol "instance-of")
                                       (term/km-list (symbol "Situation")))
                       link)
                      (term/km-list link))
              stored (frame/add-slotsvals (:kb created) next-name pairs
                                          :combine-values-by appending
                                          :query (:query created)
                                          :errors (:errors created)
                                          :warnings (:warnings created)
                                          :error-structures (:error-structures created))]
          (if (refused? stored)
            (adopt created stored)
            (assoc (adopt created stored) :value next-name)))))))

(defn new-situation
  "Create a situation whose supersituation is *Global and enter it.

  The answer is a one-element list of the new name. Situations mode
  turns on because the situation is not *Global."
  [state km-int]
  (let [created (prototypes/create-instance
                 state (symbol "Situation")
                 (term/km-list
                  (situation-pair (symbol "supersituations")
                                  (term/km-list term/global-situation))))]
    (cond
      (refused? created) created
      (nil? (:value created)) created
      :else (in-situation created (:value created) nil km-int))))

(defn immediate-supersituations
  "The situations directly above situation.

  *Global has none. A knowledge-base object is kept. Any other
  expression contributes the first value of evaluating it. Nils are
  dropped. An empty result is (*Global). The Lisp does not guard a
  cycle; the climb that uses this result does."
  [state situation km-int]
  (if (utils/eql? situation term/global-situation)
    (assoc state :value nil)
    (let [found (frame/get-vals (:kb state) situation (symbol "supersituations")
                                :situation term/global-situation
                                :dereference? false
                                :query (:query state))
          state (assoc state :kb (:kb found) :query (or (:query found) (:query state)))]
      (loop [pending (:value found)
             state state
             acc []]
        (cond
          (refused? state) state
          (nil? pending)
          (assoc state :value
                 (if (empty? acc)
                   (term/km-list term/global-situation)
                   (term/build-list acc nil)))
          (not (term/cons? pending)) (dotted! pending)
          :else
          (let [item (term/car pending)]
            (if (kb/kb-object? item)
              (recur (term/cdr pending) state (conj acc item))
              (let [evaluated (km-int state item)]
                (if (refused? evaluated)
                  evaluated
                  (let [first (when (term/cons? (:value evaluated))
                                (term/car (:value evaluated)))]
                    (recur (term/cdr pending)
                           evaluated
                           (if (nil? first) acc (conj acc first)))))))))))))

(defn- supers-below
  "situation and the situations above it, not including *Global."
  [state situation km-int seen]
  (cond
    (or (utils/eql? situation term/global-situation)
        (some #(utils/eql? situation %) seen))
    (assoc state :value nil)
    :else
    (let [immediate (immediate-supersituations state situation km-int)]
      (if (refused? immediate)
        immediate
        (loop [pending (:value immediate)
               state immediate
               acc [situation]]
          (cond
            (refused? state) state
            (nil? pending) (assoc state :value (term/build-list acc nil))
            (not (term/cons? pending)) (dotted! pending)
            :else
            (let [below (supers-below state (term/car pending) km-int (conj seen situation))]
              (if (refused? below)
                below
                (recur (term/cdr pending)
                       below
                       (into acc (utils/elements (:value below))))))))))))

(defn all-supersituations
  "The situations above situation, with *Global first.

  situation itself is not included. *Global's own list is nil."
  [state situation km-int]
  (if (utils/eql? situation term/global-situation)
    (assoc state :value nil)
    (let [immediate (immediate-supersituations state situation km-int)]
      (if (refused? immediate)
        immediate
        (loop [pending (:value immediate)
               state immediate
               acc []]
          (cond
            (refused? state) state
            (nil? pending)
            (assoc state :value
                   (term/cons-cell term/global-situation
                                   (utils/remove-duplicates
                                    (term/build-list acc nil)
                                    :test utils/equal?
                                    :from-end? false)))
            (not (term/cons? pending)) (dotted! pending)
            :else
            (let [below (supers-below state (term/car pending) km-int #{})
                  items (if (refused? below) nil (utils/elements (:value below)))]
              (if (refused? below)
                below
                (recur (term/cdr pending) below (into acc items))))))))))

(defn- rules-in
  [state instance slot situation]
  (let [own (frame/get-vals (:kb state) instance slot
                            :facet own-properties
                            :situation situation
                            :query (:query state))
        state (assoc state :kb (:kb own) :query (or (:query own) (:query state)))]
    (if (some? (:value own))
      {:state state :values (:value own)}
      (let [defined (frame/get-vals (:kb state) instance slot
                                    :facet own-definition
                                    :situation situation
                                    :query (:query state))]
        {:state (assoc state :kb (:kb defined)
                       :query (or (:query defined) (:query state)))
         :values (:value defined)}))))

(defn inherited-situation-rules
  "Own facts from supersituations and from visible theories.

  :value is a list of value lists. :raw is the bound expressions those
  lists came from, so a constraint walk still sees <>. A clone's
  inertial slot contributes nothing once the situation has a previous
  situation. The value re-read of a parent situation stays off. The
  earlier duplicate is kept. A later copy of the same value list is
  dropped. Sources are not removed."
  [state instance slot km-int]
  (let [situation (frame/target-situation (:kb state)
                                          (frame/current-situation (:kb state))
                                          instance slot)
        cloned (frame/get-vals (:kb state) instance (symbol "cloned-from")
                               :situation term/global-situation
                               :dereference? false
                               :query (:query state))
        prev (frame/get-vals (:kb cloned) situation (symbol "prev-situation")
                             :situation term/global-situation
                             :dereference? false
                             :query (:query cloned))
        state (assoc state :kb (:kb prev) :query (or (:query prev) (:query state)))]
    (if (and (some? (:value cloned))
             (not (utils/eql? situation term/global-situation))
             (frame/inertial-fluent? (:kb state) slot)
             (some? (:value prev)))
      (assoc state :raw nil :value nil)
      (let [parents (if (and (not (utils/eql? situation term/global-situation))
                             (frame/fluent? (:kb state) slot))
                      (all-supersituations state situation km-int)
                      (assoc state :value nil))]
        (if (refused? parents)
          parents
          (let [places (utils/append-lists
                        (term/km-list (:value parents)
                                      (frame/visible-theories (:kb parents))))]
            (loop [pending places
                   state parents
                   raws []
                   sets []]
              (cond
                (nil? pending)
                (assoc state
                       :raw (when (seq raws)
                              (utils/append-lists (term/build-list raws nil)))
                       :value (utils/remove-duplicates
                               (utils/remove-items nil (term/build-list sets nil))
                               :test utils/equal?
                               :from-end? true))
                (not (term/cons? pending)) (dotted! pending)
                :else
                (let [found (rules-in state instance slot (term/car pending))
                      values (:values found)]
                  (if (nil? values)
                    (recur (term/cdr pending) (:state found) raws sets)
                    (let [bound (frame/bind-self values instance)]
                      (recur (term/cdr pending)
                             (:state found)
                             (conj raws bound)
                             (conj sets (kb/&&-exprs-to-valsets bound))))))))))))))

(defn previous
  "The previous situation of the current one, or nil.

  The slot is read with no explicit situation. Two or more values keep
  the first. The trace warning is not printed. A value that evaluation
  changed is written back. An :args structure contributes its first
  argument. The cached-values-only variant is not selected."
  [state km-int]
  (let [situation (frame/current-situation (:kb state))
        found (frame/get-vals (:kb state) situation (symbol "prev-situation")
                              :query (:query state))
        state (assoc state :kb (:kb found) :query (or (:query found) (:query state)))
        evaluated (km-int state (kb/vals-to-val (:value found)))]
    (if (refused? evaluated)
      evaluated
      (let [values (:value evaluated)
            changed (not (utils/equal? (:value found) values))
            written (if-not changed
                      evaluated
                      (let [put (frame/put-vals (:kb evaluated) situation
                                                (symbol "prev-situation") values
                                                :query (:query evaluated))
                            target (frame/target-situation
                                    (:kb put)
                                    (frame/current-situation (:kb put))
                                    situation
                                    (symbol "prev-situation"))]
                        (assoc evaluated
                               :kb (frame/note-done (:kb put) situation
                                                    (symbol "prev-situation")
                                                    target)
                               :query (or (:query put) (:query evaluated)))))
            first (when (term/cons? values) (term/car values))]
        (assoc written :value (if (kb/km-args? first) (kb/arg1 first) first))))))

(defn- isa-theory?
  [state theory]
  (let [found (frame/get-vals (:kb state) (symbol "Theory") (symbol "instances")
                              :situation term/global-situation
                              :dereference? false
                              :query (:query state))]
    {:state (assoc state :kb (:kb found) :query (or (:query found) (:query state)))
     :value (boolean (utils/member? theory (:value found)))}))

(defn- accept-theory
  "The state, and whether theory may be shown or hidden.

  A Theory member or a Situation is accepted. Anything else records an
  error and is not accepted."
  [state theory hide?]
  (let [known (isa-theory? state theory)
        classed (taxonomy/isa? (:kb (:state known)) theory (symbol "Situation"))
        state (assoc (:state known) :kb (:kb classed))]
    (cond
      (or (:value known) (:value classed)) {:state state :accepted? true}
      hide?
      {:state (user-error state "(hide-theory %s): %s is not a theory!"
                          (print/km-format theory) (print/km-format theory))
       :accepted? false}
      :else
      {:state (user-error state "(see-theory %s): %s is not a theory!"
                          (print/km-format theory) (print/km-format theory))
       :accepted? false})))

(defn- revise-one
  [state theory hide?]
  (let [checked (accept-theory state theory hide?)]
    (if-not (:accepted? checked)
      (:state checked)
      (let [state (:state checked)
            visible (frame/visible-theories (:kb state))
            present? (boolean (utils/member? theory visible))]
        (cond
          (and hide? (not present?)) state
          (and (not hide?) present?) state
          hide?
          (assoc state :kb
                 (-> (:kb state)
                     frame/reset-done
                     (frame/set-visible-theories (utils/remove-items theory visible))))
          :else
          (assoc state :kb
                 (-> (:kb state)
                     frame/reset-done
                     (frame/set-visible-theories (term/cons-cell theory visible)))))))))

(defn revise-visible-theories
  "Apply see-theory or hide-theory to every value of expr.

  hide? with nothing left visible answers (t). see-theory answers the
  visible list, which is nil when none are visible. A bad name records
  an error and the walk continues."
  [state expr km-int hide?]
  (let [found (km-int state expr)]
    (if (refused? found)
      found
      (loop [pending (:value found)
             state found]
        (cond
          (nil? pending)
          (let [visible (frame/visible-theories (:kb state))]
            (assoc state :value
                   (if (and hide? (nil? visible))
                     (term/km-list (symbol "t"))
                     visible)))
          (not (term/cons? pending)) (dotted! pending)
          :else
          (recur (term/cdr pending) (revise-one state (term/car pending) hide?)))))))

(defn- find-propositions
  [state action slot km-int]
  (let [found (km-int state (term/km-list (symbol "the") slot (symbol "of") action))]
    (if (refused? found)
      found
      (loop [pending (:value found)
             state found
             acc []]
        (cond
          (nil? pending) (assoc state :value (term/build-list acc nil))
          (not (term/cons? pending)) (dotted! pending)
          :else
          (let [item (term/car pending)
                blocking (contains? #{(symbol "ncs-list") (symbol "del-list")} slot)]
            (cond
              (not (kb/km-triple? item))
              (recur (term/cdr pending)
                     (errors/report-error state :user-error
                                          "Non-triple %s found in (the %s of %s)"
                                          (print/km-format item)
                                          (print/km-format slot)
                                          (print/km-format action))
                     acc)
              (and blocking (kb/constraint-expr? (kb/arg3 item)))
              (recur (term/cdr pending)
                     (errors/report-error state :user-error
                                          "%s found in (the %s of %s)%n   You can't include constraints in the triples of a %s!"
                                          (print/km-format item)
                                          (print/km-format slot)
                                          (print/km-format action)
                                          (print/km-format slot))
                     acc)
              :else (recur (term/cdr pending) state (conj acc item)))))))))

(defn- distinct-pairs
  [triples]
  (loop [triples triples
         acc []]
    (cond
      (nil? triples) (term/build-list acc nil)
      (not (term/cons? triples)) (term/build-list acc nil)
      :else
      (let [triple (term/car triples)
            pair (term/km-list (kb/arg1 triple) (kb/arg2 triple))]
        (recur (term/cdr triples)
               (if (some #(utils/equal? pair %) acc) acc (conj acc pair)))))))

(defn- forward-propagate
  [state triples km-int]
  (loop [pending (distinct-pairs triples)
         state state]
    (cond
      (refused? state) state
      (nil? pending) state
      (not (term/cons? pending)) (dotted! pending)
      :else
      (let [pair (term/car pending)
            frame (term/car pair)
            slot (term/car (term/cdr pair))
            next (if (kb/comparison-operator? slot)
                   (km-int state frame)
                   (km-int state (term/km-list (symbol "the") slot (symbol "of") frame)))]
        (if (refused? next)
          next
          (recur (term/cdr pending) next))))))

(defn- proposition-lines
  [values]
  (loop [values values
         text ""]
    (cond
      (nil? values) text
      (not (term/cons? values)) text
      :else (recur (term/cdr values)
                   (str text "  " (print/km-format (term/car values)) "\n")))))

(defn- consistent-one
  [state proposition in-list km-int]
  (if-not (kb/km-triple? proposition)
    (user-error state "%s contains a non-proposition `%s'!%nIgnoring it..."
                (print/km-format in-list) (print/km-format proposition))
    (let [frame (kb/arg1 proposition)
          slot (kb/arg2 proposition)
          value (kb/arg3 proposition)]
      (if (contains? inverted-comparison slot)
        (let [values (kb/val-to-vals value)]
          (cond
            (nil? values)
            (user-error state "Triple %s: missing a value to compare against!"
                        (print/km-format proposition))
            (not (term/singleton? values))
            (user-error state
                        "Triple %s: the last element must be a single value for a comparison operation!"
                        (print/km-format proposition))
            (not (kb/kb-object? frame))
            (user-error state
                        "Triple %s: a comparison against (the ?x of ?y) is not ported yet."
                        (print/km-format proposition))
            :else
            (km-int state (term/km-list (symbol "not")
                                        (term/km-list frame
                                                      (inverted-comparison slot)
                                                      value)))))
        (let [values (kb/val-to-vals value)
              description (term/km-list (symbol "a") (symbol "Thing") (symbol "with")
                                        (term/km-list
                                         (term/km-list slot
                                                       (if (contains? #{(symbol "ncs-list")
                                                                        (symbol "del-list")}
                                                                      in-list)
                                                         (term/km-list (term/km-list (symbol "<>") value))
                                                         values))))]
          (km-int state (term/km-list frame (symbol "&?") description)))))))

(defn- inconsistent
  [state propositions in-list km-int]
  (if (nil? propositions)
    (assoc state :bad nil)
    (loop [pending propositions
           state state
           bad []]
      (cond
        (refused? state) state
        (nil? pending) (assoc state :bad (term/build-list bad nil))
        (not (term/cons? pending)) (dotted! pending)
        :else
        (let [hit (consistent-one state (term/car pending) in-list km-int)]
          (cond
            (refused? hit) hit
            (some? (:value hit)) (recur (term/cdr pending) (assoc hit :value nil) bad)
            :else (recur (term/cdr pending) hit (conj bad (term/car pending)))))))))

(defn- is-true
  "Whether one proposition already holds.

  A ground triple evaluates (frame is '(a Thing with (slot (value)))).
  A slotted description through is is still refused, and that refusal
  is returned to the caller."
  [state proposition km-int]
  (cond
    (not (kb/km-triple? proposition))
    (user-error state
                "(is-true %s): %s should evaluate to a triple! (evaluated to %s instead)!"
                (print/km-format proposition)
                (print/km-format proposition)
                (print/km-format proposition))
    (kb/comparison-operator? (kb/arg2 proposition))
    (km-int state (term/km-list (kb/arg1 proposition)
                                (kb/arg2 proposition)
                                (kb/arg3 proposition)))
    (nil? (kb/arg3 proposition))
    (assoc state :value (term/km-list (symbol "t")))
    :else
    (let [frame (kb/arg1 proposition)
          slot (kb/arg2 proposition)
          value (kb/arg3 proposition)
          description (term/km-list (symbol "quote")
                                    (term/km-list (symbol "a") (symbol "Thing") (symbol "with")
                                                  (term/km-list (term/km-list slot
                                                                              (term/km-list value)))))]
      (km-int state (term/km-list frame (symbol "is") description)))))

(defn- unsatisfied
  [state propositions km-int]
  (if (nil? propositions)
    (assoc state :bad nil)
    (loop [pending propositions
           state state
           bad []]
      (cond
        (refused? state) state
        (nil? pending) (assoc state :bad (term/build-list bad nil))
        (not (term/cons? pending)) (dotted! pending)
        :else
        (let [hit (is-true state (term/car pending) km-int)]
          (cond
            (refused? hit) hit
            (some? (:value hit)) (recur (term/cdr pending) hit bad)
            :else (recur (term/cdr pending) hit (conj bad (term/car pending)))))))))

(defn- record-each
  [state frame slot values action head]
  (loop [pending values
         kb (:kb state)]
    (if (or (nil? pending) (not (term/cons? pending)))
      (assoc state :kb kb)
      (let [recorded (frame/record-explanation-for
                      kb
                      (term/km-list (symbol "the") slot (symbol "of") frame)
                      (term/car pending)
                      (term/km-list head action))]
        (recur (term/cdr pending) (:kb recorded))))))

(defn- assert-has
  [state frame slot values action head km-int]
  (let [asserted (km-int state
                         (term/km-list frame (symbol "has")
                                       (term/km-list slot values))
                         :fail-mode :error)]
    (if (refused? asserted)
      asserted
      (record-each asserted frame slot values action head))))

(defn- assert-excluded
  "Store (<> value) by appending, and the inverse <> when the slot records one.

  delete-val and also-hasnt uninstall a link and do not write <>.
  This is the del-list path. The inverse is an also-has, so paths are
  evaluated and the value is classified."
  [state frame slot value km-int]
  (let [stored (frame/add-slotsvals
                (:kb state) frame
                (term/km-list (term/km-list slot
                                            (term/km-list (term/km-list (symbol "<>") value))))
                :combine-values-by appending
                :query (:query state)
                :errors (:errors state)
                :warnings (:warnings state)
                :error-structures (:error-structures state))]
    (if (refused? stored)
      (adopt state stored)
      (let [state (adopt state stored)]
        (if-not (frame/records-inverse? (:kb state) slot value)
          state
          (km-int state
                  (term/km-list value
                                (symbol "also-has")
                                (term/km-list
                                 (frame/invert-slot (:kb state) slot)
                                 (term/km-list
                                  (term/km-list (symbol "<>") frame))))
                  :fail-mode :error))))))

(defn- assert-proposition
  [state proposition action in-list km-int]
  (if-not (kb/km-triple? proposition)
    (user-error state "%s contains a non-proposition `%s'!%nIgnoring it..."
                (print/km-format in-list) (print/km-format proposition))
    (let [frame (kb/arg1 proposition)
          slot (kb/arg2 proposition)
          value (kb/arg3 proposition)]
      (if (contains? #{(symbol "ncs-list") (symbol "del-list")} in-list)
        (if (contains? inverted-comparison slot)
          state
          (let [evaluated (km-int state value)]
            (if (refused? evaluated)
              evaluated
              (loop [pending (:value evaluated)
                     state evaluated]
                (cond
                  (refused? state) state
                  (nil? pending) state
                  (not (term/cons? pending)) (dotted! pending)
                  :else
                  (recur (term/cdr pending)
                         (assert-excluded state frame slot (term/car pending) km-int)))))))
        (if (contains? inverted-comparison slot)
          state
          (let [evaluated (km-int state value)]
            (if (refused? evaluated)
              evaluated
              (assert-has evaluated frame slot (:value evaluated) action
                          (if (utils/eql? in-list (symbol "pcs-list"))
                            (symbol "precondition-for")
                            (symbol "result-of"))
                          km-int))))))))

(defn- assert-each
  [state propositions action in-list km-int]
  (loop [pending propositions
         state state]
    (cond
      (refused? state) state
      (nil? pending) state
      (not (term/cons? pending)) (dotted! pending)
      :else
      (recur (term/cdr pending)
             (assert-proposition state (term/car pending) action in-list km-int)))))

(defn- evaluate-triple
  [state triple km-int]
  (if-not (and (kb/path? (kb/arg3 triple))
               (not (kb/comparison-operator? (kb/arg2 triple)))
               (term/cons? (kb/arg3 triple)))
    {:state state :triple triple}
    (let [frame (unique state (kb/arg1 triple) km-int)]
      (if (refused? frame)
        {:state frame :triple nil}
        (let [slot (unique frame (kb/arg2 triple) km-int)]
          (if (refused? slot)
            {:state slot :triple nil}
            (let [value (km-int slot (kb/arg3 triple) :fail-mode :error)]
              {:state value
               :triple (term/km-list :triple
                                     (:value frame)
                                     (:value slot)
                                     (kb/vals-to-val (:value value)))})))))))

(defn- evaluate-triples
  [state triples km-int]
  (loop [pending triples
         state state
         acc []]
    (cond
      (refused? state) state
      (nil? pending) (assoc state :value (term/build-list acc nil))
      (not (term/cons? pending)) (dotted! pending)
      :else
      (let [done (evaluate-triple state (term/car pending) km-int)]
        (if (refused? (:state done))
          (:state done)
          (recur (term/cdr pending) (:state done) (conj acc (:triple done))))))))

(defn- block-list
  [state adds km-int]
  (loop [pending adds
         state state
         acc []]
    (cond
      (refused? state) state
      (nil? pending) (assoc state :value (kb/remove-dup-instances (term/build-list acc nil)))
      (not (term/cons? pending)) (dotted! pending)
      :else
      (let [proposition (term/car pending)
            frame (kb/arg1 proposition)
            slot (kb/arg2 proposition)
            value (kb/arg3 proposition)]
        (if-not (and (frame/single-valued-slot? (:kb state) slot)
                     (not (kb/constraint-expr? value)))
          (recur (term/cdr pending) state acc)
          (if (kb/km-set? value)
            (recur (term/cdr pending)
                   (user-error state
                               "do-action trying to assert multiple values for single-valued slot!%nTrying to assert %s for (the %s of %s)!"
                               (print/km-format (kb/val-to-vals value))
                               (print/km-format slot)
                               (print/km-format frame))
                   acc)
            (let [old (km-int state (term/km-list (symbol "the") slot (symbol "of") frame))]
              (if (refused? old)
                old
                (let [blocked (utils/remove-items value (:value old))
                      triples (loop [items blocked
                                     found []]
                                (cond
                                  (nil? items) found
                                  (not (term/cons? items)) found
                                  (kb/kb-object? (term/car items))
                                  (recur (term/cdr items)
                                         (conj found
                                               (term/km-list :triple
                                                             (term/car items)
                                                             (frame/invert-slot (:kb old) slot)
                                                             (term/km-list (symbol "<>") frame))))
                                  :else (recur (term/cdr items) found)))]
                  (recur (term/cdr pending) old (into acc triples)))))))))))

(defn- enter-and-assert
  [state next-name old change? dels blocks adds action km-int]
  (let [entered (in-situation state next-name nil km-int)]
    (if (refused? entered)
      entered
      (let [asserted (-> entered
                         (assert-each dels action (symbol "del-list") km-int)
                         (assert-each blocks action (symbol "add-list") km-int)
                         (assert-each adds action (symbol "add-list") km-int))
            here (frame/current-situation (:kb asserted))]
        (cond
          (and (refused? asserted) change?) asserted
          change? (assoc asserted :value here)
          :else
          (let [back (in-situation asserted old nil km-int)]
            (if (refused? asserted)
              (assoc back :error (:error asserted)
                     :message (:message asserted)
                     :value nil)
              (assoc back :value here))))))))

(defn- null-transition
  [state supplied change? km-int]
  (let [old (frame/current-situation (:kb state))
        nxt (make-next state nil supplied km-int)]
    (cond
      (refused? nxt) nxt
      (nil? (:value nxt)) nxt
      :else (enter-and-assert nxt (:value nxt) old change? nil nil nil nil km-int))))

(defn- action-transition
  [state action supplied change? test? km-int]
  (let [old (frame/current-situation (:kb state))
        pcs (find-propositions state action (symbol "pcs-list") km-int)]
    (if (refused? pcs)
      pcs
      (let [ncs (find-propositions pcs action (symbol "ncs-list") km-int)]
        (if (refused? ncs)
          ncs
          (let [spread (if (or (some? (:value pcs)) (some? (:value ncs)))
                         (forward-propagate ncs
                                            (utils/append-lists
                                             (term/km-list (:value pcs) (:value ncs)))
                                            km-int)
                         ncs)]
            (if (refused? spread)
              spread
              (let [bad-pcs (inconsistent spread (:value pcs) (symbol "pcs-list") km-int)]
                (if (refused? bad-pcs)
                  bad-pcs
                  (let [bad-ncs (inconsistent (dissoc bad-pcs :bad)
                                              (:value ncs) (symbol "ncs-list") km-int)]
                    (if (refused? bad-ncs)
                      bad-ncs
                      (cond
                        (or (some? (:bad bad-pcs)) (some? (:bad bad-ncs)))
                        (let [named (dissoc bad-ncs :bad)
                              named (if (some? (:bad bad-pcs))
                                      (add-text named
                                                (str "(do " (print/km-format action)
                                                     "): Can't do this action as it would be inconsistent to assert precondition(s):\n"
                                                     (proposition-lines (:bad bad-pcs))))
                                      named)]
                          (assoc (if (some? (:bad bad-ncs))
                                   (add-text named
                                             (str "(do " (print/km-format action)
                                                  "): Can't do this action as it would be inconsistent to assert negated precondition(s):\n"
                                                  (proposition-lines (:bad bad-ncs))))
                                   named)
                                 :value nil))
                        :else
                        (let [open (unsatisfied (dissoc bad-ncs :bad) (:value pcs) km-int)]
                          (if (refused? open)
                            open
                            (let [missed (:bad open)
                                  state (dissoc open :bad)]
                              (if (and test? (some? missed))
                                (assoc (add-text state
                                                 (str "(" (if change? "try-do-and-next" "try-do")
                                                      " " (print/km-format action)
                                                      "):\nCan't do this action because these precondition(s) aren't satisfied:\n"
                                                      (proposition-lines missed)))
                                       :value nil)
                                (let [assumed (assert-each state (:value ncs) action
                                                           (symbol "ncs-list") km-int)
                                      assumed (assert-each assumed missed action
                                                           (symbol "pcs-list") km-int)]
                                  (if (refused? assumed)
                                    assumed
                                    (let [cleared (if (or (some? (:value ncs)) (some? missed))
                                                    (assoc assumed :kb (frame/un-done (:kb assumed) action))
                                                    assumed)
                                          adds (find-propositions cleared action
                                                                  (symbol "add-list") km-int)]
                                      (if (refused? adds)
                                        adds
                                        (let [dels (find-propositions adds action
                                                                      (symbol "del-list") km-int)]
                                          (if (refused? dels)
                                            dels
                                            (let [evaluated-adds (evaluate-triples dels (:value adds) km-int)]
                                              (if (refused? evaluated-adds)
                                                evaluated-adds
                                                (let [evaluated-dels (evaluate-triples
                                                                      evaluated-adds (:value dels) km-int)]
                                                  (if (refused? evaluated-dels)
                                                    evaluated-dels
                                                    (let [blocks (block-list evaluated-dels
                                                                             (:value evaluated-adds)
                                                                             km-int)]
                                                      (if (refused? blocks)
                                                        blocks
                                                        (let [nxt (make-next blocks action supplied km-int)]
                                                          (if (or (refused? nxt) (nil? (:value nxt)))
                                                            nxt
                                                            (enter-and-assert nxt (:value nxt) old change?
                                                                              (:value evaluated-dels)
                                                                              (:value blocks)
                                                                              (:value evaluated-adds)
                                                                              action km-int)))))))))))))))))))))))))))))))

(defn- do-action-body
  [state action-expr km-int next-situation change? test?]
  (if (utils/eql? (frame/current-situation (:kb state)) term/global-situation)
    (assoc state :value nil)
    (let [resolved (if (nil? action-expr)
                     (assoc state :value nil)
                     (unique state action-expr km-int))]
      (cond
        (refused? resolved) resolved
        (nil? (:value resolved))
        (null-transition resolved next-situation change? km-int)
        :else
        (action-transition resolved (:value resolved) next-situation change? test? km-int)))))

(defn- with-classification-off
  "Turn classification off for f, then put the flag back.

  An abort is rethrown with the flag restored on the knowledge base at
  the error. The situation is left as f left it."
  [state f]
  (let [saved (get-in state [:kb :runtime :classification-enabled?])
        state (assoc-in state [:kb :runtime :classification-enabled?] false)]
    (try
      (assoc-in (f state) [:kb :runtime :classification-enabled?] saved)
      (catch clojure.lang.ExceptionInfo thrown
        (if (errors/abort-exception? thrown)
          (let [data (ex-data thrown)
                aborted (:state data)]
            (throw (ex-info (.getMessage thrown)
                            (assoc data :state
                                   (assoc-in aborted
                                             [:kb :runtime :classification-enabled?]
                                             saved))
                            thrown)))
          (throw thrown))))))

(defn do-action
  "Carry out one action and answer the situation it was carried out in.

  :value is that situation, or nil when the action is ignored or cannot
  be done. The caller wraps a success in a one-element list. test? is
  try-do: an unsatisfied precondition is reported and not assumed.
  change-to-next? leaves the new situation current. The Event subclass
  check and the second-time check are not active."
  [state action-expr km-int & {:keys [next change-to-next? test?]}]
  (with-classification-off
    state
    (fn [state]
      (do-action-body state action-expr km-int next change-to-next? test?))))

(defn next-command
  "Create and enter the next situation.

  A global situation or a theory records an error and answers nil."
  [state km-int]
  (if (frame/local-situation? (:kb state))
    (do-action state nil km-int :change-to-next? true)
    (user-error state "Can only do (next-situation) from within a situation!")))

(defn do-form
  "Run do, do-and-next, try-do, or try-do-and-next.

  A supplied next situation must be a Situation. The error text names
  do even when the command is another member of the family, and that
  error answers nil rather than a one-element list."
  [state action next km-int & {:keys [change-to-next? test?]}]
  (if (nil? next)
    (answer-one (do-action state action km-int
                           :change-to-next? change-to-next?
                           :test? test?))
    (let [classed (taxonomy/isa? (:kb state) next (symbol "Situation"))
          state (assoc state :kb (:kb classed))]
      (if (:value classed)
        (answer-one (do-action state action km-int
                               :next next
                               :change-to-next? change-to-next?
                               :test? test?))
        (user-error state
                    "(do %s %s): %s should be an instance of Situation, but isn't!"
                    (print/km-format action)
                    (print/km-format next)
                    (print/km-format next))))))

(defn- run-each
  [state actions next-name km-int]
  (loop [pending actions
         state state]
    (cond
      (refused? state) state
      (nil? pending) state
      (not (term/cons? pending)) (dotted! pending)
      :else
      (let [step (km-int state (term/km-list (symbol "do") (term/car pending) next-name))]
        (if (refused? step)
          step
          (recur (term/cdr pending) step))))))

(defn do-concurrently
  "Do every action in one next situation.

  No supplied next situation does the first action to create it, then
  does the rest there. change-to-next? enters that situation and stays.
  :value is a one-element list of the next situation."
  [state action-expr km-int & {:keys [next change-to-next?]}]
  (if (some? next)
    (let [classed (taxonomy/isa? (:kb state) next (symbol "Situation"))
          state (assoc state :kb (:kb classed))]
      (if-not (:value classed)
        (user-error state
                    "(do %s %s): %s should be an instance of Situation, but isn't!"
                    (print/km-format action-expr)
                    (print/km-format next)
                    (print/km-format next))
        (let [actions (km-int state action-expr)]
          (if (refused? actions)
            actions
            (let [done (run-each actions (:value actions) next km-int)]
              (if (or (refused? done) (not change-to-next?))
                (assoc done :value (term/km-list next))
                (let [entered (in-situation done next nil km-int)]
                  (assoc entered :value (term/km-list next)))))))))
    (let [actions (km-int state action-expr)]
      (if (refused? actions)
        actions
        (let [first-action (when (term/cons? (:value actions)) (term/car (:value actions)))
              started (unique actions (term/km-list (symbol "do") first-action) km-int)]
          (cond
            (refused? started) started
            (nil? (:value started)) (assoc started :value (term/km-list nil))
            :else
            (let [next-name (:value started)
                  rest-actions (when (term/cons? (:value actions)) (term/cdr (:value actions)))
                  done (run-each started rest-actions next-name km-int)]
              (if (refused? done)
                done
                (if-not change-to-next?
                  (assoc done :value (term/km-list next-name))
                  (let [entered (in-situation done next-name nil km-int)]
                    (assoc entered :value (term/km-list next-name))))))))))))

(defn prompt-text
  "The prompt for the knowledge base's current situation.

  A local situation is [name] KM>. A theory is {name} KM>. Prototype
  mode is [prototype-mode] KM>. Both at once use the commented Lisp
  form and record no error."
  [kb]
  (cond
    (and (frame/local-situation? kb) (some? (frame/curr-prototype kb)))
    (str "[prototype-mode, " (print/km-format (frame/current-situation kb)) "] KM> ")
    (and (frame/local-theory? kb) (some? (frame/curr-prototype kb)))
    (str "[prototype-mode, " (print/km-format (frame/current-situation kb)) "] KM> ")
    (some? (frame/curr-prototype kb)) "[prototype-mode] KM> "
    (frame/local-situation? kb)
    (str "[" (print/km-format (frame/current-situation kb)) "] KM> ")
    (frame/local-theory? kb)
    (str "{" (print/km-format (frame/current-situation kb)) "} KM> ")
    :else "KM> "))
