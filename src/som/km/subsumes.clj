(ns som.km.subsumes
  "Whether an existing instance matches a description.

  is0 does not unify and does not create a Skolem for an (a Class)
  inside the description. (the Class with ...) asks this test of the
  instances already on the object stack. A covered value is dropped
  when a slot is updated. The constraint check uses satisfaction mode.

  The interpreter is passed in as km-int. This namespace does not
  require it. Situations other than the current one, theories, and
  explanations are later steps. Comparing two descriptions builds a
  temporary instance and then restores the knowledge base."
  (:require [som.km.errors :as errors]
            [som.km.explain :as explain]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.minimatch :as match]
            [som.km.taxonomy :as taxonomy]
            [som.km.term :as term]
            [som.km.unify :as unify]
            [som.km.utils :as utils]))

(def ^{:dynamic true
       :doc "The interpreter for one subsumption. Public entries bind it."}
  *km-int*
  nil)

(def ^:private self-symbol (symbol "Self"))
(def ^:private thing (symbol "Thing"))
(def ^:private incomplete :incomplete)

(declare is0 is-value find-one vals-match? find-subsumees)

(defn- refused?
  [state]
  (= "not-ported" (:error state)))

(defn- user-error
  "Record a user error and clear :value, so a stale answer is not a success."
  [state template & args]
  (-> (apply errors/report-error state :user-error template args)
      (assoc :value nil)))

(defn- quiet-km
  "A callback that evaluates nothing. Used when no interpreter is bound."
  [state _ & _]
  (assoc state :value nil))

(defn- callback
  []
  (if (fn? *km-int*) *km-int* quiet-km))

(defn- discard-refusal
  "Drop a not-ported probe and keep the knowledge base and the query.

  The inverse read inside a candidate search is still refused. That
  refusal must not make the whole search a refusal."
  [state]
  (if (refused? state)
    (dissoc state :error :message)
    state))

(defn- km
  [state expr & {:keys [fail-mode target] :or {fail-mode :fail}}]
  (if (fn? *km-int*)
    (*km-int* state expr
              :fail-mode fail-mode
              :target (or target (:target state)))
    (assoc state :value nil)))

(defn- km-unique
  "The one value of expr. Several values keep the first and record that."
  [state expr & {:keys [fail-mode] :or {fail-mode :fail}}]
  (let [found (km state expr :fail-mode fail-mode)]
    (cond
      (refused? found) found
      (term/singleton? (:value found)) (assoc found :value (term/car (:value found)))
      (some? (:value found))
      (-> (errors/report-error found :user-error
                               "Expression %s was expected to return a single value,%nbut it returned multiple values %s!%nJust taking the first...(%s) "
                               (errors/format-term expr)
                               (errors/format-term (:value found))
                               (errors/format-term (term/car (:value found))))
          (assoc :value (term/car (:value found))))
      (= fail-mode :error)
      (-> (errors/report-error found :user-error
                               "Expression %s didn't return a value!"
                               (errors/format-term expr))
          (assoc :value nil))
      :else (assoc found :value nil))))

(defn- adopt
  [state result]
  (cond-> (assoc state :kb (:kb result))
    (contains? result :query) (assoc :query (:query result))
    (:errors result) (assoc :errors (:errors result))
    (:warnings result) (assoc :warnings (:warnings result))
    (:error-structures result) (assoc :error-structures (:error-structures result))))

(defn- nth-el
  [value n]
  (loop [value value
         n n]
    (cond
      (or (nil? value) (not (term/cons? value))) nil
      (zero? n) (term/car value)
      :else (recur (term/cdr value) (dec n)))))

(defn- length-of
  [value]
  (loop [value value
         n 0]
    (cond
      (nil? value) n
      (term/cons? value) (recur (term/cdr value) (inc n))
      :else (throw (ex-info "This list is dotted." {:tail value})))))

(defn- quoted
  [expr]
  (term/km-list (symbol "quote") expr))

(defn- a-class-quote
  []
  (quoted (term/km-list (symbol "a") (symbol "Class"))))

(defn- contains-self?
  "True when Self occurs outside a source marker."
  [expr]
  (cond
    (nil? expr) false
    (utils/eql? expr self-symbol) true
    (explain/source? expr) false
    (term/cons? expr)
    (or (contains-self? (term/car expr))
        (contains-self? (term/cdr expr)))
    :else false))

(defn- bad-existential
  [state expr fail-mode]
  (assoc (if (= fail-mode :error)
           (errors/report-error state :user-error
                                "Bad expression in subsumption testing %s%n(Should be one of (a ?class) or (a ?class with &rest))."
                                (errors/format-term expr))
           state)
         :value nil))

(defn- breakup
  "The class and slot pairs of (a Class) or (a Class with ...).

  called and uniquely-called are slot pairs too. :value is absent when
  the expression is not an existential. fail-mode :error records that."
  [state expr0 & {:keys [fail-mode] :or {fail-mode :fail}}]
  (let [expr (explain/desource-decomment-top-level expr0)
        n (when (utils/lisp-list? expr) (length-of expr))
        head (when (term/cons? expr) (term/car expr))]
    (if-not (and (#{(symbol "a") (symbol "some")} head) n (>= n 2))
      (bad-existential state expr fail-mode)
      (cond
        (term/pair? expr)
        (assoc state :class (nth-el expr 1) :slots nil :value true)
        (utils/eql? (nth-el expr 2) (symbol "with"))
        (assoc state :class (nth-el expr 1)
               :slots (term/cdr (term/cdr (term/cdr expr)))
               :value true)
        (and (utils/eql? (nth-el expr 2) (symbol "called")) (= n 4))
        (assoc state :class (nth-el expr 1)
               :slots (term/km-list (term/km-list (symbol "called")
                                                  (term/km-list (nth-el expr 3))))
               :value true)
        (and (utils/eql? (nth-el expr 2) (symbol "uniquely-called")) (= n 4))
        (assoc state :class (nth-el expr 1)
               :slots (term/km-list (term/km-list (symbol "uniquely-called")
                                                  (term/km-list (nth-el expr 3))))
               :value true)
        (and (utils/eql? (nth-el expr 2) (symbol "called"))
             (utils/eql? (nth-el expr 4) (symbol "with")))
        (assoc state :class (nth-el expr 1)
               :slots (term/cons-cell (term/km-list (symbol "called")
                                                    (term/km-list (nth-el expr 3)))
                                      (term/cdr (term/cdr (term/cdr (term/cdr (term/cdr expr))))))
               :value true)
        (and (utils/eql? (nth-el expr 2) (symbol "uniquely-called"))
             (utils/eql? (nth-el expr 4) (symbol "with")))
        (assoc state :class (nth-el expr 1)
               :slots (term/cons-cell (term/km-list (symbol "uniquely-called")
                                                    (term/km-list (nth-el expr 3)))
                                      (term/cdr (term/cdr (term/cdr (term/cdr (term/cdr expr))))))
               :value true)
        :else (bad-existential state expr fail-mode)))))

(defn path-to-existential-expr
  "The (a Class with ...) described by a path.

  (airplane parts wing) becomes (a wing with (parts-of (airplane))).
  A missing class is Thing. * is Thing."
  [kb path & {:keys [prep] :or {prep (symbol "a")}}]
  (letfn [(step [path embedded prep]
            (if (nil? path)
              embedded
              (let [slot (term/car path)
                    class (cond
                            (utils/eql? (nth-el path 1) (symbol "*")) thing
                            (some? (nth-el path 1)) (nth-el path 1)
                            :else thing)
                    rest-path (term/cdr (term/cdr path))
                    preposition (if (some? rest-path) (symbol "a") prep)
                    inverse (frame/invert-slot kb slot)
                    unit (term/km-list preposition class (symbol "with")
                                       (term/km-list inverse (term/km-list embedded)))]
                (step rest-path unit prep))))]
    (step (term/cdr path) (term/car path) prep)))

(defn- constraint-walk
  "Constraint expressions inside exprs. This is find-constraints-in-exprs."
  [exprs]
  (letfn [(one [expr plural?]
            (cond
              (nil? expr) nil
              (and (term/cons? expr) (kb/unification-operator? (nth-el expr 1)))
              (utils/append-lists
               (term/km-list
                (one (term/car expr) (not (kb/val-unification-operator? (nth-el expr 1))))
                (one (nth-el expr 2) (not (kb/val-unification-operator? (nth-el expr 1))))))
              (and (not plural?) (kb/constraint-expr? expr))
              (term/km-list expr)
              (and plural? (term/singleton? expr))
              (one (term/car expr) false)
              (and plural? (term/cons? expr))
              (loop [expr expr
                     acc []]
                (cond
                  (nil? expr) (term/build-list acc nil)
                  (term/cons? expr)
                  (recur (term/cdr expr)
                         (into acc (utils/elements (one (term/car expr) false))))
                  :else (throw (ex-info "This list is dotted." {:tail expr}))))
              :else nil))]
    (one exprs true)))

(defn- note-slot-flags
  [state slot values]
  (cond-> state
    (or (loop [values values]
          (cond
            (nil? values) false
            (not (term/cons? values)) false
            (kb/constraint-expr? (term/car values)) true
            :else (recur (term/cdr values))))
        (utils/eql? slot (symbol "uniquely-called")))
    (update :kb #(frame/set-are-some % :constraints true))
    (loop [values values]
      (cond
        (nil? values) false
        (not (term/cons? values)) false
        (kb/km-default? (term/car values)) true
        :else (recur (term/cdr values))))
    (update :kb #(frame/set-are-some % :defaults true))
    (or (utils/eql? slot (symbol "called"))
        (utils/eql? slot (symbol "uniquely-called")))
    (update :kb #(frame/set-are-some % :tags true))
    (or (utils/eql? slot (symbol "subslots"))
        (utils/eql? slot (symbol "superslots")))
    (update :kb #(frame/set-are-some % :subslots true))
    (utils/eql? slot (symbol "prototype-of"))
    (update :kb #(frame/set-are-some % :prototypes true))))

(defn- slots-ok?
  "True when slotsvals are (slot (values)) pairs. A bad pair records an error."
  [state slotsvals]
  (if-not (utils/lisp-list? slotsvals)
    (user-error state
                "Bad structure %s for list of slot-values! Should be of form (s1 (v1 ... vn)) (s2 (...)) ..."
                (errors/format-term slotsvals))
    (loop [pairs slotsvals
           state state]
      (cond
        (nil? pairs) (assoc state :value true)
        (not (term/cons? pairs))
        (user-error state "This list is dotted.")
        :else
        (let [pair (term/car pairs)
              slot (when (term/cons? pair) (term/car pair))
              values (nth-el pair 1)]
          (cond
            (not (term/pair? pair))
            (user-error state
                        "Bad structure %s for slot+values! Slot+values should be of the form (slot (v1 ... vn))"
                        (errors/format-term pair))
            (not (term/lisp-symbol? slot))
            (user-error state
                        "Bad structure %s for slot+values! Slot `%s' should be a symbol!"
                        (errors/format-term pair) (errors/format-term slot))
            (not (utils/lisp-list? values))
            (user-error state
                        "Bad structure %s for slot+values! Values %s for slot %s should be a list!"
                        (errors/format-term pair)
                        (errors/format-term values)
                        (errors/format-term slot))
            (contains? kb/reserved-keywords slot)
            (user-error state
                        "Bad structure %s for slot+values! The slot `%s' is a reserved KM keyword, and cannot be used as a slot name!"
                        (errors/format-term pair) (errors/format-term slot))
            :else (recur (term/cdr pairs) (note-slot-flags state slot values))))))))

(defn- ignore-fluent?
  "True when a fluent slot must not be read from the global situation.

  Situations mode starts off, so this stays false until that step."
  [kb slot]
  (and (get-in kb [:runtime :situations-mode?])
       (utils/eql? (frame/current-situation kb) term/global-situation)
       (nil? (get-in kb [:runtime :curr-prototype]))
       (frame/fluent? kb slot)))

(defn- vals-match?
  "True when every expression covers a distinct value.

  An existential is not evaluated. A definite expression is. Nothing is
  unified. :value is the binding list, or nil."
  [state ser-exprs see-vals bindings current-var]
  (cond
    (nil? ser-exprs) (assoc state :value bindings)
    (utils/equal? ser-exprs see-vals) (assoc state :value bindings)
    (not (term/cons? ser-exprs))
    (throw (ex-info "This list is dotted." {:tail ser-exprs}))
    :else
    (let [expr (term/car ser-exprs)]
      (cond
        (or (kb/existential? expr) (term/structured-list? expr))
        (let [found (find-one state expr see-vals bindings)]
          (cond
            (refused? found) found
            (nil? (:covered found)) (assoc found :value nil)
            :else
            (vals-match? found
                         (term/cdr ser-exprs)
                         (utils/remove-items (:covered found) see-vals
                                             :test utils/equal? :count 1)
                         (if current-var
                           (utils/add-binding current-var (:covered found) (:bindings found))
                           (:bindings found))
                         nil)))
        (kb/km-var? expr)
        (let [bound (utils/val-of expr bindings)]
          (cond
            (and bound (utils/member? bound see-vals utils/equal?))
            (vals-match? state (term/cdr ser-exprs)
                         (utils/remove-items bound see-vals :test utils/equal?)
                         bindings nil)
            (and (nil? bound) (term/cons? see-vals))
            (vals-match? state (term/cdr ser-exprs) (term/cdr see-vals)
                         (utils/add-binding expr (term/car see-vals) bindings)
                         nil)
            :else (assoc state :value nil)))
        (and (term/cons? expr) (kb/km-var? (term/car expr)))
        (let [matched (match/full-match expr (term/km-list (symbol "?var") (symbol "==") (symbol "?expr")))]
          (if (nil? matched)
            (user-error state
                        "Bad use of a variable in subsumption expression %s%nExpression must be of the form <var> or (<var> == <expr>)"
                        (errors/format-term expr))
            (let [var (utils/val-of (symbol "?var") matched)
                  body (utils/val-of (symbol "?expr") matched)
                  bound (utils/val-of var bindings)]
              (cond
                bound
                (if-not (utils/member? bound see-vals utils/equal?)
                  (assoc state :value nil)
                  (let [inner (vals-match? state (term/km-list body) (term/km-list bound)
                                           utils/null-bindings nil)]
                    (if (nil? (:value inner))
                      inner
                      (vals-match? inner (term/cdr ser-exprs)
                                   (utils/remove-items bound see-vals :test utils/equal?)
                                   bindings nil))))
                :else
                (vals-match? state (term/cons-cell body (term/cdr ser-exprs))
                             see-vals bindings var)))))
        :else
        (let [found (km state expr)]
          (cond
            (refused? found) found
            (not (every? #(utils/member? % see-vals utils/equal?)
                         (utils/elements (:value found))))
            (assoc found :value nil)
            :else
            (let [values (:value found)
                  noted (cond
                          (or (nil? current-var)
                              (and (some? values) (< (length-of values) 2)))
                          found
                          (nil? values)
                          (errors/report-error found :nodebugger-error
                                               "%s == %s == NIL in subsumption expression; ignoring %s...%n"
                                               (errors/format-term current-var)
                                               (errors/format-term expr)
                                               (errors/format-term current-var))
                          :else
                          (errors/report-error found :nodebugger-error
                                               "%s == %s == %s (multiple values!) in subsumption expression%nJust setting %s == %s (the first value)...%n"
                                               (errors/format-term current-var)
                                               (errors/format-term expr)
                                               (errors/format-term values)
                                               (errors/format-term current-var)
                                               (errors/format-term (term/car values))))
                  bindings (if (or (nil? current-var) (nil? values))
                             bindings
                             (utils/add-binding current-var (term/car values) bindings))]
              (vals-match? noted (term/cdr ser-exprs) see-vals bindings nil))))))))

(defn- find-one
  "The first value in see-vals that expr covers, with its bindings."
  [state expr see-vals bindings]
  (loop [see-vals see-vals
         state state]
    (cond
      (or (nil? see-vals) (not (term/cons? see-vals)))
      (assoc state :covered nil :bindings bindings)
      :else
      (let [candidate (term/car see-vals)
            hit (is0 state candidate expr :bindings bindings)]
        (if (or (refused? hit) (nil? (:value hit)))
          (if (refused? hit)
            hit
            (recur (term/cdr see-vals) hit))
          (assoc hit :covered candidate :bindings (:value hit)))))))

(defn- body-count
  "How many expressions are not constraints. A dotted tail is an error."
  [exprs]
  (loop [exprs exprs
         n 0]
    (cond
      (nil? exprs) n
      (not (term/cons? exprs))
      (throw (ex-info "This list is dotted." {:tail exprs}))
      (kb/constraint-expr? (term/car exprs)) (recur (term/cdr exprs) n)
      :else (recur (term/cdr exprs) (inc n)))))

(defn- slot-covers?
  [state slotvals instance bindings]
  (let [slot (term/car slotvals)
        exprs (nth-el slotvals 1)
        stored (frame/get-vals (:kb state) instance slot
                               :situation (frame/current-situation (:kb state))
                               :query (:query state))
        state (adopt state stored)]
    (if (utils/equal? exprs (:value stored))
      (assoc state :value bindings)
      (if (ignore-fluent? (:kb state) slot)
        (assoc state :value nil)
        (let [read (km state (term/km-list (symbol "the") slot (symbol "of") instance))]
          (if (refused? read)
            read
            (let [see-vals (:value read)
                  pending (constraint-walk exprs)]
              (if (> (body-count exprs) (length-of see-vals))
                (assoc read :value nil)
                (if (utils/eql? slot (symbol "instance-of"))
                  (let [under (taxonomy/classes-subsume-classes? (:kb read) exprs see-vals)]
                    (assoc (adopt read under) :value (when (:value under) bindings)))
                  (let [here (frame/get-vals (:kb read) instance slot
                                             :situation (frame/current-situation (:kb read))
                                             :query (:query read))
                        global (frame/get-vals (:kb here) instance slot
                                               :situation term/global-situation
                                               :query (:query here))
                        read (adopt (adopt read here) global)
                        incomplete? (or (utils/member? incomplete (:value here))
                                        (utils/member? incomplete (:value global)))
                        checked (unify/test-constraints read see-vals pending (callback)
                                                        :slot slot
                                                        :mode :satisfies
                                                        :incomplete? incomplete?)]
                    (if (or (refused? checked) (not (:value checked)))
                      (assoc checked :value nil)
                      (let [bodies (if (frame/single-valued-slot? (:kb checked) slot)
                                     (kb/&-expr-to-vals (term/car exprs))
                                     exprs)]
                        (vals-match? checked bodies see-vals bindings nil)))))))))))))

(defn- slots-cover?
  [state slotsvals instance bindings]
  (cond
    (nil? slotsvals) (assoc state :value bindings)
    (not (term/cons? slotsvals))
    (throw (ex-info "This list is dotted." {:tail slotsvals}))
    :else
    (let [hit (slot-covers? state (term/car slotsvals) instance bindings)]
      (if (or (refused? hit) (nil? (:value hit)))
        hit
        (slots-cover? hit (term/cdr slotsvals) instance (:value hit))))))

(defn- zip-tails
  [left right]
  (loop [left (term/cdr left)
         right (term/cdr right)
         acc []]
    (cond
      (and (nil? left) (nil? right)) (term/build-list acc nil)
      (or (not (term/cons? left)) (not (term/cons? right)))
      (throw (ex-info "This list is dotted." {:tail left}))
      :else
      (recur (term/cdr left) (term/cdr right)
             (conj acc (term/km-list (term/car left) (term/car right)))))))

(defn- pairs-match?
  [state pairs bindings]
  (cond
    (nil? pairs) (assoc state :value bindings)
    :else
    (let [pair (term/car pairs)
          hit (is0 state (term/car pair) (nth-el pair 1) :bindings bindings)]
      (if (or (refused? hit) (nil? (:value hit)))
        hit
        (pairs-match? hit (term/cdr pairs) (:value hit))))))

(defn- structured-match?
  [state instance expr bindings]
  (let [left (explain/desource instance)
        right (explain/desource expr)]
    (if (kb/km-triple? left)
      (let [second (is0 state (nth-el left 1) (nth-el right 1) :bindings bindings)
            third (when (and (not (refused? second)) (:value second))
                    (is0 second (nth-el left 2) (nth-el right 2) :bindings (:value second)))]
        (if (or (nil? third) (refused? third) (nil? (:value third)))
          (or third second)
          (let [values (kb/val-to-vals (nth-el left 3))]
            (loop [values values
                   state third]
              (cond
                (or (nil? values) (not (term/cons? values))) (assoc state :value nil)
                :else
                (let [hit (is0 state (term/car values) (nth-el right 3)
                               :bindings (:value third))]
                  (if (and (not (refused? hit)) (:value hit))
                    hit
                    (if (refused? hit)
                      hit
                      (recur (term/cdr values) hit)))))))))
      (pairs-match? state (zip-tails left right) bindings))))

(defn is0
  "Whether instance matches expr.

  :value is the binding list when it matches, and nil when it does not.
  An (a Class) inside expr is not created and is not unified. A definite
  expression is evaluated. A constraint is tested in satisfaction mode."
  [state instance expr & {:keys [bindings] :or {bindings utils/null-bindings}}]
  (cond
    (and (term/structured-list? instance)
         (term/structured-list? expr)
         (= (length-of (explain/desource instance))
            (length-of (explain/desource expr)))
         (utils/eql? (term/car instance) (term/car expr)))
    (structured-match? state instance expr bindings)
    :else
    (let [parts (breakup state (frame/bind-self expr instance))]
      (cond
        (refused? parts) parts
        (:value parts)
        (let [class (:class parts)
              isa (taxonomy/isa? (:kb parts) instance class)
              ready (adopt parts isa)
              syntax (when (:value isa) (slots-ok? ready (:slots parts)))]
          (cond
            (not (:value isa)) (assoc ready :value nil)
            (or (refused? syntax) (nil? (:value syntax))) syntax
            :else (slots-cover? syntax (:slots parts) instance bindings)))
        (kb/constraint-expr? expr)
        (let [checked (unify/test-constraints state (term/km-list instance) (term/km-list expr)
                                              (callback)
                                              :mode :satisfies)]
          (if (or (refused? checked) (not (:value checked)))
            (assoc checked :value nil)
            (assoc checked :value bindings)))
        :else
        (let [found (km-unique state expr)]
          (cond
            (refused? found) found
            (nil? (:value found)) (assoc found :value nil)
            (utils/equal? (:value found) instance) (assoc found :value bindings)
            :else (assoc found :value nil)))))))

(defn- class-parts
  "The class and slot pairs of a class description, or nil."
  [expr]
  (cond
    (kb/quoted-description? expr)
    (let [body (utils/unquote-expr expr)]
      [(nth-el body 1) (term/cdr (term/cdr (term/cdr body)))])
    (kb/the-class? expr)
    (let [class (nth-el expr 1)
          slots (if (utils/eql? (nth-el expr 2) (symbol "called"))
                  (term/cons-cell (term/km-list (symbol "called") (term/km-list (nth-el expr 3)))
                                  (term/cdr (term/cdr (term/cdr (term/cdr (term/cdr expr))))))
                  (term/cdr (term/cdr (term/cdr expr))))]
      [class slots])
    :else nil))

(defn- instance-description?
  "A quoted (a ...) or a quoted triple. :error records any other quote."
  [state expr fail-mode]
  (cond
    (and (utils/quote? expr) (term/cons? (utils/unquote-expr expr)))
    (let [body (utils/unquote-expr expr)]
      (cond
        (or (kb/existential? body) (kb/km-triple? body)) (assoc state :value expr)
        (= fail-mode :error)
        (if (utils/eql? (term/car body) (symbol "every"))
          (user-error state
                      "Expecting an instance description '(a ...), but found a class%ndescription %s instead!"
                      (errors/format-term expr))
          (user-error state
                      "Expecting an instance description '(a ...), but found%ndescription %s instead!"
                      (errors/format-term expr)))
        :else (assoc state :value nil)))
    (= fail-mode :error)
    (user-error state
                "Expecting a quoted instance description '(a ...), but found an unquoted%nexpression %s instead!"
                (errors/format-term expr))
    :else (assoc state :value nil)))

(defn- description-of
  "A class description for one set of values, or nil when it is instances."
  [state classes]
  (cond
    (and (term/singleton? classes) (kb/kb-object? (term/car classes)))
    (assoc state :description (quoted (term/km-list (symbol "every") (term/car classes))))
    (and (term/singleton? classes) (kb/description? (term/car classes)))
    (if-let [[class slots] (class-parts (term/car classes))]
      (assoc state :description
             (quoted (if (some? slots)
                       (term/build-list [(symbol "every") class (symbol "with")] slots)
                       (term/km-list (symbol "every") class))))
      (-> (errors/report-error state :user-error
                                "Subsumption with %s:%nDon't know how to do subsumption with this kind of expression!"
                                (errors/format-term (term/car classes)))
          (dissoc :description)
          (assoc :value nil)))
    :else state))

(defn- every-to-a
  [description]
  (let [[class slots] (class-parts description)]
    (quoted (if (some? slots)
              (term/build-list [(symbol "a") class (symbol "with")] slots)
              (term/km-list (symbol "a") class)))))

(defn- slotless-class
  "The class of (a Class) or (a Class with) when no slots are present."
  [expr]
  (let [parts (breakup {:kb nil} (utils/unquote-expr expr))]
    (when (and (:value parts) (nil? (:slots parts)))
      (:class parts))))

(defn- description-subsumes
  "Whether the x description matches the y description.

  Two slotless descriptions use the stored subclass links. A description
  with slots builds a temporary instance, tests it, and restores the
  knowledge base and the query. The Lisp undoes a checkpoint for the
  same reason. The answer and any recorded errors stay."
  [state x-desc y-desc]
  (let [x-class (slotless-class x-desc)
        y-class (slotless-class y-desc)]
    (if (and x-class y-class)
      (let [under (taxonomy/is-subclass-of? (:kb state) x-class y-class)]
        (assoc (adopt state under) :value (when (:value under) utils/null-bindings)))
      (let [saved-kb (:kb state)
            saved-query (:query state)
            made (km-unique state (utils/unquote-expr x-desc) :fail-mode :error)
            tested (cond
                     (refused? made) made
                     (nil? (:value made)) (assoc made :value nil)
                     :else (is0 made (:value made) (utils/unquote-expr y-desc)))]
        (assoc tested :kb saved-kb :query saved-query)))))

(defn is-value
  "Whether x matches y under is.

  An instance against a quoted (a Class) uses is0. Two instances use =.
  '(a Class) succeeds for a class name or a class description. :value is
  truthy or nil."
  [state x y km-int]
  (binding [*km-int* km-int]
    (if (utils/equal? y (a-class-quote))
      (if (or (term/lisp-symbol? x) (class-parts x))
        (assoc state :value utils/null-bindings)
        (user-error state
                    "Doing (%s is %s)%n%s doesn't appear to be a class or class description."
                    (errors/format-term x)
                    (errors/format-term y)
                    (errors/format-term x)))
      (let [quoted-list? (fn [expr]
                           (and (utils/quote? expr) (term/cons? (utils/unquote-expr expr))))
            x-desc (if (quoted-list? x)
                     (instance-description? state x :error)
                     (assoc state :value nil))
            y-desc (cond
                     (refused? x-desc) x-desc
                     (quoted-list? y) (instance-description? x-desc y :error)
                     :else (assoc x-desc :value nil))]
        (cond
          (refused? y-desc) y-desc
          (and (:value x-desc) (:value y-desc))
          (description-subsumes y-desc (:value x-desc) (:value y-desc))
          (:value x-desc)
          (user-error y-desc
                      "Doing (%s is %s)%nCan't test if an expression is `subsumed' by an instance!"
                      (errors/format-term x)
                      (errors/format-term y))
          (:value y-desc)
          (is0 y-desc x (utils/unquote-expr (:value y-desc)))
          :else (km y-desc (term/km-list x (symbol "=") y)))))))

(defn subsumes-values
  "Whether the values xs subsume the values ys.

  A class becomes '(every Class). Two class descriptions compare by is.
  A class against instances asks allof, which is still refused. A set
  against a class description is an error. Two instance sets use
  is-superset-of."
  [state xs ys km-int]
  (binding [*km-int* km-int]
    (let [x-state (description-of state xs)
          y-state (if (refused? x-state) x-state (description-of x-state ys))]
      (cond
        (refused? y-state) y-state
        (and (:description x-state) (:description y-state))
        (is-value y-state (every-to-a (:description y-state))
                  (every-to-a (:description x-state))
                  km-int)
        (:description x-state)
        (km y-state (term/km-list (symbol "allof")
                                  (kb/vals-to-val ys)
                                  (symbol "must")
                                  (term/km-list (:description x-state) (symbol "covers") (symbol "It"))))
        (:description y-state)
        (user-error y-state
                    "Doing (%s subsumes %s)%nCan't test if a set subsumes an expression!"
                    (errors/format-term xs)
                    (errors/format-term ys))
        :else
        (km y-state (term/km-list (kb/vals-to-val xs)
                                  (symbol "is-superset-of")
                                  (kb/vals-to-val ys)))))))

(defn covers-value
  "Whether the values xs cover y.

  A class description covering an instance asks is. The covers operator
  itself is rewritten to isa. This function is what isa calls when the
  class side is not a frame name."
  [state xs y km-int]
  (binding [*km-int* km-int]
    (let [x-state (description-of state xs)
          y-desc (if (and (utils/quote? y) (term/cons? (utils/unquote-expr y)))
                   (instance-description? x-state y :error)
                   (assoc x-state :value nil))]
      (cond
        (refused? y-desc) y-desc
        (and (:description x-state) (:value y-desc))
        (km y-desc (term/km-list (:value y-desc) (symbol "is") (every-to-a (:description x-state))))
        (:description x-state)
        (km y-desc (term/km-list y (symbol "is") (every-to-a (:description x-state))))
        (:value y-desc)
        (km y-desc (term/km-list (symbol "has-value")
                                 (term/km-list (symbol "oneof")
                                               (kb/vals-to-val xs)
                                               (symbol "where")
                                               (term/km-list (symbol "It") (symbol "is") (:value y-desc)))))
        :else
        (km y-desc (term/km-list (kb/vals-to-val xs) (symbol "includes") y))))))

(defn- kb-objects
  "The knowledge-base names in values, in order."
  [values]
  (loop [values values
         acc []]
    (cond
      (nil? values) (term/build-list acc nil)
      (not (term/cons? values))
      (throw (ex-info "This list is dotted." {:tail values}))
      (kb/kb-object? (term/car values))
      (recur (term/cdr values) (conj acc (term/car values)))
      :else (recur (term/cdr values) acc))))

(defn- probe-inverse
  "Read (the class invslot of vals). A refusal is discarded.

  That pattern is not ported yet, so the read does not add candidates.
  The object stack remains the candidate set."
  [state class inverse vals]
  (if (nil? vals)
    state
    (discard-refusal
     (km state (term/km-list (symbol "the") class inverse (symbol "of")
                             (kb/vals-to-val vals))))))

(defn- probe-candidates
  "Evaluate inverses of the description so cached values are ready.

  A nested existential is searched. Each knowledge-base object it finds
  is probed with (the class inverse of value). A plain value is
  evaluated, and its knowledge-base objects are probed the same way.
  A form that is not ported yet is discarded, and the search continues
  on the object stack."
  [state class slotsvals]
  (loop [slotsvals slotsvals
         state state]
    (if (or (nil? slotsvals) (not (term/cons? slotsvals)))
      state
      (let [pair (term/car slotsvals)
            slot (term/car pair)
            inverse (frame/invert-slot (:kb state) slot)
            values (nth-el pair 1)
            state (loop [values values
                         state state]
                    (if (or (nil? values) (not (term/cons? values)))
                      state
                      (let [expr (term/car values)
                            state (if (kb/existential? expr)
                                    (let [found (discard-refusal (find-subsumees state expr))]
                                      (loop [vals (:value found)
                                             state found]
                                        (if (or (nil? vals) (not (term/cons? vals)))
                                          state
                                          (let [val (term/car vals)]
                                            (recur (term/cdr vals)
                                                   (if (kb/kb-object? val)
                                                     (probe-inverse state class inverse
                                                                    (term/km-list val))
                                                     state))))))
                                    (let [evaluated (discard-refusal (km state expr))
                                          objects (kb-objects (:value evaluated))]
                                      (if (nil? objects)
                                        evaluated
                                        (probe-inverse evaluated class inverse objects))))]
                        (recur (term/cdr values) state))))]
        (recur (term/cdr slotsvals) state)))))

(defn find-subsumees
  "Instances on the object stack that match an (a Class with ...) expression.

  The inverse probe may be a form that is not ported yet. That refusal
  is dropped. No instance is created. :value is the matching instances,
  newest first."
  [state existential]
  (let [parts (breakup state existential :fail-mode :error)]
      (if (or (refused? parts) (nil? (:value parts)))
        (assoc parts :value nil)
        (let [probed (probe-candidates parts (:class parts) (:slots parts))
              stacked (frame/obj-stack (:kb probed) (:query probed))
              state (adopt probed stacked)]
          (loop [stack (:value stacked)
                 state state
                 acc []]
            (cond
              (or (nil? stack) (not (term/cons? stack)))
              (assoc state :value (term/build-list acc nil))
              :else
              (let [candidate (term/car stack)
                    isa (taxonomy/isa? (:kb state) candidate (:class parts))
                    state (adopt state isa)]
                (if-not (:value isa)
                  (recur (term/cdr stack) state acc)
                  (let [hit (is0 state candidate existential)]
                    (cond
                      (refused? hit) hit
                      (:value hit) (recur (term/cdr stack) hit (conj acc candidate))
                      :else (recur (term/cdr stack) hit acc)))))))))))

(defn- coercion-hit
  "An instance covered by expr, or nil. A refused probe does not stick."
  [state expr instances allow-coercion? eagerly? target]
  (if-not (or (kb/existential? expr) (term/structured-list? expr))
    [state nil]
    (loop [instances instances
           state state]
      (cond
        (or (nil? instances) (not (term/cons? instances))) [state nil]
        :else
        (let [instance (term/car instances)]
          (cond
            (and (frame/an-instance? (:kb state) instance)
                 allow-coercion?
                 (not (contains-self? expr)))
            (let [joiner (if eagerly? (symbol "&+!") (symbol "&+"))
                  probed (km state (term/km-list instance joiner expr)
                             :fail-mode :fail
                             :target target)]
              (cond
                (refused? probed) (recur (term/cdr instances) state)
                (some? (:value probed)) [probed instance]
                :else (recur (term/cdr instances) probed)))
            (and (kb/existential? instance) (not (contains-self? expr)))
            (let [probed (km state (term/km-list (quoted instance) (symbol "is") (quoted expr))
                             :fail-mode :fail
                             :target target)]
              (cond
                (refused? probed) (recur (term/cdr instances) state)
                (some? (:value probed)) [probed instance]
                :else (recur (term/cdr instances) probed)))
            :else (recur (term/cdr instances) state)))))))

(defn remove-subsuming-exprs
  "Drop expressions that cover an instance, and those instances.

  :exprs are the expressions that covered nothing. :instances are the
  instances that no expression covered. allow-coercion uses &+ or &+!,
  which may write. A failed coercion leaves that attempt unchanged.
  Explanations are not recorded. A later (a Class) is not created."
  [state exprs instances & {:keys [allow-coercion? eagerly? target]}]
  (loop [exprs exprs
           instances instances
           state state
           unused []]
      (cond
        (or (nil? exprs) (nil? instances))
        (assoc state
               :exprs (term/build-list (into unused (utils/elements exprs)) nil)
               :instances instances
               :subsumed nil)
        (not (term/cons? exprs))
        (throw (ex-info "This list is dotted." {:tail exprs}))
        :else
        (let [expr (term/car exprs)
              [state hit] (coercion-hit state expr instances allow-coercion? eagerly? target)]
          (if (nil? hit)
            (recur (term/cdr exprs) instances state (conj unused expr))
            (recur (term/cdr exprs)
                   (utils/remove-items hit instances :test utils/equal? :count 1)
                   state
                   unused))))))

(defn- covered-value
  "The value in older that expr covers, or nil."
  [state expr older]
  (loop [older older
         state state]
    (cond
      (or (nil? older) (not (term/cons? older))) (assoc state :covered nil)
      :else
      (let [val (term/car older)]
        (cond
          (frame/an-instance? (:kb state) val)
          (let [hit (is0 state val expr)]
            (if (and (not (refused? hit)) (:value hit))
              (assoc hit :covered val)
              (if (refused? hit)
                hit
                (recur (term/cdr older) hit))))
          (kb/existential? val)
          (let [hit (is-value state (quoted val) (quoted expr) *km-int*)]
            (if (and (not (refused? hit)) (:value hit))
              (assoc hit :covered val)
              (if (refused? hit)
                (recur (term/cdr older) state)
                (recur (term/cdr older) hit))))
          :else (recur (term/cdr older) state))))))

(defn valset-subsumes-valset?
  "True when every value in newer covers a distinct value in older.

  Equal values match first. An existential in newer can cover an
  instance, or another existential, without creating a Skolem. :value
  is true or false."
  [state newer older]
  (loop [newer newer
           older older
           state state]
      (cond
        (nil? newer) (assoc state :value true)
        (nil? older) (assoc state :value false)
        (not (term/cons? newer)) (throw (ex-info "This list is dotted." {:tail newer}))
        (not (term/cons? older)) (throw (ex-info "This list is dotted." {:tail older}))
        (utils/member? (term/car newer) older utils/equal?)
        (recur (term/cdr newer)
               (utils/remove-items (term/car newer) older :test utils/equal? :count 1)
               state)
        (kb/existential? (term/car newer))
        (let [found (covered-value state (term/car newer) older)]
          (if (or (refused? found) (nil? (:covered found)))
            (if (refused? found) found (assoc found :value false))
            (recur (term/cdr newer)
                   (utils/remove-items (:covered found) older :test utils/equal? :count 1)
                   found)))
        :else (assoc state :value false))))

(alter-var-root #'frame/*valset-subsumes* (constantly valset-subsumes-valset?))
(alter-var-root #'unify/*remove-subsuming* (constantly remove-subsuming-exprs))
