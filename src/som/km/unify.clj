(ns som.km.unify
  "Lazy unification and the constraint interpreter.

  & and &! combine two values and keep the result. && and &+ combine
  them only when one value's classes subsume the other's, using the
  classes stored so far. &? and &+? only test. A failed pair inside &&
  is skipped, so two values whose classes do not subsume both stay.
  &+ may fail and leaves the knowledge base unchanged. The test
  operators discard the trial. Evaluating their arguments still commits.

  A lazy result may leave (_A & _B) or ((_A _B) && (_C)) on a slot.
  The next read of that slot finishes it. &! does not leave a residue.
  This step does not create a Skolem for (a Class). When
  *remove-subsuming* is set, an existential that covers an instance is
  dropped. &+ inside that check may write the instance's slots.

  Constraints distinguish a consistent value from a satisfied one.
  at-least and exactly do not invent filler instances.
  A class rule is applied by the slot reader. Prototypes, explanations,
  and situations other than *Global are later steps. Description
  subsumption is som.km.subsumes.

  The interpreter is passed in as km-int. This namespace does not
  require it, and it does not require the slot-value reader."
  (:require [som.km.errors :as errors]
            [som.km.explain :as explain]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.stack :as stack]
            [som.km.taxonomy :as taxonomy]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(def max-padding-instances
  "How many filler instances at-least and exactly may create. Zero means none."
  0)

(def remove-violating-instances?
  "When false, a violated value stays in the list and the violation is recorded."
  false)

(def ^:private ^:dynamic *km-int*
  "The interpreter callback for one unification. Public entry points bind it."
  nil)

(def ^{:dynamic true
       :doc "Drops expressions that cover an instance during &&.

  Nil keeps every value. som.km.subsumes installs the real test at load
  time. The var lives here so unification does not require that namespace."}
  *remove-subsuming*
  nil)

(def ^:private neq-slot (symbol nil "/=="))
(def ^:private thing (symbol "Thing"))
(def ^:private exactly-one-thing
  (term/km-list (symbol "exactly") 1 thing))

(defn- refused?
  [state]
  (= "not-ported" (:error state)))

(defn- km
  [state expr & {:keys [fail-mode target] :or {fail-mode :fail}}]
  (*km-int* state expr :fail-mode fail-mode :target (or target (:target state))))

(defn- adopt
  [state result]
  (cond-> (assoc state :kb (:kb result))
    (contains? result :query) (assoc :query (:query result))))

(defn- succeed
  [state value]
  (assoc state :ok true :value value))

(defn- fail
  [state]
  (assoc state :ok false :value nil))

(defn- length-of
  [value]
  (loop [value value
         seen 0]
    (cond
      (nil? value) seen
      (term/cons? value) (recur (term/cdr value) (inc seen))
      :else nil)))

(defn- nth-el
  [value n]
  (loop [value value
         n n]
    (cond
      (or (nil? value) (not (term/cons? value))) nil
      (zero? n) (term/car value)
      :else (recur (term/cdr value) (dec n)))))

(defn- operator
  [eagerly? classes-subsumep]
  (cond
    (and eagerly? classes-subsumep) (symbol "&+!")
    eagerly? (symbol "&!")
    classes-subsumep (symbol "&+")
    :else (symbol "&")))

(defn- report-unification
  [state template & args]
  (-> (apply errors/report-error state :user-error template args)
      (assoc :unification-reported true)))

(defn- unique
  "One value of expr. The messages match km-unique-int.

  fail-mode defaults to :fail, including when the caller is unifying
  in :error mode. The Lisp evaluates these arguments that way."
  [state expr & {:keys [fail-mode target] :or {fail-mode :fail}}]
  (let [found (km state expr :fail-mode fail-mode :target target)]
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
      (errors/report-error found :user-error "Expression %s didn't return a value!"
                           (errors/format-term expr))
      :else found)))

(defn- drop-items
  [value pred]
  (loop [value value
         acc []]
    (cond
      (nil? value) (term/build-list acc nil)
      (not (term/cons? value)) value
      (pred (term/car value)) (recur (term/cdr value) acc)
      :else (recur (term/cdr value) (conj acc (term/car value))))))

(defn- drop-nil-values
  [values]
  (drop-items values nil?))

(defn- keep-items
  [value pred]
  (loop [value value
         acc []]
    (cond
      (nil? value) (term/build-list acc nil)
      (not (term/cons? value)) value
      (pred (term/car value)) (recur (term/cdr value) (conj acc (term/car value)))
      :else (recur (term/cdr value) acc))))

(defn- ordered-difference
  [left right]
  (loop [left left
         acc []]
    (cond
      (nil? left) (term/build-list acc nil)
      (not (term/cons? left)) left
      (utils/member? (term/car left) right utils/equal?)
      (recur (term/cdr left) acc)
      :else (recur (term/cdr left) (conj acc (term/car left))))))

(defn- subbag?
  [smaller larger]
  (loop [smaller smaller
         larger larger]
    (cond
      (nil? smaller) true
      (or (nil? larger) (not (term/cons? smaller))) false
      (utils/member? (term/car smaller) larger utils/equal?)
      (recur (term/cdr smaller)
             (utils/remove-items (term/car smaller) larger
                                 :test utils/equal? :count 1))
      :else false)))

(defn- any-anonymous?
  [kb values]
  (loop [values values]
    (cond
      (nil? values) false
      (not (term/cons? values)) false
      (frame/anonymous-instance? kb (term/car values)) true
      :else (recur (term/cdr values)))))

(defn- inherit-overrides?
  [kb slot]
  (and (kb/kb-object? slot)
       (some? (:value (frame/get-vals kb slot (symbol "inherit-with-overrides")
                                      :situation term/global-situation
                                      :dereference? false)))))

(defn- constraint-walk
  "Constraint expressions inside expr. plurality is :plural or :singular.

  A unification of four or more elements is rewritten before the walk.
  This walk does not report a badly formed unification. The unifying
  procedure reports that sentence."
  [expr plurality]
  (cond
    (nil? expr) nil
    (and (term/cons? expr)
         (kb/unification-operator? (nth-el expr 1))
         (when-let [n (length-of expr)] (>= n 4)))
    (constraint-walk (term/km-list (term/car expr) (nth-el expr 1) (term/cdr (term/cdr expr)))
                     :singular)
    (and (term/cons? expr) (kb/unification-operator? (nth-el expr 1)))
    (let [side (if (kb/val-unification-operator? (nth-el expr 1)) :singular :plural)]
      (utils/append-lists (term/km-list (constraint-walk (term/car expr) side)
                                        (constraint-walk (nth-el expr 2) side))))
    (and (= plurality :plural) (term/singleton? expr))
    (constraint-walk (term/car expr) :singular)
    (and (= plurality :singular) (kb/constraint-expr? expr))
    (term/km-list expr)
    (and (= plurality :plural) (term/cons? expr))
    (loop [expr expr
           acc nil]
      (cond
        (nil? expr) acc
        (not (term/cons? expr)) expr
        :else (recur (term/cdr expr)
                     (utils/append-lists
                      (term/km-list acc (constraint-walk (term/car expr) :singular))))))
    :else nil))

(defn- remove-constraints
  "Values with constraint expressions removed.

  When no constraint has been seen, the values are returned unchanged.
  A singleton (& ...) list is split before the constraints are dropped."
  [kb values]
  (cond
    (not (frame/are-some? kb :constraints)) values
    (nil? values) nil
    (and (term/singleton? values)
         (term/cons? (term/car values))
         (kb/val-unification-operator? (nth-el (term/car values) 1)))
    (drop-items (kb/&-expr-to-vals (term/car values)) kb/constraint-expr?)
    :else (drop-items values kb/constraint-expr?)))

(defn- extract-constraints
  "The constraint expressions in a list of values.

  The shape matches remove-constraints. No recorded constraint means none."
  [kb values]
  (cond
    (not (frame/are-some? kb :constraints)) nil
    (nil? values) nil
    (and (term/singleton? values)
         (term/cons? (term/car values))
         (kb/val-unification-operator? (nth-el (term/car values) 1)))
    (keep-items (kb/&-expr-to-vals (term/car values)) kb/constraint-expr?)
    :else (keep-items values kb/constraint-expr?)))

(defn- special-slot
  [kb slot]
  (cond
    (nil? slot) nil
    (frame/remove-subsumers-slot? kb slot) :remove-subsumers
    (frame/remove-subsumees-slot? kb slot) :remove-subsumees
    :else nil))

(defn- subst-symbol
  [new old expr]
  (cond
    (utils/eql? expr old) new
    (term/cons? expr)
    (term/cons-cell (subst-symbol new old (term/car expr))
                    (subst-symbol new old (term/cdr expr)))
    :else expr))

(defn- class-of-existential
  [expr]
  (nth-el (explain/desource-decomment-top-level expr) 1))

(defn- adjacent-pairs
  [values]
  (loop [values values
         acc []]
    (if (or (nil? values) (not (term/cons? (term/cdr values))))
      acc
      (recur (term/cdr values)
             (conj acc [(term/car values) (term/car (term/cdr values))])))))

(defn- all-pairs
  [values]
  (loop [values values
         acc []]
    (if (or (nil? values) (not (term/cons? (term/cdr values))))
      acc
      (let [head (term/car values)
            rest (term/cdr values)]
        (recur rest
               (into acc (mapv (fn [other] [head other]) (utils/elements rest))))))))

(declare incompatible-problem check-slotvals simple-unifiable)

(defn- test-val-constraint
  [state val constraint special mode]
  (cond
    (kb/constraint-expr? val) (succeed state true)
    (kb/retain-expr? constraint) (succeed state true)
    (utils/eql? (term/car constraint) (symbol "no-inheritance")) (succeed state true)
    (utils/eql? (term/car constraint) (symbol "must-be-a"))
    (cond
      (and (kb/kb-object? val)
           (:value (taxonomy/isa? (:kb state) val (symbol "Aggregate"))))
      (let [isa (taxonomy/isa? (:kb state) val (symbol "Aggregate"))
            state (adopt state isa)
            element (if (term/structured-list? val)
                     (assoc state :value nil)
                     (km state (term/km-list (symbol "the") (symbol "element-type")
                                             (symbol "of") val)))]
        (if (refused? element)
          element
          (if (nil? (:value element))
            (succeed element true)
            (let [fit (taxonomy/compatible-classes?
                       (:kb element)
                       :classes1 (:value element)
                       :classes2 (term/km-list (nth-el constraint 1)))]
              (succeed (adopt element fit) (boolean (:value fit)))))))
      (utils/equal? (explain/desource-decomment constraint)
                    (term/km-list (symbol "must-be-a") thing))
      (succeed state true)
      (= mode :satisfies)
      (let [hit (taxonomy/isa? (:kb state) val (nth-el constraint 1))]
        (succeed (adopt state hit) (boolean (:value hit))))
      :else
      (let [probed (km state (term/km-list val (symbol "&?")
                                           (term/cons-cell (symbol "a") (term/cdr constraint))))]
        (if (refused? probed) probed (succeed probed (some? (:value probed))))))

    (utils/eql? (term/car constraint) (symbol "mustnt-be-a"))
    (let [hit (taxonomy/isa? (:kb state) val (nth-el constraint 1))]
      (succeed (adopt state hit) (not (:value hit))))

    (utils/eql? (term/car constraint) (symbol "<>"))
    (let [banned (nth-el constraint 1)]
      (if (kb/is-simple-km-term? banned)
        (case special
          :remove-subsumers
          (let [under (taxonomy/is-subclass-of? (:kb state) val banned)]
            (succeed (adopt state under) (nil? (:value under))))
          :remove-subsumees
          (let [under (taxonomy/is-subclass-of? (:kb state) banned val)]
            (succeed (adopt state under) (nil? (:value under))))
          (succeed state (not (utils/equal? val banned))))
        (let [probed (km state (term/km-list val (symbol "/=") banned))]
          (if (refused? probed) probed (succeed probed (some? (:value probed)))))))

    (utils/eql? (term/car constraint) (symbol "excluded-values"))
    (let [found (km state (kb/vals-to-val (term/cdr constraint)))]
      (cond
        (refused? found) found
        (nil? (:value found)) (succeed found true)
        (= special :remove-subsumers)
        (let [above (taxonomy/all-superclasses0 (:kb found) val)]
          (succeed (adopt found above)
                   (not (some #(utils/member? % (:value found))
                              (utils/elements (:value above))))))
        ;; all-subclasses waits for inheritance. Until then this slot
        ;; does not reject a value for excluded-values.
        (= special :remove-subsumees) (succeed found true)
        :else (succeed found (not (utils/member? val (:value found) utils/equal?)))))

    (utils/eql? (term/car constraint) (symbol "possible-values"))
    (let [found (km state (kb/vals-to-val (term/cdr constraint)))]
      (cond
        (refused? found) found
        (nil? (:value found)) (succeed found false)
        (#{:remove-subsumers :remove-subsumees} special)
        (let [disjoint (taxonomy/disjoint-class-sets
                        (:kb found) (term/km-list val) (:value found))]
          (succeed (adopt found disjoint) (nil? (:value disjoint))))
        (= mode :satisfies)
        (succeed found (boolean (utils/member? val (:value found) utils/equal?)))
        :else
        (loop [possible (:value found)
               current found]
          (cond
            (refused? current) current
            (nil? possible) (succeed current false)
            :else
            (let [probed (km current (term/km-list val (symbol "&?") (term/car possible)))]
              (cond
                (refused? probed) probed
                (some? (:value probed)) (succeed probed true)
                :else (recur (term/cdr possible) probed)))))))

    (utils/eql? (term/car constraint) (symbol "constraint"))
    (let [body (subst-symbol val (symbol "TheValue") (nth-el constraint 1))]
      (if (stack/looping-on? (:kb state) (:query state) body)
        (succeed state true)
        (let [found (km state body)]
          (if (refused? found) found (succeed found (some? (:value found)))))))

    :else
    (-> (errors/report-error state :user-error "Unrecognized form of constraint %s"
                             (errors/format-term constraint))
        fail)))

(defn- violated-val
  [state val constraints special mode]
  (loop [constraints constraints
         state state]
    (cond
      (refused? state) state
      (nil? constraints) (assoc state :value nil)
      (not (kb/val-constraint? (term/car constraints)))
      (recur (term/cdr constraints) state)
      :else
      (let [tested (test-val-constraint state val (term/car constraints) special mode)]
        (cond
          (refused? tested) tested
          (:value tested) (recur (term/cdr constraints) tested)
          :else (assoc tested :value [(term/car constraints) val]))))))

(defn- isa-count
  [state values class]
  (loop [values values
         state state
         seen 0]
    (cond
      (nil? values) [state seen]
      (not (term/cons? values)) [state seen]
      :else
      (let [hit (taxonomy/isa? (:kb state) (term/car values) class)
            state (adopt state hit)]
        (recur (term/cdr values) state (if (:value hit) (inc seen) seen))))))

(defn- vals-in-class
  [state values class]
  (loop [values values
         state state
         acc []]
    (cond
      (nil? values) [state (term/build-list acc nil)]
      (not (term/cons? values)) [state (term/build-list acc nil)]
      :else
      (let [hit (taxonomy/isa? (:kb state) (term/car values) class)
            state (adopt state hit)]
        (recur (term/cdr values)
               state
               (if (:value hit) (conj acc (term/car values)) acc))))))

(defn- set-constraint-satisfied
  [state values0 constraint incomplete?]
  (cond
    (utils/eql? constraint :incomplete) (succeed state true)
    (not (term/cons? constraint))
    (-> (errors/report-error state :user-error "Unrecognized form of set constraint %s"
                             (errors/format-term constraint))
        fail)
    :else
    (let [values (remove-constraints (:kb state) values0)
          class (nth-el constraint 2)
          forced (when (and (#{(symbol "at-most") (symbol "exactly")} (term/car constraint))
                            (= 1 (nth-el constraint 1)))
                   class)
          [state in-class] (if forced
                             (vals-in-class state values forced)
                             [state nil])]
      (if (and forced (> (or (length-of in-class) 0) 1))
        (loop [pairs (adjacent-pairs in-class)
               current state]
          (cond
            (refused? current) current
            (empty? pairs) (succeed current true)
            :else
            (let [[a b] (first pairs)
                  probed (km current (term/km-list a (symbol "&?") b))]
              (cond
                (refused? probed) probed
                (nil? (:value probed)) (succeed probed false)
                :else (recur (rest pairs) probed)))))
        (case (term/car constraint)
          (at-least exactly at-most)
          (let [[state nvals] (isa-count state values class)
                n (nth-el constraint 1)
                ok (case (term/car constraint)
                     at-least (>= nvals n)
                     exactly (and (not incomplete?) (= nvals n))
                     at-most (and (not incomplete?) (<= nvals n)))]
            (succeed state ok))
          set-constraint
          (let [body (subst-symbol (kb/vals-to-val values) (symbol "TheValues")
                                   (nth-el constraint 1))
                found (km state body)]
            (if (refused? found) found (succeed found (some? (:value found)))))
          sometimes (succeed state true)
          set-filter (succeed state true)
          (-> (errors/report-error state :user-error
                                   "Unrecognized form of set constraint %s"
                                   (errors/format-term constraint))
              fail))))))

(defn- extract-in-class
  [state exprs class]
  (loop [exprs exprs
         state state
         acc []]
    (cond
      (nil? exprs) [state (term/build-list acc nil)]
      (not (term/cons? exprs)) [state (term/build-list acc nil)]
      (kb/existential? (term/car exprs))
      (let [under (taxonomy/is-subclass-of?
                   (:kb state) (class-of-existential (term/car exprs)) class)
            state (adopt state under)]
        (recur (term/cdr exprs) state
               (if (:value under) (conj acc (term/car exprs)) acc)))
      (kb/fully-evaluated? (term/car exprs))
      (let [hit (taxonomy/isa? (:kb state) (term/car exprs) class)
            state (adopt state hit)]
        (recur (term/cdr exprs) state
               (if (:value hit) (conj acc (term/car exprs)) acc)))
      :else (recur (term/cdr exprs) state acc))))

(defn- classes-for-score
  [state value]
  (cond
    (kb/kb-object? value) (taxonomy/immediate-classes (:kb state) value)
    (kb/existential? value)
    {:kb (:kb state) :value (term/km-list (class-of-existential value))}
    :else {:kb (:kb state) :value nil}))

(defn- score-classes
  [state x y]
  (let [left (classes-for-score state x)
        right (classes-for-score (adopt state left) y)
        state (adopt (adopt state left) right)
        classes1 (:value left)
        classes2 (:value right)]
    (if (or (nil? classes1) (nil? classes2))
      (succeed state 5)
      (let [fit (taxonomy/compatible-classes? (:kb state)
                                              :classes1 classes1
                                              :classes2 classes2)]
        (if-not (:value fit)
          (succeed (adopt state fit) nil)
          (let [same (loop [items (utils/elements classes1)
                            state (adopt state fit)]
                       (if (empty? items)
                         [state true]
                         (if (utils/member? (first items) classes2)
                           (recur (rest items) state)
                           [state false])))]
            (if (and (second same)
                     (loop [items (utils/elements classes2)]
                       (or (empty? items)
                           (and (utils/member? (first items) classes1)
                                (recur (rest items))))))
              (succeed (first same) 60)
              (if (some #(utils/member? % classes2) (utils/elements classes1))
                (succeed (first same) 30)
                (let [related (loop [xs (utils/elements classes1)
                                     state (first same)]
                                (if (empty? xs)
                                  [state false]
                                  (let [hit (loop [ys (utils/elements classes2)
                                                   state state]
                                              (if (empty? ys)
                                                [state false]
                                                (let [forward (taxonomy/is-subclass-of?
                                                               (:kb state) (first xs) (first ys))
                                                      backward (if (:value forward)
                                                                 forward
                                                                 (taxonomy/is-subclass-of?
                                                                  (:kb forward) (first ys) (first xs)))]
                                                  (if (:value backward)
                                                    [(adopt state backward) true]
                                                    (recur (rest ys) (adopt state backward))))))]
                                    (if (second hit)
                                      hit
                                      (recur (rest xs) (first hit))))))]
                  (succeed (first related) (if (second related) 10 5)))))))))))

(defn- simple-score
  [state x y]
  (cond
    (utils/equal? x y) (succeed state 100)
    (and (utils/lisp-atom? x) (utils/lisp-atom? y))
    (let [problem (incompatible-problem state x y)]
      (if (refused? problem)
        problem
        (if (:problem problem) (succeed problem nil) (score-classes problem x y))))
    :else (score-classes state x y)))

(defn simple-unifiable
  "A score for how readily x and y unify, or nil when they cannot.

  The score is used to count a cardinality constraint. It does not
  write the knowledge base. A string from incompatible-instances, or
  disjoint classes, is a nil score."
  [state x y]
  (simple-score state x y))

(defn- non-unifiable-pairs
  [state values]
  (loop [pairs (all-pairs values)
         state state
         acc []]
    (if (empty? pairs)
      (assoc state :value acc)
      (let [scored (simple-unifiable state (first (first pairs)) (second (first pairs)))]
        (if (refused? scored)
          scored
          (recur (rest pairs)
                 scored
                 (if (nil? (:value scored)) (conj acc (first pairs)) acc)))))))

(defn- add-to-group
  [val groups bad]
  (loop [groups groups
         acc []]
    (cond
      (empty? groups) (conj acc [val])
      (not-any? (fn [grouped]
                  (or (some #(= [val grouped] %) bad)
                      (some #(= [grouped val] %) bad)))
                (first groups))
      (into (conj acc (cons val (first groups))) (rest groups))
      :else (recur (rest groups) (conj acc (first groups))))))

(defn- group-unifiably
  [values bad]
  (loop [values (utils/elements values)
         groups []]
    (if (empty? values)
      groups
      (recur (rest values) (add-to-group (first values) groups bad)))))

(defn- violated-cardinality
  [state expr-sets constraint]
  (let [n (nth-el constraint 1)
        class (nth-el constraint 2)]
    (cond
      (nil? expr-sets) (assoc state :value nil)
      (and (term/singleton? expr-sets)
           (<= (or (length-of (term/car expr-sets)) 0) n))
      (assoc state :value nil)
      (and (utils/eql? class thing)
           (<= (or (length-of (utils/remove-duplicates
                               (drop-items (utils/append-lists expr-sets) kb/constraint-expr?)
                               :test utils/equal? :from-end? true))
                   0)
               n))
      (assoc state :value nil)
      :else
      (let [[state in-class] (loop [sets expr-sets
                                    state state
                                    acc []]
                               (if (nil? sets)
                                 [state (utils/remove-duplicates (term/build-list acc nil)
                                                                 :test utils/equal?
                                                                 :from-end? true)]
                                 (let [[state extracted] (extract-in-class state (term/car sets) class)]
                                   (recur (term/cdr sets)
                                          state
                                          (into acc (utils/elements extracted))))))]
        (cond
          (<= (or (length-of in-class) 0) n) (assoc state :value nil)
          (and (= n 0) (some? in-class)) (assoc state :value [constraint in-class])
          :else
          (let [pairs (non-unifiable-pairs state in-class)]
            (if (refused? pairs)
              pairs
              (cond
                (< (count (:value pairs)) n) (assoc pairs :value nil)
                (= n 1)
                (assoc pairs :value [constraint
                                     (utils/remove-duplicates
                                      (term/build-list (vec (mapcat identity (:value pairs))) nil)
                                      :test utils/equal? :from-end? true)])
                (> (count (group-unifiably in-class (:value pairs))) n)
                (assoc pairs :value [constraint
                                     (utils/remove-duplicates
                                      (term/build-list (vec (mapcat identity (:value pairs))) nil)
                                      :test utils/equal? :from-end? true)])
                :else (assoc pairs :value nil)))))))))

(defn- violated-set-constraints
  [state expr-sets constraints]
  (loop [constraints (drop-items constraints #(utils/eql? % :incomplete))
         state state]
    (cond
      (refused? state) state
      (nil? constraints) (assoc state :value nil)
      (not (kb/set-constraint? (term/car constraints)))
      (recur (term/cdr constraints) state)
      :else
      (let [constraint (term/car constraints)
            head (when (term/cons? constraint) (term/car constraint))]
        (cond
          (utils/eql? head (symbol "at-least")) (recur (term/cdr constraints) state)
          (#{(symbol "exactly") (symbol "at-most")} head)
          (let [hit (violated-cardinality state expr-sets constraint)]
            (if (or (refused? hit) (some? (:value hit)))
              hit
              (recur (term/cdr constraints) hit)))
          (utils/eql? head (symbol "set-constraint"))
          (let [body (subst-symbol (kb/vals-to-val (kb/valsets-to-&&-exprs expr-sets))
                                   (symbol "TheValues")
                                   (nth-el constraint 1))
                found (km state body)]
            (cond
              (refused? found) found
              (nil? (:value found))
              (assoc found :value [constraint (kb/vals-to-val (kb/valsets-to-&&-exprs expr-sets))])
              :else (recur (term/cdr constraints) found)))
          (#{(symbol "sometimes") (symbol "set-filter")} head)
          (recur (term/cdr constraints) state)
          :else (recur (term/cdr constraints) state))))))

(defn- violated-constraints
  [state vals constraints slot mode & {:keys [incomplete?]}]
  (if (nil? constraints)
    (assoc state :value nil)
    (let [vals (kb/remove-dup-instances vals)
          constraints (explain/desource-decomment constraints)
          special (special-slot (:kb state) slot)
          sets (if (= mode :satisfies)
                 (loop [constraints constraints
                        state state]
                   (cond
                     (refused? state) state
                     (nil? constraints) (assoc state :value nil)
                     (kb/set-constraint? (term/car constraints))
                     (let [hit (set-constraint-satisfied state vals (term/car constraints) incomplete?)]
                       (if (or (refused? hit) (not (:value hit)))
                         (assoc hit :value [(term/car constraints) vals])
                         (recur (term/cdr constraints) hit)))
                     :else (recur (term/cdr constraints) state)))
                 (violated-set-constraints state (term/km-list vals) constraints))]
      (cond
        (refused? sets) sets
        (some? (:value sets)) sets
        :else
        (loop [vals vals
               state sets]
          (cond
            (refused? state) state
            (nil? vals) (assoc state :value nil)
            :else
            (let [hit (violated-val state (term/car vals) constraints special mode)]
              (if (or (refused? hit) (some? (:value hit)))
                hit
                (recur (term/cdr vals) hit)))))))))

(defn test-constraints
  "Whether vals pass constraints.

  mode :consistent asks whether the values can be combined with the
  constraints. mode :satisfies asks whether they already meet them.
  :value is true or false. A refusal is returned unchanged."
  [state vals constraints km-int & {:keys [slot mode incomplete?] :or {mode :consistent}}]
  (binding [*km-int* km-int]
    (let [hit (violated-constraints state vals constraints slot mode :incomplete? incomplete?)]
      (if (refused? hit)
        hit
        (assoc hit :value (nil? (:value hit)))))))

(defn filter-using-constraints
  "vals whose members are consistent with constraints.

  A value that fails is dropped. Nothing is recorded and nothing is written."
  [state vals constraints km-int & {:keys [slot]}]
  (binding [*km-int* km-int]
    (if (nil? constraints)
      (assoc state :value vals)
      (let [special (special-slot (:kb state) slot)
            constraints (frame/dereference (:kb state) constraints)]
        (loop [vals vals
               state state
               acc []]
          (cond
            (refused? state) state
            (nil? vals) (assoc state :value (term/build-list acc nil))
            :else
            (let [hit (violated-val state (term/car vals) constraints special :consistent)]
              (cond
                (refused? hit) hit
                (some? (:value hit)) (recur (term/cdr vals) (assoc hit :value nil) acc)
                :else (recur (term/cdr vals) hit (conj acc (term/car vals)))))))))))

(defn- first-unifiable
  [state possible val n]
  (loop [possible possible
         state state
         acc []
         left n]
    (cond
      (or (nil? possible) (<= left 0)) [state (term/build-list acc nil)]
      :else
      (let [probed (km state (term/km-list val (symbol "&?") (term/car possible)))]
        (if (refused? probed)
          [probed :refused]
          (if (some? (:value probed))
            (recur (term/cdr possible) probed (conj acc (term/car possible)) (dec left))
            (recur (term/cdr possible) probed acc left)))))))

(defn- enforce-val-constraint
  [state val constraint0 special instance]
  (let [constraint (explain/desource-decomment constraint0)
        head (term/car constraint)]
    (cond
      (kb/retain-expr? constraint) (succeed state true)
      (utils/eql? head (symbol "no-inheritance")) (succeed state true)
      (utils/eql? head (symbol "must-be-a"))
      (cond
        (and (kb/kb-object? val)
             (:value (taxonomy/isa? (:kb state) val (symbol "Aggregate"))))
        (test-val-constraint state val constraint special :consistent)
        (utils/equal? constraint (term/km-list (symbol "must-be-a") thing))
        (succeed state val)
        :else
        (let [joined (km state (term/km-list val (symbol "&")
                                             (term/cons-cell (symbol "a") (term/cdr constraint))))]
          (if (refused? joined) joined (succeed joined (some? (:value joined))))))
      (utils/eql? head (symbol "mustnt-be-a"))
      (let [hit (taxonomy/isa? (:kb state) val (nth-el constraint 1))]
        (succeed (adopt state hit) (not (:value hit))))
      (utils/eql? head (symbol "<>"))
      (let [joined (km state (term/km-list val neq-slot (nth-el constraint 1)) :fail-mode :error)]
        (if (refused? joined) joined (succeed joined (some? (:value joined)))))
      (utils/eql? head (symbol "constraint"))
      (test-val-constraint state val constraint special :consistent)
      (utils/eql? head (symbol "excluded-values"))
      (test-val-constraint state val constraint special :consistent)
      (utils/eql? head (symbol "possible-values"))
      (let [found (km state (kb/vals-to-val (term/cdr constraint)))]
        (cond
          (refused? found) found
          (nil? (:value found)) (succeed found true)
          (and (= special :remove-subsumers) (kb/kb-object? instance))
          (if (utils/member? val (:value found) utils/equal?)
            (succeed found true)
            (let [[next choices] (first-unifiable found (:value found) instance 2)]
              (cond
                (refused? next) next
                (term/singleton? choices)
                (let [forced (km next (term/km-list instance (symbol "==")
                                                    (term/km-list (symbol "a") (term/car choices))))]
                  (if (refused? forced) forced (succeed forced true)))
                (some? choices) (succeed next true)
                :else (succeed next true))))
          (#{:remove-subsumers :remove-subsumees} special)
          (test-val-constraint found val constraint special :consistent)
          (utils/member? val (:value found) utils/equal?) (succeed found true)
          (term/singleton? (:value found))
          (let [forced (km found (term/km-list val (symbol "==") (term/car (:value found))))]
            (if (refused? forced) forced (succeed forced (some? (:value forced)))))
          :else
          (let [[next choices] (first-unifiable found (:value found) val 2)]
            (cond
              (refused? next) next
              (term/singleton? choices)
              (let [forced (km next (term/km-list val (symbol "==") (term/car choices)))]
                (if (refused? forced) forced (succeed forced (some? (:value forced)))))
              (some? choices) (succeed next true)
              :else (succeed next true)))))
      :else
      (-> (errors/report-error state :user-error "Unrecognized form of constraint %s"
                               (errors/format-term constraint))
          fail))))

(defn- enforce-one-val
  [state val constraints special instance slot]
  (loop [constraints constraints
         state state]
    (cond
      (refused? state) state
      (or (nil? val) (nil? constraints)) (succeed state true)
      (not (kb/val-constraint? (term/car constraints)))
      (recur (term/cdr constraints) state)
      :else
      (let [hit (enforce-val-constraint state val (term/car constraints) special instance)]
        (cond
          (refused? hit) hit
          (:value hit) (recur (term/cdr constraints) hit)
          :else
          (-> (errors/report-error hit :user-error
                                   "Constraint violation! Value %s conflicts with %s!"
                                   (errors/format-term val)
                                   (errors/format-term (term/car constraints)))
              (assoc :value false :ok false)))))))

(defn- remove-pending
  [state values]
  (loop [values values
         state state
         acc []]
    (cond
      (nil? values) (assoc state :value (term/build-list acc nil))
      (not (term/cons? values)) (assoc state :value (term/build-list acc nil))
      (loop [later (term/cdr values)]
        (cond
          (nil? later) false
          (stack/pending-equality? (:kb state) (:query state)
                                   (term/car values) (term/car later))
          true
          :else (recur (term/cdr later))))
      (recur (term/cdr values) state acc)
      :else (recur (term/cdr values) state (conj acc (term/car values))))))

(defn- enforce-set-constraint
  [state vals constraint0 target]
  (let [constraint (if (utils/eql? constraint0 :incomplete)
                     constraint0
                     (explain/desource-decomment constraint0))
        slot (nth-el target 1)
        instance (nth-el target 3)
        head (when (term/cons? constraint) (term/car constraint))
        forced (when (and (#{(symbol "at-most") (symbol "exactly")} head)
                          (= 1 (nth-el constraint 1)))
                 (nth-el constraint 2))
        [state in-class] (if forced
                           (vals-in-class state vals forced)
                           [state nil])]
    (cond
      (utils/eql? constraint :incomplete) (assoc state :value vals)
      (and forced (> (or (length-of in-class) 0) 1))
      (loop [pairs (adjacent-pairs vals)
             current state
             ok? true]
        (cond
          (refused? current) current
          (and ok? (empty? pairs))
          (let [joined (unique current (kb/vals-to-&-expr in-class) :fail-mode :error)
                rest (ordered-difference vals in-class)]
            (if (refused? joined)
              joined
              (assoc joined :value (term/cons-cell (:value joined) rest))))
          (not ok?)
          (-> (errors/report-error current :user-error
                                   "set-constraint violation!%nFound %s %s(s), but should be (%s 1 %s) and they can't be unified!%nValues were: %s."
                                   (str (or (length-of in-class) 0))
                                   (errors/format-term forced)
                                   (errors/format-term head)
                                   (errors/format-term forced)
                                   (errors/format-term vals))
              (assoc :value vals))
          :else
          (let [[a b] (first pairs)
                probed (km current (term/km-list a (symbol "&?") b))]
            (cond
              (refused? probed) probed
              (nil? (:value probed)) (recur (rest pairs) probed false)
              :else (recur (rest pairs) probed true)))))
      (utils/eql? head (symbol "sometimes"))
      ;; The Lisp returns t here, which is not a value list.
      (assoc state :value (symbol "t"))
      (utils/eql? head (symbol "set-filter"))
      ;; set-filter applies an embedded Lisp function. It is not run.
      (assoc state :value vals)
      (#{(symbol "at-least") (symbol "exactly") (symbol "at-most")} head)
      (let [n (nth-el constraint 1)
            class (nth-el constraint 2)
            [state seen] (isa-count state vals class)]
        (cond
          (and (utils/eql? head (symbol "at-least"))
               (or (> n max-padding-instances) (>= seen n)))
          (assoc state :value vals)
          (and (utils/eql? head (symbol "exactly")) (= seen n))
          (assoc state :value vals)
          (and (utils/eql? head (symbol "exactly")) (> seen n))
          (-> (errors/report-error state :user-error
                                   "set-constraint violation!%nFound %s %s(s), but should be exactly %s!%nValues were: %s."
                                   (str seen)
                                   (errors/format-term class)
                                   (str n)
                                   (errors/format-term vals))
              (assoc :value vals))
          (and (utils/eql? head (symbol "exactly")) (> n max-padding-instances))
          (assoc state :value vals)
          (and (utils/eql? head (symbol "at-most")) (<= seen n))
          (assoc state :value vals)
          (utils/eql? head (symbol "at-most"))
          (-> (errors/report-error state :user-error
                                   "set-constraint violation!%nFound %s %s(s), but should be at-most %s!%nValues were: %s."
                                   (str seen)
                                   (errors/format-term class)
                                   (str n)
                                   (errors/format-term vals))
              (assoc :value vals))
          :else (assoc state :value vals)))
      (utils/eql? head (symbol "set-constraint"))
      (let [body (subst-symbol (kb/vals-to-val vals) (symbol "TheValues") (nth-el constraint 1))
            found (km state body)]
        (cond
          (refused? found) found
          (some? (:value found)) (assoc found :value vals)
          :else
          (-> (errors/report-error found :user-error
                                   "set-constraint violation!%n%s failed test %s."
                                   (errors/format-term vals)
                                   (errors/format-term (nth-el constraint 1)))
              (assoc :value vals))))
      :else
      (-> (errors/report-error state :user-error "Unrecognized form of set constraint %s"
                               (errors/format-term constraint))
          (assoc :value vals)))))

(defn- enforce-sets
  [state vals constraints target]
  (let [pending (remove-pending state vals)]
    (loop [constraints constraints
           state pending
           vals (:value pending)]
      (cond
        (refused? state) state
        (nil? constraints) (assoc state :value vals)
        (and (not (utils/eql? (term/car constraints) :incomplete))
             (kb/val-constraint? (term/car constraints)))
        (recur (term/cdr constraints) state vals)
        :else
        (let [next (enforce-set-constraint state vals (term/car constraints) target)]
          (if (refused? next)
            next
            (recur (term/cdr constraints) next (:value next))))))))

(defn enforce-constraints
  "Apply constraints to vals and record a violation.

  Set constraints run first. A value constraint that fails is recorded.
  Violating values stay, because removal is off. at-least and exactly
  do not create fillers. :value is the values afterwards. sometimes
  returns the symbol t, matching the Lisp clause."
  [state vals constraints km-int & {:keys [target]}]
  (binding [*km-int* km-int]
    (let [slot (nth-el target 1)
          instance (nth-el target 3)
          special (special-slot (:kb state) slot)
          sets (enforce-sets state vals constraints target)]
      (cond
        (refused? sets) sets
        (utils/eql? (:value sets) (symbol "t")) sets
        :else
        (loop [vals (:value sets)
               state sets]
          (cond
            (refused? state) state
            (nil? vals)
            (assoc state :value (if remove-violating-instances? nil (:value sets)))
            :else
            (let [hit (enforce-one-val state (term/car vals) constraints special instance slot)]
              (if (refused? hit)
                hit
                (recur (term/cdr vals) hit)))))))))

(defn enforce-set-constraints
  "Apply the set constraints that force one value to be unified.

  at-most 1 and exactly 1 are applied. Other constraints wait for
  enforce-constraints. :incomplete is dropped from the values first.
  km-int is the interpreter. :value is the values afterwards."
  [state vals constraints km-int & {:keys [target]}]
  (binding [*km-int* km-int]
    (let [forced (loop [constraints constraints
                        acc []]
                   (cond
                     (nil? constraints) (term/build-list acc nil)
                     (not (term/cons? constraints)) (term/build-list acc nil)
                     :else
                     (let [constraint (term/car constraints)
                           head (when (term/cons? constraint) (term/car constraint))]
                       (recur (term/cdr constraints)
                              (if (and (contains? #{(symbol "at-most") (symbol "exactly")} head)
                                       (= 1 (nth-el constraint 1)))
                                (conj acc constraint)
                                acc)))))]
      (enforce-sets state (utils/remove-items :incomplete vals) forced target))))

;;; ----------------------------------------------------------------------
;;; Unification. The trial is a returned value. Discarding it leaves
;;; the caller's knowledge base as it was.

(defn- clean
  "Drop the keys a caller of a public entry does not receive."
  [state]
  (dissoc state :ok :problem :bindings :slots :equality-check?))

(defn- slots-of
  [state instance]
  (if-not (kb/kb-object? instance)
    [state nil]
    (let [found (frame/get-slotsvals (:kb state) instance
                                     :situation term/global-situation
                                     :dereference? false
                                     :query (:query state))]
      [(adopt state found) (:value found)])))

(defn- stored-vals
  [state frame slot]
  (if-not (and (kb/kb-object? frame) (kb/kb-object? slot))
    [state nil]
    (let [found (frame/get-vals (:kb state) frame slot
                                :situation term/global-situation
                                :dereference? false
                                :query (:query state))]
      [(adopt state found) (:value found)])))

(defn- slot-names
  [slotsvals]
  (loop [slotsvals slotsvals
         acc []]
    (cond
      (nil? slotsvals) acc
      (not (term/cons? slotsvals)) acc
      :else (recur (term/cdr slotsvals)
                   (conj acc (frame/slot-in (term/car slotsvals)))))))

(defn- find-pair
  [slotsvals slot]
  (loop [slotsvals slotsvals]
    (cond
      (nil? slotsvals) nil
      (not (term/cons? slotsvals)) nil
      (utils/eql? slot (frame/slot-in (term/car slotsvals))) (term/car slotsvals)
      :else (recur (term/cdr slotsvals)))))

(defn- drop-pair
  [slotsvals slot]
  (loop [slotsvals slotsvals
         acc []]
    (cond
      (nil? slotsvals) (term/build-list acc nil)
      (not (term/cons? slotsvals)) slotsvals
      (utils/eql? slot (frame/slot-in (term/car slotsvals)))
      (recur (term/cdr slotsvals) acc)
      :else (recur (term/cdr slotsvals) (conj acc (term/car slotsvals))))))

(defn- every-isa?
  [state instance classes]
  (loop [classes classes
         state state]
    (cond
      (or (nil? classes) (not (term/cons? classes))) [state true]
      :else
      (let [hit (taxonomy/isa? (:kb state) instance (term/car classes))]
        (if (:value hit)
          (recur (term/cdr classes) (adopt state hit))
          [(adopt state hit) false])))))

(defn- subsumes-instance?
  [state left right & {:keys [proper?]}]
  (let [hit (taxonomy/classes-subsume-instance? (:kb state) left right :proper? proper?)]
    (assoc (adopt state hit) :value (:value hit) :ok (boolean (:value hit)))))

(defn- fail-unify
  "Record the generic failure once. A specific problem already recorded
  is left as the only sentence."
  [state left right eagerly? classes-subsumep fail-mode]
  (let [state (fail state)]
    (if (and (= fail-mode :error) (not (:unification-reported state)))
      (report-unification state "Unification (%s %s %s) failed!"
                          (errors/format-term left)
                          (errors/format-term (operator eagerly? classes-subsumep))
                          (errors/format-term right))
      state)))

(defn- apply-binding
  [state pair]
  (let [from (frame/dereference (:kb state) (first pair))
        to (second pair)]
    (if-not (kb/kb-object? from)
      state
      (adopt state (frame/km-bind (:kb state) from to :query (:query state))))))

(defn- write-slots
  "Replace the survivor's global slots with the unified list.

  A slot that is absent from that list is removed. A survivor that is
  not a frame is left unchanged. Other situations are not merged."
  [state survivor slotsvals]
  (if-not (kb/kb-object? survivor)
    state
    (let [[state existing] (slots-of state survivor)
          kept (set (slot-names slotsvals))
          state (loop [slotsvals slotsvals
                       state state]
                  (if (or (nil? slotsvals) (not (term/cons? slotsvals)))
                    state
                    (let [pair (term/car slotsvals)
                          written (frame/put-vals (:kb state) survivor
                                                  (frame/slot-in pair)
                                                  (frame/vals-in pair)
                                                  :situation term/global-situation
                                                  :query (:query state))]
                      (recur (term/cdr slotsvals) (adopt state written)))))]
      (loop [names (slot-names existing)
             state state]
        (if (empty? names)
          state
          (if (contains? kept (first names))
            (recur (rest names) state)
            (let [cleared (frame/put-vals (:kb state) survivor (first names) nil
                                          :situation term/global-situation
                                          :query (:query state))]
              (recur (rest names) (adopt state cleared)))))))))

(defn- neq-vals
  "Ground /== values. A non-ground expression is not evaluated again."
  [state instance]
  (if-not (and (frame/are-some? (:kb state) :constraints) (kb/kb-object? instance))
    [state nil]
    (stored-vals state instance neq-slot)))

(defn- without-self
  [state instance values]
  (if (utils/member? instance values utils/equal?)
    [(errors/report-error state :user-warning
                          "Error in the KB: %s declared as not equal to %s. Ignoring that declaration..."
                          (errors/format-term instance)
                          (errors/format-term instance))
     (drop-items values #(utils/equal? % instance))]
    [state values]))

(defn- neq-problem
  [state owner values other]
  (cond
    (utils/member? other values utils/equal?)
    (str (errors/format-term owner) " has a constraint /== "
         (errors/format-term other) " on it.")
    :else
    (loop [values values]
      (cond
        (or (nil? values) (not (term/cons? values))) nil
        (stack/pending-equality? (:kb state) (:query state) other (term/car values))
        (str (errors/format-term owner) " has a constraint /== "
             (errors/format-term (term/car values))
             " on it, and (" (errors/format-term (term/car values))
             " & " (errors/format-term other)
             ") is pending (higher up the goal stack)")
        :else (recur (term/cdr values))))))

(defn- number-bound
  "A stored > or < that rules number out, or nil when the slot is empty.

  The slot is read only when a value is already stored."
  [state number instance op test]
  (let [[state stored] (stored-vals state instance op)]
    (if (nil? stored)
      [state nil]
      (let [found (km state (term/km-list (symbol "the") op (symbol "of") instance))]
        (cond
          (refused? found) [found :refused]
          (some #(and (number? %) (test number %)) (utils/elements (:value found)))
          [found (str (errors/format-term instance) " has a constraint "
                      (errors/format-term op) " "
                      (errors/format-term (:value found)) " on it.")]
          :else [found nil])))))

(defn check-slotvals
  "Whether the values already in hand are consistent.

  Inherited values are not read. A single-valued slot is also tested
  against (exactly 1 Thing). fail-mode :fail is silent. fail-mode :error
  records the constraint and continues, so a forced unification can
  still combine the values. :value is true or false."
  [state slot i1 i2 exprs1 exprs2 & {:keys [cs1 cs2 classes-subsumep eagerly? fail-mode]
                                     :or {fail-mode :fail}}]
  (let [_ [classes-subsumep eagerly?]]
    (cond
      (and eagerly? (= fail-mode :fail))
      (-> (errors/report-error state :program-error
                               "Calling check-slotvals-constraints0 with :eagerlyp t and :fail-mode 'fail (not allowed!)")
          fail)
      (and (some? i1) (utils/equal? (frame/dereference (:kb state) i1)
                                    (frame/dereference (:kb state) i2)))
      (succeed state true)
      (utils/eql? slot neq-slot)
      (succeed state true)
      :else
      (let [[state i1-ok] (if (and i1 (nil? i2) (nil? exprs2))
                            (every-isa? state i1 cs2)
                            [state false])
            [state i2-ok] (if (and (not i1-ok) i2 (nil? i1) (nil? exprs1))
                            (every-isa? state i2 cs1)
                            [state false])]
        (if (or i1-ok i2-ok)
          (succeed state true)
          (let [c1 (constraint-walk exprs1 :plural)
                c2 (constraint-walk exprs2 :plural)
                combined (utils/remove-duplicates
                          (utils/append-lists (term/km-list c1 c2))
                          :test utils/equal? :from-end? true)
                combined (if (and (kb/kb-object? slot)
                                  (frame/single-valued-slot? (:kb state) slot))
                           (utils/remove-duplicates
                            (term/cons-cell exactly-one-thing combined)
                            :test utils/equal? :from-end? true)
                           combined)
                vs1 (remove-constraints (:kb state) exprs1)
                vs2 (remove-constraints (:kb state) exprs2)
                sets (term/build-list (vec (remove nil? [vs1 vs2])) nil)
                left (violated-constraints state vs1 (ordered-difference c2 c1) slot :consistent)
                right (if (or (refused? left) (some? (:value left)))
                        left
                        (violated-constraints left vs2 (ordered-difference c1 c2) slot :consistent))
                hit (if (or (refused? right) (some? (:value right)))
                      right
                      (violated-set-constraints right sets combined))]
            (cond
              (refused? hit) hit
              (nil? (:value hit)) (succeed hit true)
              (= fail-mode :error)
              (-> (report-unification hit
                                      "Unification (%s %s %s) failed!%n  Constraint %s violated by value(s) %s on slot '%s'."
                                      (errors/format-term (or i1 (term/km-list (symbol "a"))))
                                      (errors/format-term (operator eagerly? classes-subsumep))
                                      (errors/format-term (or i2 (term/km-list (symbol "a"))))
                                      (errors/format-term (first (:value hit)))
                                      (errors/format-term (second (:value hit)))
                                      (errors/format-term slot))
                  (assoc :ok false :value false))
              :else (assoc hit :ok false :value false))))))))

(defn- incompatible-problem
  "A sentence describing why left and right cannot unify, or nil.

  The sentence is not recorded here. /== is read from the store and is
  not evaluated again. The == check is skipped while that check is
  already on the stack."
  [state left right]
  (let [left (frame/dereference (:kb state) left)
        right (frame/dereference (:kb state) right)]
    (cond
      (utils/equal? left right) (assoc state :problem nil)
      (and (frame/named-instance? (:kb state) left)
           (frame/named-instance? (:kb state) right)
           (not (utils/eql? left right)))
      (assoc state :problem
             (cond
               (and (string? left) (string? right)) "These are different strings!"
               (and (number? left) (number? right)) "These are different numbers!"
               :else "These are different objects!"))
      (frame/class? (:kb state) left)
      (let [hit (taxonomy/isa? (:kb state) right (symbol "Class"))]
        (assoc (adopt state hit) :problem
               (when-not (:value hit)
                 (str (errors/format-term left) " is a class, but "
                      (errors/format-term right) " isn't"))))
      (frame/class? (:kb state) right)
      (let [hit (taxonomy/isa? (:kb state) left (symbol "Class"))]
        (assoc (adopt state hit) :problem
               (when-not (:value hit)
                 (str (errors/format-term right) " is a class, but "
                      (errors/format-term left) " isn't"))))
      (not (frame/are-some? (:kb state) :constraints))
      (assoc state :problem nil)
      :else
      (let [[state left-neqs] (neq-vals state left)
            [state right-neqs] (neq-vals state right)
            [state left-neqs] (without-self state left left-neqs)
            [state right-neqs] (without-self state right right-neqs)
            text (or (neq-problem state left left-neqs right)
                     (neq-problem state right right-neqs left))]
        (cond
          (some? text) (assoc state :problem text)
          (and (number? left) (kb/kb-object? right))
          (let [[state text] (number-bound state left right (symbol ">") <=)]
            (if (or (= text :refused) (some? text))
              (if (= text :refused) state (assoc state :problem text))
              (let [[state text] (number-bound state left right (symbol "<") >=)]
                (assoc state :problem (when (not= text :refused) text)))))
          (and (number? right) (kb/kb-object? left))
          (let [[state text] (number-bound state right left (symbol ">") <=)]
            (if (or (= text :refused) (some? text))
              (if (= text :refused) state (assoc state :problem text))
              (let [[state text] (number-bound state right left (symbol "<") >=)]
                (assoc state :problem (when (not= text :refused) text)))))
          (:equality-check? state) (assoc state :problem nil)
          :else
          (let [[state eq1] (stored-vals state left (symbol "=="))
                [state eq2] (stored-vals state right (symbol "=="))]
            (if (and (nil? eq1) (nil? eq2))
              (assoc state :problem nil)
              (let [checked (check-slotvals (assoc state :equality-check? true)
                                            (symbol "==") left right eq1 eq2
                                            :fail-mode :fail)]
                (if (refused? checked)
                  checked
                  (assoc checked :problem
                         (when-not (:value checked)
                           (str "Some equality constraint violation ("
                                (errors/format-term left) " == "
                                (errors/format-term eq1) ", "
                                (errors/format-term right) " == "
                                (errors/format-term eq2) ")"))))))))))))

(defn- class-failure
  [state left right expr eagerly? classes-subsumep fit]
  (let [op (operator eagerly? classes-subsumep)
        partitions (:partitions fit)
        locked (:locked fit)]
    (cond
      (some? partitions)
      (report-unification state
                          "Unification (%s %s %s) failed! The classes were found to be incompatible.%nPartition(s) %s was violated:%n%s"
                          (errors/format-term left) (errors/format-term op) (errors/format-term right)
                          (errors/format-term partitions) (errors/format-term partitions))
      (some? locked)
      (report-unification state
                          "Unification (%s %s %s) failed! The unification would replace the locked class %s with %s. (not allowed!)"
                          (errors/format-term left) (errors/format-term op) (errors/format-term right)
                          (errors/format-term (first locked)) (errors/format-term (second locked)))
      :else
      (report-unification state
                          "Unification (%s %s %s) failed! The classes were found to be incompatible."
                          (errors/format-term left) (errors/format-term op) (errors/format-term expr)))))

(defn- unify-names
  "The survivor and one binding, or a failure.

  Two named instances are rejected by incompatible-instances. An
  anonymous instance unifies with a non-frame only when the anonymous
  instance's classes subsume that value, and that test does not fall
  through. A named instance on the right wins. Equal classes keep the
  left instance. Fluent instances are not a separate case."
  [state left right & {:keys [classes-subsumep eagerly? fail-mode] :or {fail-mode :fail}}]
  (let [left (frame/dereference (:kb state) left)
        right (frame/dereference (:kb state) right)]
    (cond
      (utils/eql? left right) (assoc (succeed state left) :bindings nil)
      :else
      (let [problem (incompatible-problem state left right)]
        (cond
          (refused? problem) problem
          (:problem problem)
          (if (= fail-mode :error)
            (-> (report-unification problem
                                    "Unification (%s %s %s) failed!%n       Problem was: %s"
                                    (errors/format-term left)
                                    (errors/format-term (operator eagerly? classes-subsumep))
                                    (errors/format-term right)
                                    (:problem problem))
                fail)
            (fail problem))
          (and (not (kb/kb-object? left)) (frame/anonymous-instance? (:kb problem) right))
          (let [fit (subsumes-instance? problem right left)]
            (if (:value fit)
              (assoc (succeed fit left) :bindings [[right left]])
              (fail fit)))
          (and (not (kb/kb-object? right)) (frame/anonymous-instance? (:kb problem) left))
          (let [fit (subsumes-instance? problem left right)]
            (if (:value fit)
              (assoc (succeed fit right) :bindings [[left right]])
              (fail fit)))
          :else
          (let [fit (taxonomy/compatible-classes? (:kb problem)
                                                  :instance1 left
                                                  :instance2 right
                                                  :classes-subsumep classes-subsumep
                                                  :check-locked? classes-subsumep)
                state (adopt problem fit)]
            (if (:value fit)
              (let [proper (subsumes-instance? state left right :proper? true)]
                (if (or (frame/named-instance? (:kb proper) right)
                        (and (not (frame/named-instance? (:kb proper) left))
                             (:value proper)))
                  (assoc (succeed proper right) :bindings [[left right]])
                  (assoc (succeed proper left) :bindings [[right left]])))
              (if (= fail-mode :error)
                (fail (class-failure state left right right eagerly? classes-subsumep fit))
                (fail state)))))))))

(defn- and-append
  "One expression joining the two value lists. The common cases are a
  value pair and a set pair."
  [xs op ys]
  (cond
    (utils/equal? xs ys) xs
    (kb/set-unification-operator? op) (term/km-list (term/km-list xs op ys))
    (kb/val-unification-operator? op)
    (term/km-list (term/km-list (term/car xs) op (term/car ys)))
    :else xs))

(defn- reattach-constraints
  [new-vals constraints]
  (kb/val-to-vals
   (kb/vals-to-&-expr
    (utils/remove-duplicates
     (utils/append-lists (term/km-list new-vals constraints))
     :test utils/equal?))))

(declare lazy-unify)

(defn- lazy-unify-vals
  "The combined values of one slot. :ok is false when they cannot combine.

  A single-valued pair that can combine and is not eager becomes
  (_A & _B). &! evaluates that pair. A multivalued lazy pair becomes
  a && residue. Inheritance of constraints is not applied."
  [state slot i1 i2 vs1 vs2 & {:keys [classes-subsumep eagerly? target]}]
  (cond
    (nil? vs2) (succeed state vs1)
    (nil? vs1) (succeed state vs2)
    (kb/km-equal? vs1 vs2) (succeed state vs1)
    (subbag? vs1 vs2) (succeed state vs2)
    (subbag? vs2 vs1) (succeed state vs1)
    (frame/remove-subsumers-slot? (:kb state) slot)
    (let [hit (taxonomy/remove-subsumers (:kb state) (utils/append-lists (term/km-list vs1 vs2)))]
      (succeed (adopt state hit) (:value hit)))
    (frame/remove-subsumees-slot? (:kb state) slot)
    (let [hit (taxonomy/remove-subsumees (:kb state) (utils/append-lists (term/km-list vs1 vs2)))]
      (succeed (adopt state hit) (:value hit)))
    (or (frame/appending-slot? (:kb state) slot) (utils/eql? slot neq-slot))
    (succeed state (kb/remove-dup-instances (utils/append-lists (term/km-list vs1 vs2))))
    (and (inherit-overrides? (:kb state) slot)
         (not (any-anonymous? (:kb state) vs1))
         (not (any-anonymous? (:kb state) vs2)))
    (let [kept (remove-constraints (:kb state) vs1)
          constraints (constraint-walk vs1 :plural)
          found (km state (kb/vals-to-val kept) :target target)]
      (if (refused? found)
        found
        (succeed found (utils/append-lists (term/km-list (:value found) constraints)))))
    (frame/single-valued-slot? (:kb state) slot)
    (let [state (if (and (term/singleton? vs1) (term/singleton? vs2))
                  state
                  (errors/report-error state :user-warning
                                       "A single-valued slot has multiple values!%nDoing unification (%s & %s)%nContinuing, assuming all these values should be unified together..."
                                       (errors/format-term vs1)
                                       (errors/format-term vs2)))
          probe-op (if classes-subsumep (symbol "&+?") (symbol "&?"))
          probed (km state (term/km-list (term/car vs1) probe-op (term/car vs2)) :target target)]
      (cond
        (refused? probed) probed
        (nil? (:value probed)) (fail probed)
        eagerly?
        (let [expr (kb/vals-to-val (and-append (term/km-list (term/car vs1))
                                               (symbol "&!")
                                               (term/km-list (term/car vs2))))
              found (km probed expr :fail-mode :error :target target)
              constraints (utils/append-lists
                           (term/km-list (constraint-walk vs1 :plural)
                                         (constraint-walk vs2 :plural)))]
          (if (refused? found)
            found
            (succeed found (reattach-constraints (:value found) constraints))))
        :else
        (succeed probed
                 (kb/val-to-vals
                  (kb/vals-to-&-expr
                   (utils/remove-duplicates
                    (utils/append-lists (term/km-list (kb/un-andify vs1) (kb/un-andify vs2)))
                    :test utils/equal?))))))
    eagerly?
    (let [expr (kb/vals-to-val (and-append vs1 (symbol "&&!") vs2))
          found (km state expr :fail-mode :error :target target)
          constraints (utils/remove-duplicates
                       (utils/append-lists
                        (term/km-list (constraint-walk vs1 :plural)
                                      (constraint-walk vs2 :plural)))
                       :test utils/equal? :from-end? true)]
      (cond
        (refused? found) found
        (nil? constraints) (succeed found (:value found))
        :else
        (let [checked (test-constraints found (:value found) constraints *km-int*
                                        :slot slot :mode :consistent)]
          (if (or (refused? checked) (:value checked))
            (let [enforced (enforce-constraints checked (:value found) constraints *km-int*
                                                :target (or target
                                                            (term/km-list (symbol "the") slot
                                                                          (symbol "of") i1)))]
              (if (refused? enforced)
                enforced
                (succeed enforced (utils/append-lists
                                   (term/km-list (:value enforced) constraints)))))
            (let [violated (violated-constraints checked (:value found) constraints slot :consistent)]
              (-> (report-unification violated
                                      "Unification (%s %s %s) failed on slot %s with combined values %s:%nConstraint %s was violated by value(s) %s."
                                      (errors/format-term i1)
                                      (errors/format-term (operator true classes-subsumep))
                                      (errors/format-term i2)
                                      (errors/format-term slot)
                                      (errors/format-term (:value found))
                                      (errors/format-term (first (:value violated)))
                                      (errors/format-term (second (:value violated))))
                  fail))))))
    :else
    (succeed state
             (kb/valsets-to-&&-exprs
              (utils/remove-duplicates
               (utils/append-lists (term/km-list (kb/&&-exprs-to-valsets vs1)
                                                 (kb/&&-exprs-to-valsets vs2)))
               :test utils/equal?
               :from-end? true)))))

(defn- lazy-unify-slotsvals
  [state i1 i2 svs1 svs2 & {:keys [cs1 cs2 classes-subsumep eagerly? check-constraints? fail-mode target]
                            :or {check-constraints? true fail-mode :fail}}]
  (loop [svs1 svs1
         svs2 svs2
         state state
         acc []]
    (if (and (nil? svs1) (nil? svs2))
      (assoc (succeed state (term/build-list acc nil)) :slots (term/build-list acc nil))
      (let [sv1 (when (term/cons? svs1) (term/car svs1))
            slot (or (when sv1 (frame/slot-in sv1))
                     (frame/slot-in (term/car svs2)))
            exprs1 (frame/vals-in sv1)
            exprs2 (frame/vals-in (find-pair svs2 slot))
            rest1 (when (term/cons? svs1) (term/cdr svs1))
            rest2 (drop-pair svs2 slot)]
        (if (and (nil? exprs1) (nil? exprs2))
          (recur rest1 rest2 state acc)
          (let [overrides? (and (inherit-overrides? (:kb state) slot)
                                (not (any-anonymous? (:kb state) exprs1))
                                (not (any-anonymous? (:kb state) exprs2)))
                checked (cond
                          (or (not check-constraints?) overrides?) (succeed state true)
                          :else (check-slotvals state slot i1 i2 exprs1 exprs2
                                                :cs1 cs1 :cs2 cs2
                                                :classes-subsumep classes-subsumep
                                                :eagerly? eagerly?
                                                :fail-mode fail-mode))
                continue? (or (refused? checked)
                              (:value checked)
                              (not= fail-mode :fail))]
            (cond
              (refused? checked) checked
              (not continue?) (fail checked)
              :else
              (let [unified (lazy-unify-vals checked slot i1 i2 exprs1 exprs2
                                             :classes-subsumep classes-subsumep
                                             :eagerly? eagerly?
                                             :target target)]
                (cond
                  (refused? unified) unified
                  (not (:ok unified)) (fail unified)
                  :else
                  (recur rest1 rest2 unified
                         (if (some? (:value unified))
                           (conj acc (frame/make-slotvals slot (:value unified)))
                           acc)))))))))))

(defn- unified-slots
  "The merged global slots, or a failure. One side with no slots copies
  the other. Situations other than *Global are not visited."
  [state i1 i2 & {:keys [cs1 cs2 classes-subsumep eagerly? check-constraints? fail-mode target]
                  :or {check-constraints? true fail-mode :fail}}]
  (let [[state s1] (slots-of state i1)
        [state s2] (slots-of state i2)]
    (cond
      (and (nil? s1) (nil? s2)) (assoc (succeed state nil) :slots nil)
      (or (nil? s1) (nil? s2))
      (let [copied (or s1 s2)]
        (assoc (succeed state copied) :slots copied))
      :else
      (lazy-unify-slotsvals state i1 i2 s1 s2
                            :cs1 cs1 :cs2 cs2
                            :classes-subsumep classes-subsumep
                            :eagerly? eagerly?
                            :check-constraints? check-constraints?
                            :fail-mode fail-mode
                            :target target))))

(defn- try2
  "The unification that would be committed, without writing it.

  :value is the survivor. :slots is the merged slot list. :bindings
  is the list of pairs to bind. :ok is false when it cannot be done."
  [state left right & {:keys [classes-subsumep eagerly? check-constraints? fail-mode target]
                       :or {check-constraints? true fail-mode :fail}}]
  (if (and (= fail-mode :fail) eagerly?)
    (-> (errors/report-error state :program-error
                             "try-lazy-unify2: :fail-mode 'fail and :eagerlyp t can't both be set at the same time!")
        fail)
    (let [named (unify-names state left right
                             :classes-subsumep classes-subsumep
                             :eagerly? eagerly?
                             :fail-mode fail-mode)]
      (if-not (:ok named)
        named
        (let [slots (unified-slots named left right
                                   :classes-subsumep classes-subsumep
                                   :eagerly? eagerly?
                                   :check-constraints? check-constraints?
                                   :fail-mode fail-mode
                                   :target target)]
          (if-not (:ok slots)
            slots
            (let [again (unify-names slots left right
                                     :classes-subsumep classes-subsumep
                                     :eagerly? eagerly?
                                     :fail-mode fail-mode)]
              (if (:ok again)
                (assoc again
                       :value (:value named)
                       :slots (:slots slots)
                       :bindings (:bindings named))
                again))))))))

(defn- lazy-unify
  "Unify two values and keep the result.

  Bindings are written first, then the merged slots. A failure leaves
  the returned state uncommitted: the caller rolls it back. A second
  generic failure sentence is not added when a specific one was recorded."
  [state left right & {:keys [classes-subsumep eagerly? check-constraints? fail-mode target]
                       :or {check-constraints? true fail-mode :fail}}]
  (let [left (frame/dereference (:kb state) left)
        right (frame/dereference (:kb state) right)]
    (cond
      (utils/equal? left right) (succeed state left)
      (nil? left) (succeed state right)
      (nil? right) (succeed state left)
      :else
      (let [trial (try2 state left right
                        :classes-subsumep classes-subsumep
                        :eagerly? eagerly?
                        :check-constraints? check-constraints?
                        :fail-mode fail-mode
                        :target target)]
        (if-not (:ok trial)
          (fail-unify trial left right eagerly? classes-subsumep fail-mode)
          (let [bound (reduce apply-binding trial (or (:bindings trial) []))
                written (write-slots bound (:value trial) (:slots trial))
                written (update-in written [:query :unifications] (fnil inc 0))]
            (succeed written (:value trial))))))))

(declare probe)

(defn- probe-structured
  [state left right classes-subsumep check-constraints?]
  (let [left (explain/desource left)
        right (explain/desource right)]
    (cond
      (or (not (term/structured-list? left)) (not (term/structured-list? right)))
      (let [named (unify-names state left right
                               :classes-subsumep classes-subsumep
                               :fail-mode :fail)]
        (if (:ok named) named (fail named)))
      (and (utils/eql? (term/car left) (term/car right))
           (not (utils/eql? (term/car left) :triple)))
      (loop [left (term/cdr left)
             right (term/cdr right)
             state state]
        (cond
          (and (nil? left) (nil? right)) (succeed state true)
          (or (nil? left) (nil? right) (not (term/cons? left)) (not (term/cons? right)))
          (fail state)
          :else
          (let [hit (probe state (term/car left) (term/car right)
                          :classes-subsumep classes-subsumep
                          :check-constraints? check-constraints?)]
            (if (or (refused? hit) (not (:ok hit)))
              (fail hit)
              (recur (term/cdr left) (term/cdr right) hit)))))
      :else (fail state))))

(defn- probe
  "Whether left and right can unify. Nothing is written.

  A :set succeeds without looking inside. 1 and 1.0 succeed here,
  because this test uses km-equal. The committing unify uses equal
  and treats them as different numbers."
  [state left right & {:keys [classes-subsumep check-constraints?] :or {check-constraints? true}}]
  (let [left (frame/dereference (:kb state) left)
        right (frame/dereference (:kb state) right)]
    (cond
      (kb/km-equal? left right) (succeed state left)
      (nil? left) (succeed state right)
      (nil? right) (succeed state left)
      (and (kb/km-triple? left) (kb/km-triple? right)) (fail state)
      (or (kb/km-set? left) (kb/km-set? right)) (succeed state (or left right))
      (or (term/structured-list? left) (term/structured-list? right))
      (probe-structured state left right classes-subsumep check-constraints?)
      :else
      (try2 state left right
            :classes-subsumep classes-subsumep
            :check-constraints? check-constraints?
            :fail-mode :fail))))

(defn try-lazy-unify
  "Whether left and right can unify.

  The returned knowledge base and query are the ones passed in. Errors
  from the trial are kept. :value is (t) or nil. eagerly is ignored:
  a test must not write."
  [state left right km-int & {:keys [classes-subsumep check-constraints?]
                              :or {check-constraints? true}}]
  (binding [*km-int* km-int]
    (let [trial (probe state left right
                       :classes-subsumep classes-subsumep
                       :check-constraints? check-constraints?)]
      (if (refused? trial)
        trial
        (clean
         (assoc state
                :errors (vec (or (:errors trial) []))
                :warnings (vec (or (:warnings trial) []))
                :error-structures (vec (or (:error-structures trial) []))
                :unification-reported (:unification-reported trial)
                :value (when (:ok trial) (term/km-list (symbol "t")))))))))

(defn- bad-existential
  [state expr fail-mode]
  (if (= fail-mode :error)
    (fail (errors/report-error state :user-error
                               "Bad expression in subsumption testing %s%n(Should be one of (a ?class) or (a ?class with &rest))."
                               (errors/format-term expr)))
    (fail state)))

(defn- breakup
  "The class and the slot pairs of a local existential expression.

  (a Class) and (a Class with slots) are accepted. called and
  uniquely-called of length 4, and those forms with slots, are slot
  pairs too. :value is (class slots) or nil."
  [state expr fail-mode]
  (let [expr (explain/desource-decomment-top-level expr)
        n (length-of expr)
        head (when (term/cons? expr) (term/car expr))]
    (if-not (and (#{(symbol "a") (symbol "some")} head) n (>= n 2))
      (bad-existential state expr fail-mode)
      (cond
        (term/pair? expr)
        (succeed state (term/km-list (nth-el expr 1) nil))
        (utils/eql? (nth-el expr 2) (symbol "with"))
        (succeed state (term/km-list (nth-el expr 1) (term/cdr (term/cdr (term/cdr expr)))))
        (and (utils/eql? (nth-el expr 2) (symbol "called")) (= n 4))
        (succeed state (term/km-list (nth-el expr 1)
                                     (term/km-list (term/km-list (symbol "called")
                                                                 (term/km-list (nth-el expr 3))))))
        (and (utils/eql? (nth-el expr 2) (symbol "uniquely-called")) (= n 4))
        (succeed state (term/km-list (nth-el expr 1)
                                     (term/km-list (term/km-list (symbol "uniquely-called")
                                                                 (term/km-list (nth-el expr 3))))))
        (and (utils/eql? (nth-el expr 2) (symbol "called"))
             (utils/eql? (nth-el expr 4) (symbol "with")))
        (succeed state (term/km-list (nth-el expr 1)
                                     (term/cons-cell (term/km-list (symbol "called")
                                                                   (term/km-list (nth-el expr 3)))
                                                     (term/cdr (term/cdr (term/cdr (term/cdr (term/cdr expr))))))))
        (and (utils/eql? (nth-el expr 2) (symbol "uniquely-called"))
             (utils/eql? (nth-el expr 4) (symbol "with")))
        (succeed state (term/km-list (nth-el expr 1)
                                     (term/cons-cell (term/km-list (symbol "uniquely-called")
                                                                   (term/km-list (nth-el expr 3)))
                                                     (term/cdr (term/cdr (term/cdr (term/cdr (term/cdr expr))))))))
        :else (bad-existential state expr fail-mode)))))

(defn- existential-classes
  [class slotsvals]
  (utils/remove-duplicates
   (term/cons-cell class (frame/vals-in (find-pair slotsvals (symbol "instance-of"))))
   :test utils/eql?
   :from-end? true))

(defn- put-unified-slots
  [state instance slotsvals]
  (loop [slotsvals slotsvals
         state state
         changed? false]
    (if (or (nil? slotsvals) (not (term/cons? slotsvals)))
      [state changed?]
      (let [pair (term/car slotsvals)
            current (frame/get-vals (:kb state) instance (frame/slot-in pair)
                                    :situation term/global-situation
                                    :dereference? false
                                    :query (:query state))
            state (adopt state current)]
        (if (utils/equal? (:value current) (frame/vals-in pair))
          (recur (term/cdr slotsvals) state changed?)
          (let [written (frame/put-vals (:kb state) instance (frame/slot-in pair)
                                        (frame/vals-in pair)
                                        :situation term/global-situation
                                        :query (:query state))]
            (recur (term/cdr slotsvals) (adopt state written) true)))))))

(defn- unify-existential
  "Unify instance with an existential expression.

  commit? false only tests. A successful test does not write. No Skolem
  is created. Explanations are not recorded."
  [state instance expr & {:keys [classes-subsumep eagerly? fail-mode commit? target]
                          :or {fail-mode :fail commit? true}}]
  (let [_ target
        broken (breakup state expr fail-mode)]
    (if (or (refused? broken) (nil? (:value broken)))
      (if (and commit? (= fail-mode :error) (not (:unification-reported broken))
               (not (refused? broken)))
        broken
        (fail broken))
      (let [class (term/car (:value broken))
            slots0 (frame/bind-self (nth-el (:value broken) 1) instance)
            classes (existential-classes class slots0)
            isa (taxonomy/isa? (:kb broken) instance class)
            state (adopt broken isa)]
        (cond
          (and (nil? slots0)
               (:value isa)
               (frame/remove-subsumers-slot? (:kb state) (symbol "instance-of")))
          (succeed state instance)
          :else
          (let [fit (taxonomy/compatible-classes? (:kb state)
                                                  :instance1 instance
                                                  :classes2 (term/km-list class)
                                                  :classes-subsumep classes-subsumep
                                                  :check-locked? classes-subsumep)
                state (adopt state fit)]
            (cond
              (not (:value fit))
              (if (and commit? (= fail-mode :error))
                (fail (class-failure state instance expr expr eagerly? classes-subsumep fit))
                (fail state))
              (not (kb/kb-object? instance))
              (succeed state instance)
              :else
              (let [slotsvals (let [updated (term/km-list (symbol "instance-of") classes)]
                                (if (find-pair slots0 (symbol "instance-of"))
                                  (loop [rest slots0
                                         acc []]
                                    (cond
                                      (nil? rest) (term/build-list acc nil)
                                      (utils/eql? (frame/slot-in (term/car rest)) (symbol "instance-of"))
                                      (recur (term/cdr rest) (conj acc updated))
                                      :else (recur (term/cdr rest) (conj acc (term/car rest)))))
                                  (term/cons-cell updated slots0)))
                    [state own] (slots-of state instance)
                    merged (lazy-unify-slotsvals state instance nil own slotsvals
                                                 :cs2 (keep-items classes kb/kb-object?)
                                                 :classes-subsumep classes-subsumep
                                                 :eagerly? eagerly?
                                                 :fail-mode (if commit? fail-mode :fail))]
                (cond
                  (refused? merged) merged
                  (not (:ok merged))
                  (if (and commit? (= fail-mode :error))
                    (fail-unify merged instance expr eagerly? classes-subsumep fail-mode)
                    (fail merged))
                  (not commit?) (succeed merged instance)
                  :else
                  (let [[written _] (put-unified-slots merged instance (:slots merged))]
                    (succeed written instance)))))))))))

(declare unify-pair)

(defn- elements-unifiable?
  [state left right classes-subsumep]
  (loop [left left
         right right
         state state]
    (cond
      (and (nil? left) (nil? right)) (succeed state true)
      (or (nil? left) (nil? right) (not (term/cons? left)) (not (term/cons? right)))
      (fail state)
      (or (kb/km-set? (term/car left)) (kb/km-set? (term/car right)))
      (recur (term/cdr left) (term/cdr right) state)
      :else
      (let [op (if classes-subsumep (symbol "&+?") (symbol "&?"))
            probed (km state (term/km-list (term/car left) op (term/car right)))]
        (cond
          (refused? probed) probed
          (nil? (:value probed)) (fail probed)
          :else (recur (term/cdr left) (term/cdr right) probed))))))

(defn- unify-structured
  [state left right & {:keys [classes-subsumep eagerly? fail-mode]}]
  (let [left (explain/desource-decomment-top-level left)
        right (explain/desource-decomment-top-level right)]
    (if-not (and (term/cons? left) (term/cons? right)
                 (utils/eql? (term/car left) (term/car right)))
      (fail state)
      (let [ready (elements-unifiable? state (term/cdr left) (term/cdr right) classes-subsumep)]
        (if (or (refused? ready) (not (:ok ready)))
          (fail ready)
          (loop [left (term/cdr left)
                 right (term/cdr right)
                 state ready
                 acc [(term/car left)]]
            (cond
              (and (nil? left) (nil? right))
              (succeed state (term/build-list acc nil))
              (or (nil? left) (nil? right))
              (-> (errors/report-error state :nodebugger-error
                                       "Yikes! I partly unified two sequences %s and %s but then found they couldn't be unified!%nI'll continue and hope for the best (sorry!)..."
                                       (errors/format-term left)
                                       (errors/format-term right))
                  (assoc :ok false :value nil))
              :else
              (let [one (term/car left)
                    two (term/car right)
                    hit (if (or (kb/km-set? one) (kb/km-set? two))
                          (fail state)
                          (unify-pair state one two
                                            :classes-subsumep classes-subsumep
                                            :eagerly? eagerly?
                                            :fail-mode fail-mode))]
                (if (or (refused? hit) (and (not (:ok hit)) (some? (:value hit))))
                  hit
                  (if (or (:ok hit) (nil? one) (nil? two))
                    (recur (term/cdr left) (term/cdr right) hit (conj acc (:value hit)))
                    (-> (errors/report-error hit :nodebugger-error
                                             "Yikes! I partly unified two sequences %s and %s but then found they couldn't be unified!%nI'll continue and hope for the best (sorry!)..."
                                             (errors/format-term left)
                                             (errors/format-term right))
                        (assoc :ok false :value nil))))))))))))

(defn- unify-pair
  "One atomic value for two expressions, or nil.

  The arguments are evaluated with fail-mode :fail, even when the
  unification itself is in :error mode. A protoinstance guard is not
  applied. An explanation is not consulted."
  [state x y & {:keys [classes-subsumep eagerly? fail-mode target]
                :or {fail-mode :fail}}]
  (cond
    (and (nil? x) (nil? y)) (assoc state :ok true :value nil)
    (nil? x) (unique state y :target target)
    (nil? y) (unique state x :target target)
    (kb/km-equal? x y) (unique state x :target target)
    (and (kb/km-triple? x) (kb/km-triple? y)) (fail state)
    (or (term/structured-list? x) (term/structured-list? y))
    (let [dx (explain/desource x)
          dy (explain/desource y)]
      (cond
        (and (term/structured-list? dy) (not (term/structured-list? dx)))
        (let [edx (unique state dx)]
          (cond
            (refused? edx) edx
            (not (term/structured-list? (:value edx)))
            (cond
              (nil? (:value edx)) (unique edx dy)
              (frame/anonymous-instance? (:kb edx) (:value edx))
              (let [ans (lazy-unify edx (:value edx) (or (:value (unique edx dy)) dy)
                                    :fail-mode fail-mode :eagerly? eagerly?
                                    :classes-subsumep classes-subsumep :target target)]
                (if (:ok ans)
                  ans
                  (fail-unify ans x y eagerly? classes-subsumep fail-mode)))
              (kb/km-args? dy)
              (unify-pair edx (term/km-list (term/car dy) (:value edx)) dy
                                :fail-mode fail-mode)
              :else (fail-unify edx x y eagerly? classes-subsumep fail-mode))
            :else (unify-pair edx (:value edx) dy :fail-mode fail-mode)))
        (and (term/structured-list? dx) (not (term/structured-list? dy)))
        (let [edy (unique state dy)]
          (cond
            (refused? edy) edy
            (not (term/structured-list? (:value edy)))
            (cond
              (nil? (:value edy)) (unique edy dx)
              (frame/anonymous-instance? (:kb edy) (:value edy))
              (let [ans (lazy-unify edy (or (:value (unique edy dx)) dx) (:value edy)
                                    :fail-mode fail-mode :eagerly? eagerly?
                                    :classes-subsumep classes-subsumep :target target)]
                (if (:ok ans) ans (fail-unify ans x y eagerly? classes-subsumep fail-mode)))
              (kb/km-args? dx)
              (unify-pair edy dx (term/km-list (term/car dx) (:value edy))
                                :fail-mode fail-mode)
              :else (fail-unify edy x y eagerly? classes-subsumep fail-mode))
            :else (unify-pair edy dx (:value edy) :fail-mode fail-mode)))
        (and (term/cons? dx) (term/cons? dy)
             (utils/eql? (term/car dx) (term/car dy))
             (not (utils/eql? (term/car dx) :triple)))
        (let [unified (unify-structured state dx dy
                                        :classes-subsumep classes-subsumep
                                        :eagerly? eagerly?
                                        :fail-mode fail-mode)]
          (if (:ok unified) unified (fail-unify unified x y eagerly? classes-subsumep fail-mode)))
        :else (fail-unify state x y eagerly? classes-subsumep fail-mode)))
    (kb/existential? y)
    (let [xf (unique state x :target target)]
      (cond
        (refused? xf) xf
        (nil? (:value xf)) (unique xf y :target target)
        :else (unify-existential xf (:value xf) y
                                 :classes-subsumep classes-subsumep
                                 :eagerly? eagerly?
                                 :fail-mode fail-mode
                                 :target target)))
    (kb/existential? x)
    (let [yf (unique state y :target target)]
      (cond
        (refused? yf) yf
        (nil? (:value yf)) (unique yf x :target target)
        :else (unify-existential yf (:value yf) x
                                 :classes-subsumep classes-subsumep
                                 :eagerly? eagerly?
                                 :fail-mode fail-mode
                                 :target target)))
    :else
    (let [xf (unique state x :target target)
          yf (if (refused? xf) xf (unique xf y :target target))]
      (cond
        (refused? yf) yf
        (nil? (:value xf)) (assoc yf :ok true)
        (nil? (:value yf)) (assoc yf :ok true :value (:value xf))
        (or (term/structured-list? (:value xf)) (term/structured-list? (:value yf)))
        (unify-pair yf (:value xf) (:value yf)
                          :classes-subsumep classes-subsumep
                          :eagerly? eagerly?
                          :fail-mode fail-mode
                          :target target)
        (and (kb/is-km-term? (:value xf)) (kb/is-km-term? (:value yf)))
        (let [unified (lazy-unify yf (:value xf) (:value yf)
                                  :eagerly? eagerly?
                                  :classes-subsumep classes-subsumep
                                  :fail-mode fail-mode
                                  :target target)]
          (if (:ok unified)
            unified
            (fail-unify unified (:value xf) (:value yf) eagerly? classes-subsumep fail-mode)))
        (= fail-mode :error)
        (fail (errors/report-error yf :user-error
                                   "Arguments in a unification expression should be unique KM objects!%nDoing (%s %s %s) [ie. (%s %s %s)]"
                                   (errors/format-term x)
                                   (errors/format-term (operator eagerly? classes-subsumep))
                                   (errors/format-term y)
                                   (errors/format-term (:value xf))
                                   (errors/format-term (operator eagerly? classes-subsumep))
                                   (errors/format-term (:value yf))))
        :else (fail yf)))))

(defn- pending-count
  [state left right]
  (if (and (kb/kb-object? left) (kb/kb-object? right)
           (stack/pending-equality? (:kb state) (:query state) left right))
    1
    0))

(defn- rank-pair
  [state left right]
  (let [classes1 (taxonomy/immediate-classes (:kb state) left)
        classes2 (taxonomy/immediate-classes (:kb classes1) right)
        state (adopt (adopt state classes1) classes2)
        same? (and (every? #(utils/member? % (:value classes2)) (utils/elements (:value classes1)))
                   (every? #(utils/member? % (:value classes1)) (utils/elements (:value classes2))))
        [state slot-score] (if-not (and same? (kb/kb-object? left) (kb/kb-object? right))
                             [state 0]
                             (let [[state s1] (slots-of state left)
                                   [state s2] (slots-of state right)]
                               [state (if (= (set (slot-names s1)) (set (slot-names s2))) 100 50)]))
        score (+ slot-score (* 2 (pending-count state left right)))]
    [state score]))

(defn- all-scored
  [state set1 set2]
  (loop [left set1
         state state
         acc []]
    (if (or (nil? left) (not (term/cons? left)))
      [state acc]
      (let [[state acc] (loop [right set2
                               state state
                               acc acc]
                          (if (or (nil? right) (not (term/cons? right)))
                            [state acc]
                            (let [[state score] (rank-pair state (term/car left) (term/car right))]
                              (recur (term/cdr right)
                                     state
                                     (conj acc [(term/car left) (term/car right) score])))))]
        (recur (term/cdr left) state acc)))))

(defn- lazy-unify-sets
  "The values from set1 that unified with a value from set2.

  A pair whose classes do not subsume is skipped. Both values then stay
  in the caller's combination. The score prefers matching classes."
  [state set1 set2 & {:keys [eagerly? target]}]
  (if (or (nil? set1) (nil? set2))
    (assoc state :ok true :value nil)
    (let [[state scored] (all-scored state set1 set2)
          ordered (vec (sort-by (fn [[_ _ score]] (- score)) scored))]
      (loop [pairs ordered
             set1 set1
             set2 set2
             state state
             acc []]
        (if (empty? pairs)
          (assoc state :ok true :value (term/build-list acc nil))
          (let [[v1 v2] (first pairs)]
            (if-not (and (utils/member? v1 set1) (utils/member? v2 set2))
              (recur (rest pairs) set1 set2 state acc)
              (let [hit (if eagerly?
                          (let [probed (probe state v1 v2 :classes-subsumep true)]
                            (if (or (refused? probed) (not (:ok probed)))
                              (fail probed)
                              (let [done (km probed (term/km-list v1 (symbol "&!") v2)
                                             :fail-mode :error :target target)]
                                (if (refused? done)
                                  done
                                  (assoc done :ok (some? (:value done)))))))
                          (lazy-unify state v1 v2
                                      :classes-subsumep true
                                      :fail-mode :fail
                                      :target target))]
                (if (or (refused? hit) (not (:ok hit)))
                  (if (refused? hit)
                    hit
                    (recur (rest pairs) set1 set2 hit acc))
                  (recur (rest pairs)
                         (drop-items set1 #(utils/eql? % v1))
                         (drop-items set2 #(utils/eql? % v2))
                         hit
                         (conj acc v1)))))))))))

(defn- shared-difference
  [left right]
  [(ordered-difference left right) (ordered-difference right left)])

(defn- eval-definite
  "Evaluate a value that is not an existential and not a structured list.

  Existential expressions are left in place. This step does not create
  a Skolem for them."
  [state exprs target]
  (loop [exprs exprs
         state state
         acc []]
    (cond
      (or (nil? exprs) (not (term/cons? exprs)))
      [state (term/build-list acc nil)]
      (or (kb/existential? (term/car exprs)) (term/structured-list? (term/car exprs)))
      (recur (term/cdr exprs) state (conj acc (term/car exprs)))
      :else
      (let [found (km state (term/car exprs) :target target)]
        (if (refused? found)
          [found :refused]
          (recur (term/cdr exprs)
                 found
                 (into acc (utils/elements (:value found)))))))))

(defn- lazy-unify-expr-sets
  "The combination of two sets.

  A failed pair is skipped, so the result keeps both values. When
  *remove-subsuming* is set, an existential that covers an instance is
  removed and that instance stays in the original set. A leftover
  (a Class) is not evaluated. (a Class) is not created. Explanations
  are not stored, so every value stays unexplained."
  [state exprs1 exprs2 & {:keys [eagerly? target]}]
  (if-not (and (utils/lisp-list? exprs1) (utils/lisp-list? exprs2))
    (-> (errors/report-error state :user-error
                             "(%s && %s): Arguments should be *sets* of values, but just found a single value!"
                             (errors/format-term exprs1)
                             (errors/format-term exprs2))
        (assoc :ok false :value nil))
    (if (subbag? exprs2 exprs1)
      (let [found (km state (kb/vals-to-val exprs1) :target target)]
        (if (refused? found) found (assoc found :ok true)))
      (let [set1 (km state (kb/vals-to-val exprs1) :target target)]
        (cond
          (refused? set1) set1
          (nil? (:value set1))
          (let [set2 (km set1 (kb/vals-to-val exprs2) :target target)]
            (if (refused? set2) set2 (assoc set2 :ok true)))
          :else
          (let [[state set2] (eval-definite set1 (frame/dereference (:kb set1) exprs2) target)]
            (if (= set2 :refused)
              state
              (let [[reduced1 reduced2] (shared-difference (:value set1) set2)
                    dropped (when (fn? *remove-subsuming*)
                              (*remove-subsuming* state reduced2 reduced1
                                                  :allow-coercion? true
                                                  :eagerly? eagerly?
                                                  :target target))]
                (if (and dropped (refused? dropped))
                  dropped
                  (let [state (or dropped state)
                        left (if dropped (:instances dropped) reduced1)
                        right (if dropped (:exprs dropped) set2)
                        unified (lazy-unify-sets state left right
                                                 :eagerly? eagerly? :target target)]
                    (if (refused? unified)
                      unified
                      (let [final (kb/remove-dup-instances
                                   (utils/append-lists
                                    (term/km-list
                                     (frame/dereference (:kb unified) (:value set1))
                                     (ordered-difference
                                      (frame/dereference (:kb unified) right)
                                      (frame/dereference (:kb unified) (:value unified))))))]
                        (assoc unified :ok true :value final)))))))))))))

(defn- regroup
  "Rewrite a chain of four or more of the same joiner.

  (a & b & c) becomes ((a & b) & c). A set joiner wraps the pair in an
  extra list. A different fourth operator is reported, then rewritten."
  [state expr joiner fail-mode]
  (let [n (length-of expr)]
    (if (or (nil? n) (< n 4) (not (utils/eql? (nth-el expr 1) joiner)))
      [state expr]
      (let [state (if (and (= fail-mode :error) (not (utils/eql? (nth-el expr 3) joiner)))
                    (errors/report-error state :user-error
                                         "Badly formed unification expression %s encountered during unification!"
                                         (errors/format-term expr))
                    state)
            pair (term/km-list (term/car expr) joiner (nth-el expr 2))
            head (if (kb/val-unification-operator? joiner) pair (term/km-list pair))
            revised (term/build-list [head joiner] (term/cdr (term/cdr (term/cdr (term/cdr expr)))))]
        (regroup state revised joiner fail-mode)))))

(defn- amp-expr1
  [state expr joiner fail-mode target]
  (cond
    (nil? expr) (assoc state :ok true :value nil)
    (and (term/cons? expr) (utils/eql? (nth-el expr 1) joiner))
    (let [[state expr] (regroup state expr joiner fail-mode)
          left (amp-expr1 state (term/car expr) joiner fail-mode target)]
      (if (refused? left)
        left
        (let [right (amp-expr1 left (nth-el expr 2) joiner fail-mode target)]
          (cond
            (refused? right) right
            (kb/val-unification-operator? joiner)
            (unify-pair right (:value left) (:value right)
                              :eagerly? (utils/eql? joiner (symbol "&!"))
                              :fail-mode fail-mode
                              :target target)
            :else
            (lazy-unify-expr-sets right
                                  (if (some? (:value left)) (:value left) nil)
                                  (if (some? (:value right)) (:value right) nil)
                                  :eagerly? (utils/eql? joiner (symbol "&&!"))
                                  :target target)))))
    (and (term/singleton? expr)
         (kb/set-unification-operator? joiner)
         (term/cons? (term/car expr))
         (utils/eql? (nth-el (term/car expr) 1) joiner))
    (amp-expr1 state (term/car expr) joiner fail-mode target)
    :else (assoc state :ok true :value expr)))

(defn lazy-unify-&-expr
  "The values of one & or && expression.

  :value is a list, or nil. The caller decides whether a nil result
  rolls the knowledge base back. Constraints on the expression are
  enforced by the slot reader, not here."
  [state expr km-int & {:keys [joiner fail-mode target] :or {joiner (symbol "&") fail-mode :fail}}]
  (binding [*km-int* km-int]
    (let [unified (amp-expr1 (assoc state :target target) expr joiner fail-mode target)]
      (if (refused? unified)
        unified
        (clean
         (assoc unified :value
                (drop-nil-values
                 (if (kb/val-unification-operator? joiner)
                   (when (some? (:value unified)) (term/km-list (:value unified)))
                   (:value unified)))))))))

(defn unifiable-with-existential
  "Whether instance can unify with an existential expression.

  Nothing is written. :value is (t) or nil."
  [state instance expr km-int & {:keys [classes-subsumep fail-mode] :or {fail-mode :fail}}]
  (binding [*km-int* km-int]
    (let [hit (unify-existential state instance expr
                                 :classes-subsumep classes-subsumep
                                 :fail-mode fail-mode
                                 :commit? false)]
      (if (refused? hit)
        hit
        (clean (assoc state
                      :errors (vec (or (:errors hit) []))
                      :warnings (vec (or (:warnings hit) []))
                      :error-structures (vec (or (:error-structures hit) []))
                      :value (when (:ok hit) (term/km-list (symbol "t")))))))))

(defn lazy-unify-exprs
  "One value of unifying x and y, or nil.

  This is the &+ entry. A failure does not by itself restore the
  knowledge base. The caller does that."
  [state x y km-int & {:keys [classes-subsumep eagerly? fail-mode target]
                       :or {fail-mode :fail}}]
  (binding [*km-int* km-int]
    (clean
     (unify-pair state x y
                       :classes-subsumep classes-subsumep
                       :eagerly? eagerly?
                       :fail-mode fail-mode
                       :target target))))
