(ns som.km.stack
  "The goal stack and the loop check, from stack.lisp.

  A goal is five elements: the canonical expression, the situation, the
  expression that was pushed, the inference number, and the target.
  The target is (the slot of frame), or empty. Both this stack and the
  object stack live on the query, not in the saved knowledge base.

  looping-on? compares canonical forms after bindings are followed.
  &+! is not rewritten to the same form as &. An or between a goal and
  its repeat is still a loop. The comment in stack.lisp describes a
  revised check and does not implement it.

  The interpreter pushes goals and dispatches the inspectors.
  Nothing here is printed."
  (:require [som.km.explain :as explain]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.minimatch :as match]
            [som.km.print :as print]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(def ^:private all-situations (symbol "all situations"))
(def ^:private unified-with (symbol "unified-with"))
(def ^:private set-unified-with (symbol "set-unified-with"))
(def ^:private amp-plus-bang (symbol "&+!"))
(def ^:private the-symbol (symbol "the"))
(def ^:private of-symbol (symbol "of"))

(def ^:private the-of-pattern
  (term/km-list the-symbol (symbol "?slot") of-symbol (symbol "?instance")))

(defn- dotted!
  [tail]
  (throw (ex-info "This list is dotted." {:tail tail})))

(defn- query-of
  [query]
  (or query frame/empty-query))

(defn- nth-el
  [coll n]
  (loop [coll coll
         n n]
    (cond
      (nil? coll) nil
      (not (term/cons? coll)) (dotted! coll)
      (zero? n) (term/car coll)
      :else (recur (term/cdr coll) (dec n)))))

(defn- second-el
  "The second element. A dotted pair is an error, as Lisp second is."
  [expr]
  (when (term/cons? expr)
    (let [tail (term/cdr expr)]
      (cond
        (nil? tail) nil
        (term/cons? tail) (term/car tail)
        :else (dotted! tail)))))

(defn- proper-length
  [value]
  (loop [value value
         n 0]
    (cond
      (nil? value) n
      (term/cons? value) (recur (term/cdr value) (inc n))
      :else (dotted! value))))

(defn- last-el
  [coll]
  (loop [coll coll
         found nil]
    (cond
      (nil? coll) found
      (term/cons? coll) (recur (term/cdr coll) (term/car coll))
      :else (dotted! coll))))

(defn- reverse-list
  [coll]
  (loop [coll coll
         acc nil]
    (cond
      (nil? coll) acc
      (term/cons? coll) (recur (term/cdr coll) (term/cons-cell (term/car coll) acc))
      :else (dotted! coll))))

(defn- pushnew
  [item coll]
  (if (utils/member? item coll) coll (term/cons-cell item coll)))

(defn inference-number
  "One more than the two inference counters stored on the query.

  Both counters start at 0, so the first recorded goal is inference 1.
  reset does not clear them. A query increments the query-directed
  counter as it runs. The classification counter stays as the caller
  left it."
  [query]
  (let [query (query-of query)]
    (inc (+ (or (:classification-inferences query) 0)
            (or (:query-directed-inferences query) 0)))))

(defn km-canonicalize
  "The form a goal is compared as.

  A two-element path (frame slot) becomes (the slot of frame), unless
  the frame is a reserved keyword. &&, &&!, and === become
  set-unified-with, in the written order. &, &?, &!, &+, &+?, and ==
  become unified-with. Two symbols are ordered by name: the greater
  name is moved second. &+! is left as written. The interpreter splits
  it into a test and then &!, and those goals must stay distinct.
  Any other expression is returned as it is."
  [expr]
  (cond
    (and (term/pair? expr)
         (not (contains? kb/reserved-keywords (term/car expr))))
    (term/km-list the-symbol (nth-el expr 1) of-symbol (term/car expr))

    (and (term/triple? expr)
         (kb/set-unification-operator? (nth-el expr 1)))
    (term/km-list (term/car expr) set-unified-with (nth-el expr 2))

    (and (term/triple? expr)
         (kb/val-unification-operator? (nth-el expr 1))
         (not (utils/eql? (nth-el expr 1) amp-plus-bang)))
    (let [left (term/car expr)
          right (nth-el expr 2)]
      (if (and (term/lisp-symbol? left)
               (term/lisp-symbol? right)
               (pos? (compare (term/symbol-name left) (term/symbol-name right))))
        (term/km-list right unified-with left)
        (term/km-list left unified-with right)))

    :else expr))

(defn item-to-stack
  "The five-element goal for expr.

  The elements are the canonical expression, the situation, expr, the
  inference number, and target. A unification is stored under
  |all situations|. Any other goal uses the current situation."
  [kb query expr & {:keys [target]}]
  (term/km-list
   (km-canonicalize expr)
   (if (and (term/cons? expr)
            (kb/unification-operator? (second-el expr)))
     all-situations
     (frame/current-situation kb))
   expr
   (inference-number query)
   target))

(defn stacked-canonical
  "The canonical expression of one stacked goal."
  [item]
  (nth-el item 0))

(defn stacked-situation
  "The situation recorded on one stacked goal."
  [item]
  (nth-el item 1))

(defn stacked-expr
  "The expression that was pushed, before canonicalizing."
  [item]
  (nth-el item 2))

(defn stacked-inference-number
  "The inference number recorded when the goal was pushed."
  [item]
  (nth-el item 3))

(defn stacked-target
  "The (the slot of frame) this goal is for, or nil."
  [item]
  (nth-el item 4))

(defn- stack-equal
  "True when a new goal repeats a stacked goal.

  item1 is the new goal and item2 is already stacked. The test is not
  symmetrical: a new set-unified-with can repeat an old unified-with,
  and the opposite pairing does not."
  [kb item1 item2]
  (let [left (frame/dereference kb (stacked-canonical item1))
        right (frame/dereference kb (stacked-canonical item2))]
    (and (or (utils/equal? left right)
             (and (term/cons? left)
                  (term/cons? right)
                  (utils/eql? (second-el left) set-unified-with)
                  (utils/eql? (second-el right) unified-with)
                  (or (and (utils/equal? (term/car left)
                                         (term/km-list (term/car right)))
                           (utils/equal? (nth-el left 2)
                                         (term/km-list (nth-el right 2))))
                      (and (utils/equal? (term/car left)
                                         (term/km-list (nth-el right 2)))
                           (utils/equal? (nth-el left 2)
                                         (term/km-list (term/car right)))))))
         (utils/eql? (stacked-situation item1) (stacked-situation item2)))))

(defn goal-stack
  "The goal stack, newest goal first."
  [query]
  (:goal-stack (query-of query)))

(defn top-level-goal
  "The canonical form of the oldest goal, or nil when the stack is empty."
  [query]
  (when-let [item (last-el (goal-stack query))]
    (stacked-canonical item)))

(defn on-goal-stack?
  "True when expr is already a goal in this situation.

  The canonical forms are compared after bindings are followed. target
  is recorded on the probe and is not compared."
  [kb query expr & {:keys [target]}]
  (let [query (query-of query)
        probe (item-to-stack kb query expr :target target)]
    (boolean (utils/member? probe (:goal-stack query)
                            (fn [item stacked] (stack-equal kb item stacked))))))

(defn looping-on?
  "True when expr repeats a goal already on the stack.

  Comments and sources are removed first. (the parts of _X) and
  (the parts of _Engine1) are the same goal once _X is bound to
  _Engine1, in the same situation. An or between the two copies does
  not make this false."
  [kb query expr]
  (on-goal-stack? kb query (explain/desource-decomment expr)))

(defn- equality-ends
  "The two sides of a three-element full equality, or nil."
  [expr]
  (when (and (term/cons? expr)
             (= 3 (proper-length expr))
             (kb/full-equality-assertion-operator? (nth-el expr 1)))
    [(term/car expr) (nth-el expr 2)]))

(defn- track-unified
  [instances expr]
  (if-let [[left right] (equality-ends expr)]
    (if (and (kb/kb-object? left) (kb/kb-object? right))
      (pushnew left (pushnew right instances))
      instances)
    instances))

(defn- drop-instance
  [instances item]
  (if (and (kb/kb-object? item) (utils/member? item instances))
    (utils/remove-items item instances)
    instances))

(defn- untrack-unified
  [instances expr]
  (if (nil? instances)
    nil
    (if-let [[left right] (equality-ends expr)]
      (-> instances (drop-instance left) (drop-instance right))
      instances)))

(defn push-to-goal-stack
  "Push expr onto the goal stack.

  Comments and sources are removed before the goal is built. A full
  equality whose two sides are both knowledge-base objects records
  both on :instances-being-unified, the right-hand side first. :value
  is the five-element goal. The knowledge base is unchanged."
  [kb query expr & {:keys [target]}]
  (let [query (query-of query)
        cleaned (explain/desource-decomment expr)
        item (item-to-stack kb query cleaned :target target)
        instances (track-unified (:instances-being-unified query)
                                 (stacked-expr item))
        query (assoc query :goal-stack (term/cons-cell item (:goal-stack query)))
        query (if (nil? instances)
                query
                (assoc query :instances-being-unified instances))]
    {:kb kb :query query :value item}))

(defn pop-from-goal-stack
  "Remove the newest goal and return it.

  An empty stack returns nil. A full equality taken off the stack drops
  its two instances from :instances-being-unified when they are present.
  Clearing the stack does not do this."
  [kb query]
  (let [query (query-of query)
        stack (:goal-stack query)]
    (if (nil? stack)
      {:kb kb :query query :value nil}
      (let [item (term/car stack)
            instances (:instances-being-unified query)
            query (assoc query :goal-stack (term/cdr stack))
            query (if (nil? instances)
                    query
                    (assoc query :instances-being-unified
                           (untrack-unified instances (stacked-expr item))))]
        {:kb kb :query query :value item}))))

(defn clear-goal-stack
  "Drop every goal. Instances being unified stay on the query."
  [query]
  {:query (assoc (query-of query) :goal-stack nil) :value nil})

(defn clear-obj-stack
  "Drop every name from the object stack. The goal stack stays."
  [query]
  {:query (assoc (query-of query) :obj-stack nil) :value nil})

(defn new-context
  "Clear the object stack. This is new-context."
  [query]
  (clear-obj-stack query))

(defn- pending-expr?
  [kb expr x y]
  (and (term/cons? expr)
       (= 3 (proper-length expr))
       (kb/equality-assertion-operator? (nth-el expr 1))
       (let [left (frame/dereference kb (term/car expr))
             right (frame/dereference kb (nth-el expr 2))]
         (or (and (utils/eql? x left) (utils/eql? y right))
             (and (utils/eql? y left) (utils/eql? x right))))))

(defn- pending-in-set?
  [kb expr x y]
  (loop [items expr]
    (cond
      (nil? items) false
      (not (term/cons? items)) (dotted! items)
      (pending-expr? kb (term/car items) x y) true
      :else (recur (term/cdr items)))))

(defn pending-equality?
  "True when x and y are the two sides of an equality still on the stack.

  Bindings are followed on x, y, and on the stacked expression. A :set
  goal is searched for an equality inside it. &? is not an equality
  assertion, so a test does not count."
  [kb query x y]
  (let [x (frame/dereference kb x)
        y (frame/dereference kb y)]
    (loop [stack (goal-stack query)]
      (cond
        (nil? stack) false
        (not (term/cons? stack)) (dotted! stack)
        :else
        (let [expr (stacked-expr (term/car stack))]
          (if (or (pending-expr? kb expr x y)
                  (and (kb/km-set? expr) (pending-in-set? kb expr x y)))
            true
            (recur (term/cdr stack))))))))

(defn- every-fully-evaluated?
  [vals]
  (loop [vals vals]
    (cond
      (nil? vals) true
      (not (term/cons? vals)) (dotted! vals)
      (kb/fully-evaluated? (term/car vals)) (recur (term/cdr vals))
      :else false)))

(defn- first-kb-object
  [vals]
  (loop [vals vals]
    (cond
      (nil? vals) nil
      (not (term/cons? vals)) (dotted! vals)
      (kb/kb-object? (term/car vals)) (term/car vals)
      :else (recur (term/cdr vals)))))

(defn- every-kb-object?
  [vals]
  (loop [vals vals]
    (cond
      (nil? vals) true
      (not (term/cons? vals)) (dotted! vals)
      (kb/kb-object? (term/car vals)) (recur (term/cdr vals))
      :else false)))

(defn- first-ground-set
  [sets]
  (loop [sets sets]
    (cond
      (nil? sets) nil
      (not (term/cons? sets)) (dotted! sets)
      (every-kb-object? (term/car sets)) (term/car sets)
      :else (recur (term/cdr sets)))))

(defn- mark-looping
  [query]
  (assoc query :looping? true))

(defn- loop-result
  [kb query value]
  {:kb kb :query (mark-looping query) :value value})

(defn handle-looping
  "The value a repeated goal returns.

  :looping? on the query becomes true. reason is :loop-detected, the
  default, or :depth-limit-reached. (the slot of frame), including a
  path rewritten to that form, returns the values already stored when
  every value is fully evaluated. A stored value that still needs
  evaluation, and is not itself the current goal, is returned as
  :evaluate together with :slot and :instance. The interpreter
  evaluates that residue and writes it back. A residue that is itself
  looping returns nil and does not name :evaluate. &? and &+? return
  (t) for either reason. Another value unification returns a list of
  the first knowledge-base object in the expression, when there is
  one. A && expression returns the first set whose elements are all
  knowledge-base objects. Any other goal returns nil. Nothing is
  printed. The depth limit itself is applied by the interpreter."
  [kb query expr & {:keys [reason] :or {reason :loop-detected}}]
  (let [query (query-of query)
        canonical (km-canonicalize expr)]
    (cond
      (and (match/minimatch canonical the-of-pattern)
           (term/lisp-symbol? (nth-el canonical 1))
           (kb/kb-object? (nth-el canonical 3)))
      (let [slot (nth-el canonical 1)
            instance (nth-el canonical 3)
            found (frame/get-vals
                   kb instance slot
                   :situation (frame/target-situation
                               kb (frame/current-situation kb) instance slot)
                   :query query)
            vals (:value found)]
        (if (every-fully-evaluated? vals)
          (loop-result (:kb found) (:query found) vals)
          (let [residual (kb/vals-to-val vals)
                blocked (loop-result (:kb found) (:query found) nil)]
            (if (looping-on? (:kb found) (:query found) residual)
              blocked
              (assoc blocked :evaluate residual :slot slot :instance instance)))))

      (and (term/cons? expr)
           (kb/val-unification-operator? (second-el expr)))
      (if (contains? #{(symbol "&?") (symbol "&+?")} (second-el expr))
        (loop-result kb query
                     (when (contains? #{:loop-detected :depth-limit-reached} reason)
                       (term/km-list (symbol "t"))))
        (if-let [val (first-kb-object (kb/&-expr-to-vals expr))]
          (loop-result kb query (term/km-list val))
          (loop-result kb query nil)))

      (kb/&&-expr? expr)
      (if-let [answer (first-ground-set
                       (kb/&&-exprs-to-valsets (term/km-list expr)))]
        (loop-result kb query answer)
        (loop-result kb query nil))

      :else (loop-result kb query nil))))

(defn- line-column
  [sb]
  (let [text (str sb)
        break (clojure.string/last-index-of text \newline)]
    (if (nil? break)
      (count text)
      (- (count text) break 1))))

(defn- tab-to
  "Pad to a column. Past that column, one space is written.

  This is ~T with a column increment of 1."
  [sb column]
  (let [column-now (line-column sb)
        target (if (< column-now column) column (inc column-now))]
    (dotimes [_ (- target column-now)]
      (.append ^StringBuilder sb \space))))

(defn- show-situations?
  [stack]
  (loop [stack stack]
    (cond
      (nil? stack) false
      (not (term/cons? stack)) (dotted! stack)
      (not (utils/eql? (stacked-situation (term/car stack))
                       term/global-situation))
      true
      :else (recur (term/cdr stack)))))

(defn- append-goal
  [sb item depth show-situations? show-numbers?]
  (let [expr (explain/desource (stacked-expr item))
        situation (stacked-situation item)
        target (stacked-target item)]
    (when show-numbers?
      (.append ^StringBuilder sb (print/km-format (stacked-inference-number item))))
    (tab-to sb (if show-numbers? (+ depth 7) depth))
    (.append ^StringBuilder sb "-> ")
    (.append ^StringBuilder sb (print/km-format expr))
    (cond
      (and (some? target) show-situations?)
      (do (.append ^StringBuilder sb \newline)
          (tab-to sb (+ depth 3))
          (.append ^StringBuilder sb "[for ")
          (.append ^StringBuilder sb (print/km-format target))
          (.append ^StringBuilder sb ", in ")
          (.append ^StringBuilder sb (print/km-format situation))
          (.append ^StringBuilder sb "]\n"))

      show-situations?
      (do (tab-to sb 55)
          (.append ^StringBuilder sb "[called in ")
          (.append ^StringBuilder sb (print/km-format situation))
          (.append ^StringBuilder sb "]\n"))

      (some? target)
      (do (.append ^StringBuilder sb \newline)
          (tab-to sb (+ depth 3))
          (.append ^StringBuilder sb "[for ")
          (.append ^StringBuilder sb (print/km-format target))
          (.append ^StringBuilder sb "]\n"))

      :else (.append ^StringBuilder sb \newline))))

(defn show-goal-stack
  "The text show-goal-stack would print. :value is nil.

  The oldest goal is first. A situation is shown when any goal was
  recorded outside *Global, including a unification under
  |all situations|. show-inference-numbers? prints the recorded number
  in front of the arrow. Nothing is printed."
  [kb query & {:keys [show-inference-numbers?]}]
  (let [query (query-of query)
        stack (goal-stack query)
        shown? (show-situations? stack)
        sb (StringBuilder.)]
    (.append sb "--------------------\n\n")
    (.append sb " CURRENT GOAL STACK IS AS FOLLOWS:\n")
    (loop [pending (reverse-list stack)
           depth 1]
      (when (term/cons? pending)
        (append-goal sb (term/car pending) depth shown? show-inference-numbers?)
        (recur (term/cdr pending) (inc depth))))
    (.append sb "\n--------------------\n")
    {:kb kb :query query :value nil :text (str sb)}))

(defn show-obj-stack
  "The text show-obj-stack would print. :value is true.

  Bindings are followed first, and the followed stack is written back
  on the query. Nothing is printed."
  [kb query]
  (let [read (frame/obj-stack kb query)
        sb (StringBuilder.)]
    (loop [items (:value read)]
      (cond
        (nil? items) nil
        (not (term/cons? items)) (dotted! items)
        :else
        (do (.append sb "   ")
            (.append sb (print/km-format (term/car items)))
            (.append sb \newline)
            (recur (term/cdr items)))))
    {:kb kb :query (:query read) :value true :text (str sb)}))

(defn show-context
  "show-obj-stack. The older name is show-context."
  [kb query]
  (show-obj-stack kb query))
