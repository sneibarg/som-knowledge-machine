(ns som.km.slotvals
  "Local slot values, and the six places a slot value can come from.

  Prototypes, projection, subslots, supersituations, and inheritance
  return nothing. The local store is read, evaluated, and written back
  unless the slot says not to cache. A constraint that evaluated to
  nothing is put back, so a read does not drop it. Constraints are not
  enforced. The interpreter is passed in, so this namespace does not
  call it by name."
  (:require [som.km.explain :as explain]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.print :as print]
            [som.km.stack :as stack]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(def ^:private own-properties (symbol "own-properties"))
(def ^:private own-definition (symbol "own-definition"))
(def ^:private dont-cache (symbol "dont-cache-values"))

(def ^:private bag-aggregation
  #{(symbol "min") (symbol "max") (symbol "sum") (symbol "average")
    (symbol "difference") (symbol "product") (symbol "quotient")})

(def ^:private set-position
  #{(symbol "first") (symbol "second") (symbol "third")
    (symbol "fourth") (symbol "fifth") (symbol "last")})

(defn- refused?
  [state]
  (= "not-ported" (:error state)))

(defn- adopt
  "Keep the accumulated notes and take the store's knowledge base."
  [state stored]
  (assoc state
         :kb (:kb stored)
         :query (or (:query stored) (:query state))))

(defn- dotted!
  [tail]
  (throw (ex-info "This list is dotted." {:tail tail})))

(defn- nth-value
  [values n]
  (loop [values values
         n n]
    (cond
      (nil? values) nil
      (not (term/cons? values)) (dotted! values)
      (zero? n) (term/car values)
      :else (recur (term/cdr values) (dec n)))))

(defn- proper-length
  [value]
  (loop [value value
         seen 0]
    (cond
      (nil? value) seen
      (term/cons? value) (recur (term/cdr value) (inc seen))
      :else nil)))

(defn- caches?
  "True unless dont-cache-values is stored on the slot in *Global.

  A slot that is not a frame has no such value and is cached."
  [kb slot]
  (nil? (:value (frame/get-vals kb slot dont-cache
                                :situation term/global-situation
                                :dereference? false))))

(defn- constraint-walk
  "Constraint expressions inside expr. plurality is :plural or :singular.

  A unification of four or more elements is rewritten to (left op rest)
  before the two sides are walked. The Lisp reports a badly formed
  unification when the fourth element is not an operator, then rewrites
  anyway. This walk rewrites and does not report that sentence."
  [expr plurality]
  (cond
    (nil? expr) nil
    (and (term/cons? expr)
         (kb/unification-operator? (nth-value expr 1))
         (when-let [length (proper-length expr)]
           (>= length 4)))
    (constraint-walk (term/km-list (term/car expr)
                                   (nth-value expr 1)
                                   (term/cdr (term/cdr expr)))
                     :singular)
    (and (term/cons? expr)
         (kb/unification-operator? (nth-value expr 1)))
    (let [side (if (kb/val-unification-operator? (nth-value expr 1)) :singular :plural)]
      (utils/append-lists
       (term/km-list (constraint-walk (term/car expr) side)
                     (constraint-walk (nth-value expr 2) side))))
    (and (= plurality :plural) (term/singleton? expr))
    (constraint-walk (term/car expr) :singular)
    (and (= plurality :singular) (kb/constraint-expr? expr))
    (term/km-list expr)
    (and (= plurality :plural) (term/cons? expr))
    (loop [expr expr
           acc nil]
      (cond
        (nil? expr) acc
        (not (term/cons? expr)) (dotted! expr)
        :else (recur (term/cdr expr)
                     (utils/append-lists
                      (term/km-list acc (constraint-walk (term/car expr) :singular))))))
    :else nil))

(defn- own-rules
  "Local values as a list of value lists. Supersituations add nothing.

  Own properties are used. Own definition is used when those are empty.
  Self is replaced. Comments stay, because the Lisp asks for them.
  :raw is the bound value list. :value is that list split into value
  lists. Constraints are read from :raw, not from the split lists."
  [state instance slot]
  (let [kb (:kb state)
        situation (frame/target-situation kb (frame/current-situation kb) instance slot)
        query (:query state)
        own (frame/get-vals kb instance slot
                            :facet own-properties
                            :situation situation
                            :query query)
        defined (if (some? (:value own))
                  own
                  (frame/get-vals (:kb own) instance slot
                                  :facet own-definition
                                  :situation situation
                                  :query (:query own)))]
    (when-let [values (:value defined)]
      (let [bound (frame/bind-self values instance)]
        {:kb (:kb defined)
         :query (:query defined)
         :raw bound
         :value (kb/&&-exprs-to-valsets bound)}))))

(defn- simple-local?
  "One value list of one atom that is not :incomplete and not a binding."
  [kb rules]
  (and (term/singleton? rules)
       (term/singleton? (term/car rules))
       (utils/lisp-atom? (term/car (term/car rules)))
       (not (utils/eql? (term/car (term/car rules)) :incomplete))
       (utils/eql? (frame/dereference kb (term/car (term/car rules)))
                   (term/car (term/car rules)))))

(defn- put-local
  [state instance slot values]
  (if-not (caches? (:kb state) slot)
    state
    (adopt state (frame/put-vals (:kb state) instance slot values
                                 :situation (frame/target-situation
                                             (:kb state)
                                             (frame/current-situation (:kb state))
                                             instance slot)
                                 :query (:query state)))))

(defn- reattach
  "Put local constraints back onto the values a read just computed."
  [kb slot values constraints]
  (if (nil? constraints)
    values
    (if (frame/single-valued-slot? kb slot)
      (kb/val-to-vals (kb/vals-to-&-expr (utils/append-lists (term/km-list values constraints))))
      (utils/append-lists (term/km-list values constraints)))))

(defn slotvals-from-kb
  "The six sources of one slot. Only the local store contributes.

  km-int is called as (km-int state expr :target target). A refusal is
  returned unchanged and the slot is left as it was. Other sources are
  present as empty results: prototypes, projection, subslots,
  supersituations, and inheritance."
  [state instance slot km-int & {:keys [target]}]
  (let [rules (own-rules state instance slot)
        state (if rules (adopt state rules) state)
        constraints (when rules (constraint-walk (:raw rules) :plural))
        single? (frame/single-valued-slot? (:kb state) slot)
        appending? (frame/appending-slot? (:kb state) slot)]
    (cond
      (nil? rules)
      (assoc state :value nil :sources {:prototypes nil
                                        :projection nil
                                        :subslots nil
                                        :supersituations nil
                                        :local nil
                                        :inheritance nil})

      (simple-local? (:kb state) (:value rules))
      (let [values (term/car (:value rules))
            kept (reattach (:kb state) slot values constraints)
            stored (put-local state instance slot kept)]
        (assoc stored :value values))

      :else
      (let [expr (kb/val-sets-to-expr (:value rules)
                                      :single-valued? single?
                                      :combine-values-by-appending? appending?)
            evaluated (km-int state expr :target target)]
        (if (refused? evaluated)
          evaluated
          (let [values (:value evaluated)
                kept (reattach (:kb evaluated) slot values constraints)
                stored (put-local evaluated instance slot kept)]
            (assoc stored :value values)))))))

(defn- numeric-list?
  [values]
  (loop [values values]
    (cond
      (nil? values) true
      (not (term/cons? values)) false
      (number? (term/car values)) (recur (term/cdr values))
      :else false)))

(defn- aggregate
  "Apply f to every number. An empty sum is 0. Any other empty or
  non-numeric bag asks for a Number, which is not created here."
  [state values f km-int empty-sum?]
  (cond
    (and (nil? values) empty-sum?) (assoc state :value (term/km-list 0))
    (and (nil? values) (not empty-sum?))
    (km-int state (term/km-list (symbol "a") (symbol "Number")) :fail-mode :error)
    (numeric-list? values)
    (assoc state :value (term/km-list (apply f (utils/elements values))))
    :else
    (km-int state (term/km-list (symbol "a") (symbol "Number")) :fail-mode :error)))

(defn- position-value
  [frames slot]
  (let [n (cond
            (utils/eql? slot (symbol "first")) 0
            (utils/eql? slot (symbol "second")) 1
            (utils/eql? slot (symbol "third")) 2
            (utils/eql? slot (symbol "fourth")) 3
            (utils/eql? slot (symbol "fifth")) 4
            (utils/eql? slot (symbol "last")) (when-let [n (proper-length frames)]
                                                (dec n)))]
    (when (and (some? n) (not (neg? n)))
      (nth-value frames n))))

(defn- error-structure
  "The expression on top of the goal stack, or the expression in hand."
  [state]
  (let [stack (get-in state [:query :goal-stack])]
    (if (term/cons? stack)
      (stack/stacked-expr (term/car stack))
      (:current-expr state))))

(defn- user-error
  "Record a user error. The template uses %s and the arguments are already text.

  The answer is nil. Nothing is printed."
  [state template & args]
  (-> state
      (assoc :value nil)
      (update :errors (fnil conj [])
              (clojure.string/trim (str "ERROR! " (apply format template args))))
      (update :error-structures (fnil conj []) (error-structure state))))

(defn one-slotvals
  "The values of slot on one frame.

  Arithmetic slots, bags, sequences, and :args are computed here. A
  class walk such as all-superclasses is not. A stored value on an
  ordinary slot, including superclasses stored on a built-in class, is
  read from the local store. km-int evaluates a local rule."
  [state frame slot km-int & {:keys [fail-mode] :or {fail-mode :fail}}]
  (cond
    (nil? frame) (assoc state :value nil)

    (and (contains? #{(symbol "min") (symbol "max")} slot)
         (not (kb/km-bag? frame))
         (number? frame))
    (assoc state :value (term/km-list frame))

    (contains? bag-aggregation slot)
    (if (kb/km-bag? frame)
      (let [values (kb/seq-elements frame)]
        (cond
          (utils/eql? slot (symbol "sum"))
          (aggregate state values +' km-int true)
          (utils/eql? slot (symbol "product"))
          (aggregate state values *' km-int false)
          (utils/eql? slot (symbol "difference"))
          (aggregate state values -' km-int false)
          (utils/eql? slot (symbol "min"))
          (aggregate state values min km-int false)
          (utils/eql? slot (symbol "max"))
          (aggregate state values max km-int false)
          (utils/eql? slot (symbol "quotient"))
          (aggregate state values / km-int false)
          (utils/eql? slot (symbol "average"))
          (if (and (some? values) (numeric-list? values))
            (assoc state :value (term/km-list (/ (apply +' (utils/elements values))
                                                 (proper-length values))))
            (km-int state (term/km-list (symbol "a") (symbol "Number")) :fail-mode :error))))
      (user-error state
                  "(the %s of %s): %s should be given a bag (:bag ...) as an argument."
                  (print/km-format slot)
                  (print/km-format frame)
                  (print/km-format slot)))

    (kb/km-args? frame)
    (km-int state (term/km-list (symbol "the") slot (symbol "of") (nth-value frame 1))
            :fail-mode fail-mode)

    (utils/eql? slot (symbol "elements"))
    (if (term/structured-list? frame)
      (assoc state :value (kb/flatten-sets (kb/seq-elements frame)))
      (-> (user-error state
                      "Trying to find the elements of a non-sequence/non-bag %s. Continuing, returning (%s)..."
                      (print/km-format frame)
                      (print/km-format frame))
          (assoc :value (term/km-list frame))))

    (utils/eql? slot (symbol "seq-length"))
    (if (term/structured-list? frame)
      (assoc state :value (term/km-list (proper-length (kb/seq-elements frame))))
      (user-error state
                  "Trying to find the length of a non-sequence %s. (Use `number' not `length' to find the number of elements in a set)"
                  (print/km-format frame)))

    (utils/eql? slot (symbol "bag-length"))
    (if (kb/km-bag? frame)
      (assoc state :value (term/km-list (proper-length (kb/seq-elements frame))))
      (user-error state
                  "Trying to find the length of a non-bag %s. (Use `number' not `length' to find the number of elements in a set)"
                  (print/km-format frame)))

    (kb/km-function? frame)
    (user-error state
                "Trying to take the slot of a function (not allowed). Doing (the %s of %s)"
                (print/km-format slot)
                (print/km-format frame))

    (term/structured-list? frame)
    (let [head (term/car frame)]
      (loop [items (term/cdr frame)
             current state
             acc []]
        (cond
          (refused? current) current
          (nil? items)
          (assoc current :value
                 (term/km-list (term/cons-cell head (term/build-list acc nil))))
          (not (term/cons? items)) (dotted! items)
          :else
          (let [next (km-int current
                             (term/km-list (symbol "the") slot (symbol "of") (term/car items))
                             :fail-mode fail-mode)]
            (if (refused? next)
              next
              (recur (term/cdr items)
                     next
                     (into acc (utils/elements (:value next)))))))))

    (utils/lisp-list? frame)
    (user-error state
                "Trying to get a slot value of a list of frames, rather than a single frame. slot: %s. frame: %s."
                (print/km-format slot)
                (print/km-format frame))

    (contains? #{(symbol "abs") (symbol "log") (symbol "exp")
                 (symbol "sqrt") (symbol "floor")}
               slot)
    (assoc state :value
           (term/km-list
            (cond
              (not (number? frame)) frame
              (utils/eql? slot (symbol "abs")) (if (neg? frame) (-' frame) frame)
              (utils/eql? slot (symbol "floor")) (long (Math/floor (double frame)))
              (utils/eql? slot (symbol "log")) (Math/log (double frame))
              (utils/eql? slot (symbol "exp")) (Math/exp (double frame))
              (utils/eql? slot (symbol "sqrt")) (Math/sqrt (double frame)))))

    (and (utils/eql? slot (symbol "name"))
         (not (kb/kb-object? frame)))
    (assoc state :value
           (cond
             (string? frame) (term/km-list frame)
             (number? frame) (term/km-list (print/km-format frame))
             :else nil))

    (not (kb/kb-object? frame))
    (user-error state
                "(the %s of %s): Attempt to find a property of a non-kb-object %s."
                (print/km-format slot)
                (print/km-format frame)
                (print/km-format frame))

    (utils/eql? slot (symbol "cardinality"))
    (let [card (frame/cardinality-of (:kb state) frame)]
      (assoc state :value (when card (term/km-list card))))

    (utils/eql? slot (symbol "fluent-status"))
    (assoc state :value (term/km-list (frame/fluent-status (:kb state) frame)))

    (utils/eql? slot (symbol "inverse"))
    (assoc state :value (term/km-list (frame/invert-slot (:kb state) frame)))

    :else
    (slotvals-from-kb state frame slot km-int)))

(defn- frames-of
  [state frames slot km-int fail-mode]
  (cond
    (refused? state) state
    (nil? frames) (assoc state :value nil)
    (term/singleton? frames) (one-slotvals state (term/car frames) slot km-int :fail-mode fail-mode)
    :else
    (loop [frames frames
           current state
           acc []]
      (cond
        (refused? current) current
        (nil? frames) (assoc current :value (term/build-list acc nil))
        (not (term/cons? frames)) (dotted! frames)
        :else
        (let [next (km-int current
                           (term/km-list (symbol "the") slot (symbol "of") (term/car frames))
                           :fail-mode fail-mode)]
          (if (refused? next)
            next
            (recur (term/cdr frames)
                   next
                   (into acc (utils/elements (:value next))))))))))

(defn- every-headed?
  [values head?]
  (loop [values values]
    (cond
      (nil? values) true
      (not (term/cons? values)) false
      (head? (term/car values)) (recur (term/cdr values))
      :else false)))

(defn- reserved-in
  "Reserved keywords among values, in encounter order."
  [values]
  (loop [values values
         acc []]
    (cond
      (nil? values) (term/build-list acc nil)
      (not (term/cons? values)) nil
      (contains? kb/reserved-keywords (term/car values))
      (recur (term/cdr values) (conj acc (term/car values)))
      :else (recur (term/cdr values) acc))))

(defn- reject-frames
  "Nil when frames contain a reserved keyword. The error is recorded."
  [state frames]
  (when-let [hits (reserved-in frames)]
    (user-error state
                "Keyword(s) %s found where concept name(s) were expected, within a list of %s KM expressions: %s (Error = missing parentheses?)"
                (print/km-format hits)
                (or (proper-length frames) 0)
                (print/km-format frames))))

(defn- reject-slot
  "Nil when slot can be looked up. A list, a number, or a non-symbol is an error."
  [state slot]
  (cond
    (utils/lisp-list? slot)
    (user-error state
                "Non-atomic slot %s encountered! (Missing parentheses in expression?)"
                (print/km-format slot))
    (number? slot)
    (user-error state
                "Numbers can't be used as slots! (A slot named `%s' was encountered)"
                (print/km-format slot))
    (not (kb/slot-object? slot))
    (user-error state
                "Invalid slot name `%s' encountered! (Slots should be a non-nil symbol)"
                (print/km-format slot))
    :else nil))

(defn- append-of
  "Splice a sequence of sequences, or a bag of bags. A bad element is an error."
  [state frames]
  (let [outer (term/car frames)
        bag? (kb/km-bag? outer)
        elements (kb/seq-elements outer)
        good? (every-headed? elements (if bag? kb/km-bag? kb/km-seq?))]
    (if good?
      (assoc state :value
             (term/km-list (term/cons-cell (if bag? :bag :seq)
                                           (utils/mapcan-list kb/seq-elements elements))))
      (user-error state
                  "(the append of %s): value should be a %s of %s!"
                  (print/km-format outer)
                  (if bag? "bag" "sequence")
                  (if bag? "bags" "sequences")))))

(defn multi-slotvals
  "Slot values of a list of frames, including the aggregation slots.

  first, second, third, fourth, fifth, last, number, bag, and seq are
  computed from the list. unification and set-unification are passed
  back through km-int, so they wait until unification is ported.
  most-specific and most-general are refused: they need subsumption."
  [state frames slot km-int & {:keys [fail-mode] :or {fail-mode :fail}}]
  (let [frames (frame/dereference (:kb state) frames)
        rejected (or (reject-frames state frames) (reject-slot state slot))]
    (cond
      (some? rejected) rejected

      (or (utils/eql? slot (symbol "most-specific"))
          (utils/eql? slot (symbol "most-general")))
      (assoc state
             :error "not-ported"
             :message (str "This form is not ported yet: (the "
                           (print/km-format slot)
                           " of "
                           (print/km-format (kb/vals-to-val frames))
                           ").")
             :value nil)

      (contains? set-position slot)
      (let [found (position-value frames slot)]
        (assoc state :value (when (some? found) (term/km-list found))))

      (utils/eql? slot (symbol "number"))
      (assoc state :value (term/km-list (or (proper-length frames) 0)))

      (utils/eql? slot (symbol "bag"))
      (assoc state :value (term/km-list (term/cons-cell :bag frames)))

      (utils/eql? slot (symbol "seq"))
      (assoc state :value (term/km-list (term/cons-cell :seq frames)))

      (utils/eql? slot (symbol "unification"))
      (km-int state (kb/val-sets-to-expr
                     (utils/mapcan-list #(term/km-list (term/km-list %)) frames)
                     :single-valued? true)
              :fail-mode fail-mode)

      (utils/eql? slot (symbol "set-unification"))
      (km-int state (kb/val-sets-to-expr
                     (utils/mapcan-list #(term/km-list (term/km-list %)) frames))
              :fail-mode fail-mode)

      (and (contains? #{(symbol "min") (symbol "max")} slot)
           (not (term/singleton? frames)))
      (if (nil? frames)
        (user-error state
                    "(the %s of NIL): %s should be given at least one value to operate on."
                    (print/km-format slot)
                    (print/km-format slot))
        (aggregate state frames
                   (if (utils/eql? slot (symbol "min")) min max)
                   km-int false))

      (and (contains? #{(symbol "sum") (symbol "average")} slot)
           (nil? frames))
      (assoc state :value (term/km-list 0))

      (utils/eql? slot (symbol "bag2seq"))
      (if (and (term/singleton? frames) (kb/km-bag? (term/car frames)))
        (assoc state :value (term/km-list (term/cons-cell :seq (kb/seq-elements (term/car frames)))))
        (user-error state
                    "(the bag2seq of %s): argument should be a single bag."
                    (print/km-format (kb/vals-to-val frames))))

      (utils/eql? slot (symbol "seq2bag"))
      (if (and (term/singleton? frames) (kb/km-seq? (term/car frames)))
        (assoc state :value (term/km-list (term/cons-cell :bag (kb/seq-elements (term/car frames)))))
        (user-error state
                    "(the seq2bag of %s): argument should be a single seq."
                    (print/km-format (kb/vals-to-val frames))))

      (utils/eql? slot (symbol "append"))
      (cond
        (nil? frames) (assoc state :value nil)
        (and (term/singleton? frames)
             (or (kb/km-seq? (term/car frames)) (kb/km-bag? (term/car frames))))
        (append-of state frames)
        :else
        (user-error state
                    "(the append of %s): argument should be a single sequence of sequences, or bag of bags."
                    (print/km-format (kb/vals-to-val frames))))

      :else (frames-of state frames slot km-int fail-mode))))
