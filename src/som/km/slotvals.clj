(ns som.km.slotvals
  "Slot values, and the six places a slot value can come from.

  The local store and the rules inherited from classes contribute.
  Values on a slot's subslots contribute too. A prototype is cloned
  onto an ordinary instance before those are collected. An inertial
  fluent in a local situation is projected from the previous situation.
  Own facts from supersituations and visible theories are merged. The
  parent-situation value re-read stays off. A computed answer is written
  back unless the slot says not to cache, and the frame remembers that
  the slot was computed. A constraint that evaluated to nothing is put
  back, so a read does not drop it. Local and inherited constraints are
  enforced on the values just computed. A stored (no-inheritance)
  skips subslots and inherited rules. A default is evaluated once.
  The interpreter is passed in, so this namespace does not call it
  by name."
  (:require [som.km.classify :as classify]
            [som.km.errors :as errors]
            [som.km.explain :as explain]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.print :as print]
            [som.km.prototypes :as prototypes]
            [som.km.situations :as situations]
            [som.km.taxonomy :as taxonomy]
            [som.km.term :as term]
            [som.km.unify :as unify]
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
  "Local values plus facts from supersituations and visible theories.

  Own properties are used. Own definition is used when those are empty.
  Self is replaced. Comments stay, because the Lisp asks for them.
  :raw is the bound value list. :value is that list split into value
  lists. Constraints are read from :raw, not from the split lists.
  Supersituation values are included even when the local facet is empty."
  [state instance slot km-int]
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
                                  :query (:query own)))
        state (assoc state :kb (:kb defined) :query (or (:query defined) (:query state)))
        local-raw (when-let [values (:value defined)]
                    (frame/bind-self values instance))
        local-sets (when local-raw (kb/&&-exprs-to-valsets local-raw))
        inherited (situations/inherited-situation-rules state instance slot km-int)]
    (if (refused? inherited)
      inherited
      (assoc inherited
             :raw (utils/append-lists (term/km-list local-raw (:raw inherited)))
             :value (utils/remove-duplicates
                     (utils/remove-items nil
                                         (utils/append-lists
                                          (term/km-list local-sets (:value inherited))))
                     :test utils/equal?
                     :from-end? false)))))

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

(defn- narrowed
  "Drop a subsuming or subsumed class when the slot asks for that."
  [kb slot values]
  (cond
    (frame/remove-subsumers-slot? kb slot)
    (taxonomy/remove-subsumers kb values)
    (frame/remove-subsumees-slot? kb slot)
    (taxonomy/remove-subsumees kb values)
    :else {:kb kb :value values}))

(defn- with-constraints
  "Store values with their constraints and return the values alone."
  [state instance slot values constraints]
  (let [kept (reattach (:kb state) slot values constraints)
        stored (put-local state instance slot kept)]
    (assoc stored :value values)))

(defn- remember
  "Record the slot as computed when the answer is cached."
  [state instance slot]
  (if (or (refused? state)
          (not (caches? (:kb state) slot))
          (not (kb/kb-object? instance)))
    state
    (assoc state :kb
           (frame/note-done (:kb state) instance slot
                            (frame/target-situation
                             (:kb state)
                             (frame/current-situation (:kb state))
                             instance slot)))))

(defn- after-constraints
  "Enforce constraints, store the values with the local constraints, and
  remember the slot.

  reattach is put back on the stored values. constraints are the ones
  that are checked. An empty value list is left alone while filler
  creation is off. sometimes answers the symbol t, and that symbol is
  not a value list."
  [state instance slot values constraints reattach km-int]
  (let [finish (fn [state values reattach]
                 (remember (with-constraints state instance slot values reattach)
                           instance slot))]
    (cond
      (refused? state) state
      (or (nil? constraints)
          (and (nil? values) (zero? unify/max-padding-instances)))
      (finish state values reattach)
      :else
      (let [target (term/km-list (symbol "the") slot (symbol "of") instance)
            enforced (unify/enforce-constraints state values constraints km-int
                                                :target target)]
        (cond
          (refused? enforced) enforced
          (not (or (nil? (:value enforced)) (term/cons? (:value enforced))))
          (finish enforced values reattach)
          :else
          (let [fit (narrowed (:kb enforced) slot (:value enforced))]
            (finish (assoc enforced :kb (:kb fit)) (:value fit) reattach)))))))

(defn- use-inheritance?
  [kb]
  (nil? (:curr-prototype (:runtime kb))))

(defn- flag-stored?
  [kb slot flag]
  (and (term/lisp-symbol? slot)
       (kb/kb-object? slot)
       (some? (:value (frame/get-vals kb slot flag
                                      :situation term/global-situation
                                      :dereference? false)))))

(defn- inherit-with-overrides?
  [kb slot]
  (or (flag-stored? kb slot (symbol "inherit-with-overrides"))
      (flag-stored? kb slot (symbol "simple-inherit-with-overrides"))))

(defn- simple-inherit-with-overrides?
  [kb slot]
  (flag-stored? kb slot (symbol "simple-inherit-with-overrides")))

(defn- list-each
  [values]
  (loop [values values
         acc []]
    (cond
      (nil? values) (term/build-list acc nil)
      (not (term/cons? values)) (dotted! values)
      :else (recur (term/cdr values) (conj acc (term/km-list (term/car values)))))))

(defn- rule-sets-in-situation
  "Member rules for one class, as a list of value lists.

  Both member facets are read. A single-valued slot splits & and wraps
  each value. A multivalued slot splits &&. Two empty facets stay empty:
  &&-exprs-to-valsets of nil would be a list holding nil."
  [kb class slot situation]
  (let [member (frame/get-vals kb class slot
                               :facet (symbol "member-properties")
                               :situation situation
                               :dereference? false)
        defined (frame/get-vals (:kb member) class slot
                                :facet (symbol "member-definition")
                                :situation situation
                                :dereference? false)
        kb (:kb defined)]
    (if (frame/single-valued-slot? kb slot)
      (let [pieces (utils/append-lists
                    (term/km-list (kb/&-expr-to-vals (:value member))
                                  (kb/&-expr-to-vals (:value defined))))
            unique (utils/remove-duplicates pieces :test utils/equal? :from-end? true)]
        {:kb kb :value (list-each unique)})
      (if (and (nil? (:value member)) (nil? (:value defined)))
        {:kb kb :value nil}
        {:kb kb
         :value (utils/append-lists
                 (term/km-list (when (some? (:value member))
                                 (kb/&&-exprs-to-valsets (:value member)))
                               (when (some? (:value defined))
                                 (kb/&&-exprs-to-valsets (:value defined)))))}))))

(defn- pairs-for-classes
  [kb slot classes]
  (loop [classes classes
         kb kb
         acc []]
    (if (nil? classes)
      {:kb kb :value (term/build-list acc nil)}
      (let [found (rule-sets-in-situation kb (term/car classes) slot
                                          term/global-situation)
            cleaned (utils/remove-duplicates (utils/remove-items nil (:value found))
                                             :test utils/equal?)]
        (recur (term/cdr classes)
               (:kb found)
               (if (some? cleaned)
                 (conj acc (term/km-list cleaned (term/car classes)))
                 acc))))))

(defn- first-rules
  [pairs]
  (when (and (term/cons? pairs) (term/cons? (term/car pairs)))
    (term/car (term/car pairs))))

(defn- substantive-sets?
  [rule-sets]
  (loop [sets rule-sets]
    (cond
      (nil? sets) false
      (not (term/cons? sets)) false
      (loop [rules (term/car sets)]
        (cond
          (nil? rules) false
          (not (term/cons? rules)) false
          (not (kb/constraint-expr? (term/car rules))) true
          :else (recur (term/cdr rules))))
      true
      :else (recur (term/cdr sets)))))

(defn- override-pairs
  "Rules on class, or on the classes above it when class has none.

  A value that is not a constraint stops that branch. Thing does not
  climb any further."
  [kb slot class]
  (let [here (pairs-for-classes kb slot (term/km-list class))]
    (if (substantive-sets? (first-rules (:value here)))
      here
      (if (utils/eql? class (symbol "Thing"))
        {:kb (:kb here) :value nil}
        (let [supers (taxonomy/immediate-superclasses (:kb here) class)]
          (loop [rest (:value supers)
                 kb (:kb supers)
                 acc nil]
            (if (nil? rest)
              {:kb kb :value acc}
              (let [deeper (override-pairs kb slot (term/car rest))]
                (recur (term/cdr rest)
                       (:kb deeper)
                       (utils/append-lists
                        (term/km-list acc (:value deeper))))))))))))

(defn- strip-pairs
  [pairs instance]
  (let [lists (loop [pairs pairs
                     acc []]
                (cond
                  (nil? pairs) (term/build-list acc nil)
                  (not (term/cons? pairs)) (dotted! pairs)
                  :else (recur (term/cdr pairs)
                               (conj acc (term/car (term/car pairs))))))]
    (frame/bind-self
     (utils/remove-duplicates (utils/append-lists lists)
                              :test utils/equal?
                              :from-end? true)
     instance)))

(defn- collapse-appending
  [kb slot rules]
  (if-not (and (some? rules) (frame/appending-slot? kb slot))
    rules
    (let [flat (utils/append-lists rules)]
      (when (some? flat) (term/km-list flat)))))

(defn- constraints-of
  [rules]
  (loop [rules rules
         acc nil]
    (if (or (nil? rules) (not (term/cons? rules)))
      acc
      (recur (term/cdr rules)
             (utils/append-lists
              (term/km-list acc (constraint-walk (term/car rules) :plural)))))))

(defn- every-frame?
  [values]
  (loop [values values]
    (cond
      (nil? values) true
      (not (term/cons? values)) false
      (kb/kb-object? (term/car values)) (recur (term/cdr values))
      :else false)))

(defn- stored-classes
  [kb instance]
  (when (kb/kb-object? instance)
    (let [defined (when (frame/are-some? kb :definitions)
                    (:value (frame/get-vals kb instance (symbol "instance-of")
                                            :facet (symbol "own-definition")
                                            :situation term/global-situation)))
          own (:value (frame/get-vals kb instance (symbol "instance-of")
                                      :situation term/global-situation))]
      (utils/append-lists (term/km-list defined own)))))

(defn- evaluated-immediate-classes
  "The classes of instance. A stored frame is used as it is.

  An instance-of value that is not a frame is evaluated, the classes
  are tidied, and the result is written back. A number, a string, and
  a frame with nothing stored use immediate-classes."
  [state instance km-int]
  (let [stored (stored-classes (:kb state) instance)]
    (if (or (not (kb/kb-object? instance))
            (nil? stored)
            (every-frame? stored))
      (let [found (taxonomy/immediate-classes (:kb state) instance)]
        (assoc state :kb (:kb found) :value (:value found)))
      (let [target (term/km-list (symbol "the") (symbol "instance-of")
                                 (symbol "of") instance)
            evaluated (km-int state (kb/vals-to-val stored) :target target)]
        (if (refused? evaluated)
          evaluated
          (let [tidy (taxonomy/remove-subsumers (:kb evaluated) (:value evaluated))
                written (frame/put-vals (:kb tidy) instance (symbol "instance-of")
                                        (:value tidy)
                                        :situation term/global-situation
                                        :query (:query evaluated))]
            (assoc evaluated
                   :kb (:kb written)
                   :query (:query written)
                   :value (:value tidy))))))))

(defn- class-chain
  "Thing and the classes of instance, including the classes above them."
  [state instance km-int]
  (let [imm (evaluated-immediate-classes state instance km-int)]
    (if (refused? imm)
      imm
      (let [walked (utils/mapcan-list
                    (fn [class]
                      (:value (taxonomy/all-superclasses0 (:kb imm) class)))
                    (:value imm))]
        (assoc imm :value
               (term/cons-cell (symbol "Thing")
                               (utils/remove-duplicates walked :test utils/eql?)))))))

(defn- rules-from-classes
  [state instance slot classes]
  (let [pairs (pairs-for-classes (:kb state) slot classes)
        rules (collapse-appending (:kb pairs) slot
                                  (strip-pairs (:value pairs) instance))]
    {:state (assoc state :kb (:kb pairs)) :rules rules}))

(defn- rules-with-overrides
  [state instance slot km-int]
  (let [classes (evaluated-immediate-classes state instance km-int)]
    (if (refused? classes)
      classes
      (let [climbed (loop [rest (:value classes)
                           kb (:kb classes)
                           acc nil]
                      (if (nil? rest)
                        {:kb kb :value acc}
                        (let [deeper (override-pairs kb slot (term/car rest))]
                          (recur (term/cdr rest)
                                 (:kb deeper)
                                 (utils/append-lists
                                  (term/km-list acc (:value deeper)))))))
            rules (collapse-appending (:kb climbed) slot
                                      (strip-pairs (:value climbed) instance))]
        {:state (assoc classes :kb (:kb climbed)) :rules rules}))))

(defn- inherited-rules
  "The member rules that apply to instance, with Self replaced.

  ignore-overrides? climbs every class, so a constraint above a stopping
  class is still found. Situations other than *Global are not read.
  :rules is a list of value lists. A refusal is returned as a state."
  [state instance slot km-int ignore-overrides?]
  (cond
    (not (use-inheritance? (:kb state))) {:state state :rules nil}
    (and (inherit-with-overrides? (:kb state) slot) (not ignore-overrides?))
    (rules-with-overrides state instance slot km-int)
    :else
    (let [classes (class-chain state instance km-int)]
      (if (refused? classes)
        classes
        (rules-from-classes classes instance slot (:value classes))))))

(defn- default-sets
  [own-sets]
  (loop [sets own-sets
         acc []]
    (cond
      (nil? sets) (term/build-list acc nil)
      (not (term/cons? sets)) (dotted! sets)
      :else
      (let [defaults (loop [rules (term/car sets)
                            kept []]
                       (cond
                         (nil? rules) (term/build-list kept nil)
                         (not (term/cons? rules)) (dotted! rules)
                         (kb/km-default? (term/car rules))
                         (recur (term/cdr rules) (conj kept (term/car rules)))
                         :else (recur (term/cdr rules) kept)))]
        (recur (term/cdr sets)
               (if (some? defaults) (conj acc defaults) acc))))))

(defn- no-inheritance?
  "True when constraints contain (no-inheritance).

  The Lisp also requires *use-no-inheritance-flag*, which starts nil
  and is never set. A stored constraint is honored here, so the flag
  changes the read. Comments are stripped before the comparison."
  [constraints]
  (let [marker (term/km-list (symbol "no-inheritance"))]
    (loop [constraints constraints]
      (cond
        (nil? constraints) false
        (not (term/cons? constraints)) false
        (utils/equal? (explain/desource-decomment (term/car constraints)) marker)
        true
        :else (recur (term/cdr constraints))))))

(defn- consistent-default-vals
  [state vals curr-vals constraints slot km-int]
  (let [constraints (frame/dereference (:kb state) constraints)]
    (loop [vals vals
           state state
           acc []]
      (cond
        (refused? state) state
        (nil? vals) (assoc state :value (term/build-list acc nil))
        (not (term/cons? vals)) (dotted! vals)
        :else
        (let [val (term/car vals)
              combined (utils/append-lists (term/km-list curr-vals (term/km-list val)))
              hit (unify/test-constraints state combined constraints km-int
                                          :slot slot :mode :consistent)]
          (cond
            (refused? hit) hit
            (:value hit) (recur (term/cdr vals) hit (conj acc val))
            :else (recur (term/cdr vals) hit acc)))))))

(defn- default-body-vals
  "The values of one (:default expr), or nil when they do not fit.

  A single-valued clash with the intermediate values drops the whole
  body. Any other value is kept only when it is consistent with the
  constraints. The body is not sent back through the handler that
  only records the flag."
  [state expr curr-vals constraints slot single? km-int]
  (let [evaluated (km-int state (nth-value expr 1))]
    (if (refused? evaluated)
      evaluated
      (if (and single? (some? curr-vals) (some? (:value evaluated)))
        (let [probe (km-int evaluated
                            (term/km-list (term/car curr-vals)
                                          (symbol "&?")
                                          (term/car (:value evaluated))))]
          (cond
            (refused? probe) probe
            (nil? (:value probe)) (assoc probe :value nil)
            :else (consistent-default-vals probe (:value evaluated) curr-vals
                                           constraints slot km-int)))
        (consistent-default-vals evaluated (:value evaluated) curr-vals
                                 constraints slot km-int)))))

(defn- expr-set-has-default?
  [exprs]
  (loop [exprs exprs]
    (cond
      (nil? exprs) false
      (not (term/cons? exprs)) false
      (kb/km-default? (term/car exprs)) true
      :else (recur (term/cdr exprs)))))

(defn- rewrite-default-set
  [state exprs curr-vals constraints slot single? km-int]
  (if-not (expr-set-has-default? exprs)
    {:state state :set exprs}
    (loop [exprs exprs
           state state
           acc []]
      (cond
        (refused? state) {:state state :set nil}
        (nil? exprs) {:state state :set (term/build-list acc nil)}
        (not (term/cons? exprs)) (dotted! exprs)
        (kb/km-default? (term/car exprs))
        (let [filtered (default-body-vals state (term/car exprs) curr-vals
                                          constraints slot single? km-int)]
          (if (refused? filtered)
            {:state filtered :set nil}
            (recur (term/cdr exprs)
                   filtered
                   (into acc (utils/elements (:value filtered))))))
        :else (recur (term/cdr exprs) state (conj acc (term/car exprs)))))))

(defn- filter-defaults
  "Replace each (:default expr) with the values its body produces.

  An expr-set with no default is left as it is. :rules is the list of
  expr-sets. :value is the intermediate values the caller already has."
  [state rule-sets curr-vals constraints slot single? km-int]
  (loop [sets rule-sets
         state state
         acc []]
    (cond
      (refused? state) state
      (nil? sets) (assoc state :rules (term/build-list acc nil) :value curr-vals)
      (not (term/cons? sets)) (dotted! sets)
      :else
      (let [rewritten (rewrite-default-set state (term/car sets) curr-vals
                                           constraints slot single? km-int)]
        (if (refused? (:state rewritten))
          (:state rewritten)
          (recur (term/cdr sets) (:state rewritten) (conj acc (:set rewritten))))))))

(defn- rules-for-fold
  "Inherited rules, with defaults replaced by the values they produce.

  A stored (no-inheritance) contributes no rules, so the fold and the
  recursive retry see none. The Lisp also gates that skip on
  *use-no-inheritance-flag*, which starts nil. The stored constraint
  is enough here. A default body is evaluated once against the
  intermediate values."
  [state inherited-rules own-value curr-vals constraints slot single? no-inh? km-int]
  (cond
    no-inh? (assoc state :rules nil :value curr-vals)
    (frame/are-some? (:kb state) :defaults)
    (filter-defaults state
                     (utils/append-lists
                      (term/km-list (default-sets own-value) inherited-rules))
                     curr-vals constraints slot single? km-int)
    :else (assoc state :rules inherited-rules :value curr-vals)))

(defn- subslot-values
  "The values of slot's immediate subslots, as one value list.

  Several subslots are one (:set ...) expression. The caller skips
  this read when (no-inheritance) is stored."
  [state instance slot target km-int]
  (let [subs (taxonomy/immediate-subslots (:kb state) slot)]
    (if (nil? (:value subs))
      (assoc state :kb (:kb subs) :value nil)
      (let [exprs (loop [rest (:value subs)
                         acc []]
                    (if (nil? rest)
                      (term/build-list acc nil)
                      (recur (term/cdr rest)
                             (conj acc
                                   (term/km-list
                                    (symbol "the") (term/car rest) (symbol "of") instance
                                    (term/km-list (symbol "comm")
                                                  (symbol "[subslot-reasoning]")
                                                  (symbol "Self")
                                                  (term/car rest)))))))
            evaluated (km-int (assoc state :kb (:kb subs))
                              (kb/vals-to-val exprs)
                              :target target)]
        evaluated))))

(defn- local-values
  [state own single? appending? target km-int]
  (cond
    (or (nil? own) (nil? (:value own))) (assoc state :value nil)
    (simple-local? (:kb state) (:value own))
    (assoc state :value (term/car (:value own)))
    :else
    (let [expr (kb/val-sets-to-expr (:value own)
                                    :single-valued? single?
                                    :combine-values-by-appending? appending?)]
      (if (nil? expr)
        (assoc state :value nil)
        (km-int state expr :target target)))))

(defn- intermediate
  "Combine the value lists found so far and store them before the rules.

  A multivalued slot puts projected values first, then subslot values,
  then local values. A single-valued slot leaves the projected values
  out until the rules have run. One list is stored after the at-most-1
  and exactly-1 check. Several lists are evaluated together, then that
  same check runs."
  [state projected-vals local-vals sub-vals single? appending? instance slot target km-int constraints]
  (let [sets (utils/remove-duplicates
              (utils/remove-items nil (if single?
                                       (term/km-list sub-vals local-vals)
                                       (term/km-list projected-vals sub-vals local-vals)))
              :test utils/equal?)]
    (cond
      (nil? sets) (assoc state :value nil)
      (term/singleton? sets)
      (let [enforced (unify/enforce-set-constraints
                      state (utils/remove-items :incomplete (term/car sets))
                      constraints km-int :target target)]
        (if (refused? enforced)
          enforced
          (assoc (put-local enforced instance slot (:value enforced))
                 :value (:value enforced))))
      :else
      (let [expr (kb/val-sets-to-expr sets
                                      :single-valued? single?
                                      :combine-values-by-appending? appending?)
            evaluated (if (nil? expr)
                       (assoc state :value nil)
                       (km-int state expr :target target))]
        (cond
          (refused? evaluated) evaluated
          (nil? (:value evaluated)) evaluated
          :else
          (let [enforced (unify/enforce-set-constraints
                          evaluated (:value evaluated) constraints km-int
                          :target target)]
            (if (refused? enforced)
              enforced
              (assoc (put-local enforced instance slot (:value enforced))
                     :value (:value enforced)))))))))

(defn- constraints-hold?
  [state vals constraints slot km-int]
  (or (nil? constraints)
      (let [filtered (unify/filter-using-constraints state vals constraints km-int
                                                     :slot slot)]
        (and (not (refused? filtered))
             (utils/equal? (:value filtered) vals)))))

(defn- combine-overrides
  [state vals rules single? target km-int constraints slot]
  (if single?
    (let [loc (km-int state (kb/vals-to-&-expr vals) :target target)
          expr (kb/val-sets-to-expr rules :single-valued? true)]
      (cond
        (refused? loc) loc
        (nil? expr) (assoc loc :value (:value loc))
        :else
        (let [trial (km-int loc (term/km-list (:value loc) (symbol "&?") expr))]
          (cond
            (refused? trial) trial
            (some? (:value trial))
            (km-int trial (term/km-list (:value loc) (symbol "&") expr) :target target)
            :else (assoc trial :value (:value loc))))))
    (let [loc (km-int state (kb/val-sets-to-expr (term/km-list vals)) :target target)]
      (if (refused? loc)
        loc
        (let [expr (kb/val-sets-to-expr (term/cons-cell (:value loc) rules))
              combined (if (nil? expr)
                         (assoc loc :value (:value loc))
                         (km-int loc expr :target target))]
          (cond
            (refused? combined) combined
            (constraints-hold? combined (:value combined) constraints slot km-int)
            combined
            :else (assoc combined :value (:value loc))))))))

(defn- fold-rules
  [state vals rules single? appending? slot target km-int constraints]
  (cond
    (not (use-inheritance? (:kb state))) (assoc state :value vals)
    (nil? rules) (assoc state :value vals)
    (and (some? vals) (simple-inherit-with-overrides? (:kb state) slot))
    (assoc state :value vals)
    (and (some? vals) (inherit-with-overrides? (:kb state) slot))
    (combine-overrides state vals rules single? target km-int constraints slot)
    :else
    (let [expr (kb/val-sets-to-expr (term/cons-cell vals rules)
                                    :single-valued? single?
                                    :combine-values-by-appending? appending?)]
      (if (nil? expr)
        (assoc state :value vals)
        (km-int state expr :target target)))))

(defn- flatten-atoms
  [expr]
  (cond
    (nil? expr) []
    (term/cons? expr)
    (into (flatten-atoms (term/car expr)) (flatten-atoms (term/cdr expr)))
    :else [expr]))

(defn- contains-subseq?
  [hay needle]
  (let [n (count needle)
        m (count hay)
        needle (vec needle)]
    (and (pos? n)
         (<= n m)
         (loop [index 0]
           (cond
             (> index (- m n)) false
             (= (subvec hay index (+ index n)) needle) true
             :else (recur (inc index)))))))

(defn- recursive-ruleset?
  [instance slot ruleset]
  (contains-subseq? (flatten-atoms ruleset) [slot (symbol "of") instance]))

(defn- retry-recursive
  [state vals rules single? appending? instance slot target km-int]
  (if (or (nil? rules)
          (not (use-inheritance? (:kb state)))
          (not (caches? (:kb state) slot))
          (not (loop [rules rules]
                 (cond
                   (nil? rules) false
                   (not (term/cons? rules)) false
                   (recursive-ruleset? instance slot (term/car rules)) true
                   :else (recur (term/cdr rules))))))
    (assoc state :value vals)
    (let [stored (put-local (assoc state :value vals) instance slot vals)
          expr (kb/val-sets-to-expr (term/cons-cell vals rules)
                                    :single-valued? single?
                                    :combine-values-by-appending? appending?)]
      (if (nil? expr)
        (assoc stored :value vals)
        (km-int stored expr :target target)))))

(defn- collected-rules
  [state instance slot own km-int]
  (let [primary (inherited-rules state instance slot km-int false)]
    (cond
      (refused? primary) primary
      (inherit-with-overrides? (:kb (:state primary)) slot)
      (let [full (inherited-rules (:state primary) instance slot km-int true)]
        (if (refused? full)
          full
          {:state (:state full)
           :rules (:rules primary)
           :constraints (constraints-of (:rules full))}))
      :else
      {:state (:state primary)
       :rules (:rules primary)
       :constraints (constraints-of (:rules primary))})))

(defn- prototypes-first
  "Clone suitable prototypes, then warn about a protoinstance.

  A refusal is returned as it is. The warning leaves the answer alone.
  A slot that is not cloned, and a knowledge base with no prototypes,
  skip the clone. Querying a protoinstance outside prototype mode
  records the Lisp sentence and continues."
  [state instance slot km-int]
  (let [state (if (and (frame/are-some? (:kb state) :prototypes)
                       (prototypes/clones-for? slot)
                       (frame/use-prototypes? (:kb state))
                       (not (frame/protoinstance? (:kb state) instance)))
                (prototypes/unify-in-prototypes state instance slot km-int)
                state)]
    (if (refused? state)
      state
      (let [instance (frame/dereference (:kb state) instance)]
        (if (and (frame/protoinstance? (:kb state) instance)
                 (nil? (frame/curr-prototype (:kb state))))
          (errors/report-error
           state :user-error
           "Attempt to query a protoinstance %s when not in prototype mode!%n         Doing (the %s of %s)%n"
           (print/km-format instance)
           (print/km-format slot)
           (print/km-format instance))
          state)))))

(defn- km-length
  [value]
  (loop [value value
         seen 0]
    (cond
      (nil? value) seen
      (term/cons? value) (recur (term/cdr value) (inc seen))
      :else seen)))

(defn- add-text
  [state text]
  (assoc state :text (str (:text state) text)))

(defn- record-projected
  [state instance slot values prev]
  (if (or (nil? values) (nil? prev))
    state
    (loop [pending values
           kb (:kb state)]
      (if (or (nil? pending) (not (term/cons? pending)))
        (assoc state :kb kb)
        (let [recorded (frame/record-explanation-for
                        kb
                        (term/km-list (symbol "the") slot (symbol "of") instance)
                        (term/car pending)
                        (term/km-list (symbol "projected-from") prev))]
          (recur (term/cdr pending) (:kb recorded)))))))

(defn- project-from-prev
  "Values an inertial fluent keeps from the previous situation.

  :values is nil when projection does not apply. A refusal from the
  previous-situation read is returned as :state."
  [state instance slot constraints km-int]
  (if-not (and (frame/local-situation? (:kb state))
               (frame/inertial-fluent? (:kb state) slot))
    {:state state :values nil :prev nil}
    (let [prev (situations/previous state km-int)]
      (cond
        (refused? prev) {:state prev :values nil :prev nil}
        (nil? (:value prev)) {:state prev :values nil :prev nil}
        :else
        (let [read (km-int prev
                           (term/km-list (symbol "in-situation")
                                         (:value prev)
                                         (term/km-list (symbol "the") slot
                                                       (symbol "of") instance)))]
          (cond
            (refused? read) {:state read :values nil :prev (:value prev)}
            (nil? constraints)
            {:state read :values (:value read) :prev (:value prev)}
            :else
            (let [filtered (unify/filter-using-constraints
                            read (:value read) constraints km-int :slot slot)]
              {:state filtered
               :values (when-not (refused? filtered) (:value filtered))
               :prev (:value prev)})))))))

(defn- maybe-project
  "The one projected value to keep, or nil when the local list stands.

  Equal lists return the first value and do not report a multiple-value
  error. Two or more projected values, or two or more local values,
  record the ERROR! sentences and keep the first. A failed unification
  keeps the local list and the knowledge base the unification returned."
  [state projected local slot instance km-int]
  (cond
    (nil? projected) {:state state :kept nil}
    (utils/equal? projected local) {:state state :kept (term/car projected)}
    :else
    (let [state (if (>= (km-length projected) 2)
                  (add-text state
                            (str "ERROR! Projected multiple values "
                                 (print/km-format projected)
                                 " for the single-valued slot `"
                                 (print/km-format slot)
                                 "' on instance "
                                 (print/km-format instance)
                                 "!\nERROR! Discarding all but the first value ("
                                 (print/km-format (term/car projected))
                                 ")...\n"))
                  state)
          state (if (>= (km-length local) 2)
                  (add-text state
                            (str "ERROR! Found multiple values "
                                 (print/km-format local)
                                 " for the single-valued slot `"
                                 (print/km-format slot)
                                 "' on instance "
                                 (print/km-format instance)
                                 "!\nERROR! Discarding all but the first value ("
                                 (print/km-format (term/car local))
                                 ")...\n"))
                  state)
          projected-value (term/car projected)
          local-value (when (term/cons? local) (term/car local))]
      (if (nil? local-value)
        {:state state :kept projected-value}
        (let [unified (unify/lazy-unify-exprs state projected-value local-value km-int)]
          {:state unified :kept (:value unified)})))))

(defn slotvals-from-kb
  "The values of one slot from prototypes, the local store, subslots, and classes.

  A suitable prototype is cloned before the instance's own values and
  the class rules are collected. km-int is called as (km-int state expr
  :target target). A refusal is returned unchanged and is not recorded
  as done. An inertial fluent in a local situation is projected from
  the previous situation. Own facts from supersituations and visible
  theories are merged before that. The answer is stored before the
  class rules are applied, then stored again with the local constraints."
  [state instance slot km-int & {:keys [target]}]
  (let [instance (frame/dereference (:kb state) instance)
        state (prototypes-first state instance slot km-int)]
    (if (refused? state)
      state
      (let [instance (frame/dereference (:kb state) instance)
            target (or target (term/km-list (symbol "the") slot (symbol "of") instance))
            own (own-rules state instance slot km-int)]
        (if (refused? own)
          own
          (let [raw (:raw own)
                own-value (:value own)
                state (dissoc own :raw)
                single? (frame/single-valued-slot? (:kb state) slot)
                appending? (frame/appending-slot? (:kb state) slot)
                own-constraints (constraint-walk raw :plural)
                inherited (collected-rules state instance slot own km-int)]
            (if (refused? inherited)
              inherited
              (let [state (:state inherited)
                    inherited-rules (:rules inherited)
                    constraints (utils/append-lists
                                 (term/km-list (:constraints inherited) own-constraints))
                    no-inh? (no-inheritance? constraints)
                    projected (project-from-prev state instance slot constraints km-int)]
                (if (refused? (:state projected))
                  (:state projected)
                  (let [state (:state projected)
                        prev (:prev projected)
                        projected-vals (:values projected)
                        sub (if no-inh?
                              (assoc state :value nil)
                              (subslot-values state instance slot target km-int))]
                    (if (refused? sub)
                      sub
                      (let [local (local-values sub (assoc state :value own-value)
                                               single? appending? target km-int)]
                        (if (refused? local)
                          local
                          (let [recorded (if single?
                                           local
                                           (record-projected local instance slot
                                                             projected-vals prev))
                                mid (intermediate recorded
                                                  (when-not single? projected-vals)
                                                  (:value local)
                                                  (:value sub)
                                                  single? appending? instance slot target
                                                  km-int constraints)]
                            (if (refused? mid)
                              mid
                              (let [ruled (rules-for-fold mid inherited-rules own-value
                                                          (:value mid) constraints slot
                                                          single? no-inh? km-int)]
                                (if (refused? ruled)
                                  ruled
                                  (let [folded (fold-rules ruled (:value ruled)
                                                           (:rules ruled) single? appending?
                                                           slot target km-int constraints)]
                                    (if (refused? folded)
                                      folded
                                      (let [retried (retry-recursive folded (:value folded)
                                                                     (:rules ruled)
                                                                     single? appending? instance
                                                                     slot target km-int)]
                                    (if (refused? retried)
                                      retried
                                      (if-not single?
                                        (after-constraints retried instance slot (:value retried)
                                                           constraints own-constraints km-int)
                                        (let [chosen (maybe-project retried projected-vals
                                                                    (:value retried)
                                                                    slot instance km-int)]
                                          (cond
                                            (refused? (:state chosen)) (:state chosen)
                                            (nil? (:kept chosen))
                                            (after-constraints (:state chosen) instance slot
                                                               (:value retried)
                                                               constraints own-constraints km-int)
                                            :else
                                            (let [recorded (record-projected
                                                            (:state chosen) instance slot
                                                            (term/km-list (:kept chosen)) prev)]
                                              (after-constraints recorded instance slot
                                                                 (term/km-list (:kept chosen))
                                                                 constraints own-constraints
                                                                 km-int))))))))))))))))))))))))))

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

(defn- user-error
  "Record a user error. The template uses %s and the arguments are already text.

  The answer is nil. Nothing is printed. :abort throws before that."
  [state template & args]
  (-> (apply errors/report-error state :user-error template args)
      (assoc :value nil)))

(defn- drop-matching
  [value pred]
  (loop [value value
         acc []]
    (cond
      (nil? value) (term/build-list acc nil)
      (not (term/cons? value)) value
      (pred (term/car value)) (recur (term/cdr value) acc)
      :else (recur (term/cdr value) (conj acc (term/car value))))))

(defn- without-constraints
  "Values with constraint expressions removed.

  When no constraint has been seen, the values are returned unchanged.
  A singleton (& ...) list is split before the constraints are dropped."
  [kb values]
  (cond
    (not (frame/are-some? kb :constraints)) values
    (nil? values) nil
    (and (term/singleton? values)
         (term/cons? (term/car values))
         (kb/val-unification-operator? (nth-value (term/car values) 1)))
    (drop-matching (kb/&-expr-to-vals (term/car values)) kb/constraint-expr?)
    :else (drop-matching values kb/constraint-expr?)))

(defn cached-situation-lookup
  "A slot already computed in the current situation, read in another.

  :hit is true when frame and slot are done in the current situation's
  target. The values are then read in the target of situation. The
  current situation is not changed. A done slot whose stored value is
  nil is still a hit. A miss returns the class test's knowledge base."
  [state situation frame slot]
  (let [classed (taxonomy/isa? (:kb state) situation (symbol "Situation"))]
    (if-not (and (kb/kb-object? situation) (:value classed))
      {:hit false :state (assoc state :kb (:kb classed))}
      (let [kb (:kb classed)
            current-target (frame/target-situation kb
                                                    (frame/current-situation kb)
                                                    frame slot)
            passed-target (frame/target-situation kb situation frame slot)]
        (if-not (frame/already-done? kb frame slot current-target)
          {:hit false :state (assoc state :kb kb)}
          (let [found (frame/get-vals kb frame slot
                                      :situation passed-target
                                      :query (:query state))]
            {:hit true
             :state (assoc state
                           :kb (:kb found)
                           :query (or (:query found) (:query state))
                           :value (without-constraints (:kb found)
                                                       (:value found)))}))))))

(defn- situations-mode-error
  [state frame slot]
  (user-error state
              (str "Attempt to call (the %s of %s) in the global situation!%n"
                   "(Not allowed, as `%s' is a fluent and you're using KM's situation mechanism).%n"
                   "DEBUGGING HINTS:%n"
                   " * IF you issued your query for the `%s' slot from the global situation%n"
                   "   THEN you shouldn't do this! You should only issue queries for a fluent slot from%n"
                   "        within a situation, not from the global KB.%n"
                   "   SOLUTIONS:%n"
                   "     (i) Enter a situation by%n"
                   "		KM> (new-situation)%n"
                   "	 then reissue your query, or%n"
                   "    (ii) Declare the `%s' slot as a non-fluent (i.e. with time-independent values), by%n"
                   "	        KM> (%s has (fluent-status (*Non-Fluent)))")
              (print/km-format slot)
              (print/km-format frame)
              (print/km-format slot)
              (print/km-format slot)
              (print/km-format slot)
              (print/km-format slot)))

(defn- class-slot
  "instance-of, classes, and all-classes, or nil for any other slot.

  instance-of and classes are the immediate classes, with a superclass
  removed. all-classes adds Thing and the classes above. A stored
  expression is evaluated. A refusal is returned as a state."
  [state frame slot km-int]
  (cond
    (contains? #{(symbol "instance-of") (symbol "classes")} slot)
    (let [found (evaluated-immediate-classes state frame km-int)]
      (if (refused? found)
        found
        (let [tidy (taxonomy/remove-subsumers (:kb found) (:value found))]
          (assoc found :kb (:kb tidy) :value (:value tidy)))))
    (utils/eql? slot (symbol "all-classes"))
    (class-chain state frame km-int)
    :else nil))

(defn- tidy-classes
  [kb slot values]
  (cond
    (frame/remove-subsumers-slot? kb slot)
    (taxonomy/remove-subsumers kb values)
    (frame/remove-subsumees-slot? kb slot)
    (taxonomy/remove-subsumees kb values)
    :else {:kb kb :value values}))

(defn- class-walk
  "A computed class or subslot walk, or nil when slot is an ordinary slot.

  superclasses and subclasses are the immediate walks, with a more
  general or more specific class removed. instances, subslots, and
  superslots stay ordinary lookups, so a stored list is left as it
  was stored."
  [state frame slot]
  (let [walked (cond
                 (utils/eql? slot (symbol "superclasses"))
                 (let [found (taxonomy/immediate-superclasses (:kb state) frame)]
                   (tidy-classes (:kb found) slot (:value found)))
                 (utils/eql? slot (symbol "subclasses"))
                 (let [found (taxonomy/immediate-subclasses (:kb state) frame)]
                   (tidy-classes (:kb found) slot (:value found)))
                 (utils/eql? slot (symbol "all-superclasses"))
                 (taxonomy/all-superclasses (:kb state) frame)
                 (utils/eql? slot (symbol "all-subclasses"))
                 (taxonomy/all-subclasses (:kb state) frame)
                 (utils/eql? slot (symbol "all-instances"))
                 (taxonomy/all-instances (:kb state) frame)
                 (utils/eql? slot (symbol "all-subslots"))
                 (taxonomy/all-subslots (:kb state) frame)
                 (utils/eql? slot (symbol "all-superslots"))
                 (taxonomy/all-superslots (:kb state) frame)
                 :else nil)]
    (when walked
      (assoc state :kb (:kb walked) :value (:value walked)))))

(defn- cached-answer
  "The values recorded for a slot that has already been computed.

  Nil when the frame has no such record. Constraints are not part of
  the cached answer."
  [state frame slot]
  (let [situation (frame/target-situation (:kb state)
                                          (frame/current-situation (:kb state))
                                          frame slot)]
    (when (frame/already-done? (:kb state) frame slot situation)
      (let [cached (frame/get-vals (:kb state) frame slot
                                   :situation situation
                                   :query (:query state))]
        (assoc state
               :kb (:kb cached)
               :query (or (:query cached) (:query state))
               :value (without-constraints (:kb cached) (:value cached)))))))

(defn one-slotvals
  "The values of slot on one frame.

  Arithmetic slots, bags, sequences, and :args are computed here.
  instance-of, classes, and all-classes are computed before a
  non-object is rejected. all-superclasses, all-subclasses,
  all-instances, all-subslots, and all-superslots are computed for a
  knowledge-base object. superclasses and subclasses are the immediate
  walks. instances, subslots, and superslots are ordinary lookups. A
  knowledge-base object is
  classified before the value is read. A slot already computed is read
  from the frame. km-int evaluates a local rule and a rule inherited
  from a class."
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

    :else
    ;; A slot read classifies. The Lisp calls in get-slotvals are
    ;; commented out and would classify only at creation and has.
    (let [state (if (kb/kb-object? frame)
                  (classify/classify state frame km-int)
                  state)]
      (if (refused? state)
        state
        (if-let [classed (class-slot state frame slot km-int)]
          classed
          (cond
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

            (utils/eql? slot (symbol "supersituations"))
            (situations/immediate-supersituations state frame km-int)

            (utils/eql? slot (symbol "all-supersituations"))
            (situations/all-supersituations state frame km-int)

            :else
            (if-let [walked (class-walk state frame slot)]
              walked
              (if-let [cached (cached-answer state frame slot)]
                cached
                (if (frame/ignore-slot-in-global? (:kb state) slot)
                  (situations-mode-error state frame slot)
                  (slotvals-from-kb state frame slot km-int))))))))))

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
  back through km-int. most-specific and most-general are refused:
  they need description subsumption."
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
