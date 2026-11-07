(ns som.km.kbutils
  "Shape tests and equality from the syntactic half of kbutils.lisp.

  These functions look at a value. Whether a name is a class, a slot,
  or an instance is answered by som.km.frame, which holds the frames.
  remove-dup-instances does not dereference. The store follows a
  binding before it asks this function to compare values."
  (:require [som.km.explain :as explain]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(def tolerance
  "Numbers within this bound are the same value. The binding in header.lisp is 0.0001."
  0.0001)

(def ^{:doc "Symbols and keywords that are not class or slot names. This is *reserved-keywords*."}
  reserved-keywords
  (into #{:set :seq :bag :args :triple :pair :function :default}
        (map symbol)
        ["a" "some" "must-be-a" "mustnt-be-a" "print" "format" "km-format"
         "an" "instance" "@" "retain-expr"
         "possible-values" "excluded-values" "spy" "unspy" "anonymous-instancep"
         "sanity-check"
         "every" "the" "the1" "the2" "the3" "theN" "theNth" "of" "forall"
         "forall2" "with" "where" "theoneof" "theoneof2"
         "forall-seq" "forall-seq2" "forall-bag" "forall-bag2" "the-class"
         "constraints-for" "rules-for"
         "the+" "a+" "evaluate-paths" "clone" "a-prototype"
         "oneof" "oneof2" "It" "It2" "if" "then" "else" "allof" "allof2"
         "in" "and" "or" "not" "is" "&" "&&" "&?" "&+" "&+?" "&+!" "&!" "&&!"
         "=" "===" "/=" "+" "-" "/" "^" ">=" "<=" "isa" "append"
         "are" "includes" "thelast"
         "showme-here" "showme" "showme-all" "evaluate-all" "quote"
         "delete" "evaluate" "has-value" "andify" "make-sentence" "make-phrase"
         "has" "now-has" "also-has" "also-hasnt" "now-has-definition"
         "must" "is-superset-of" "covers" "subsumes" "has-definition" "numberp"
         "bag" "seq"
         "no-inheritance" "comm" "get-justification"
         "trace" "untrace" "fluent-instancep" "at-least" "at-most" "exactly"
         "constraint" "<>" "reverse"
         "is-subsumed-by" "is-covered-by" "set-constraint" "set-filter"
         "in-situation" "in-every-situation" "end-situation" "do" "do-and-next"
         "in-theory" "end-theory" "see-theory" "hide-theory" "visible-theories"
         "curr-situation" "ignore-result" "do-script" "new-context" "do-plan"]))

(def ^:private excluded-objects
  "kb-objectp rejects these. t is not in the list."
  #{(symbol "nil") :set :seq :bag :args :triple :pair :function :incomplete})

(def ^:private val-constraint-keywords
  #{(symbol "must-be-a") (symbol "mustnt-be-a") (symbol "<>")
    (symbol "possible-values") (symbol "excluded-values")
    (symbol "constraint") (symbol "no-inheritance") (symbol "retain-expr")})

(def ^:private set-constraint-keywords
  #{(symbol "at-least") (symbol "at-most") (symbol "exactly")
    (symbol "set-constraint") (symbol "sometimes") (symbol "set-filter")})

(def ^:private inequality-relations
  #{(symbol "<") (symbol ">") (symbol "<=") (symbol ">=") (symbol "/=")})

(def ^:private equality-relations
  #{(symbol "=") (symbol "&?")})

(def ^:private val-unification-operators
  #{(symbol "&") (symbol "&+") (symbol "&+!") (symbol "&!")
    (symbol "==") (symbol "&+?") (symbol "&?")})

(def ^:private set-unification-operators
  #{(symbol "&&") (symbol "&&!") (symbol "===")})

(def ^:private unification-operators
  #{(symbol "&") (symbol "&?") (symbol "&!") (symbol "&&") (symbol "&&!")
    (symbol "&+") (symbol "&+!") (symbol "&+?") (symbol "==") (symbol "===")})

(def ^:private amp (symbol "&"))
(def ^:private amp-amp (symbol "&&"))
(def ^:private existential-heads #{(symbol "a") (symbol "some")})

(defn km-null?
  "True for the empty list and for the symbol nil."
  [value]
  (or (nil? value) (= value (symbol "nil"))))

(defn slot-object?
  "True for a symbol other than the empty list. This is slot-objectp."
  [slot]
  (and (some? slot) (term/lisp-symbol? slot)))

(defn path?
  "True for a list, including the empty list. This is pathp."
  [path]
  (utils/lisp-list? path))

(defn kb-object?
  "True for a symbol that can have a frame.

  The symbol nil, a user comment, and the structure keywords are rejected.
  The symbols t and f are accepted. This does not ask the store."
  [instance]
  (and (some? instance)
       (term/lisp-symbol? instance)
       (not (explain/user-comment? instance))
       (not (contains? excluded-objects instance))))

(defn km-set?
  "True for a list headed by :set."
  [expr]
  (and (term/cons? expr) (= :set (term/car expr))))

(defn km-seq?
  "True for a list headed by :seq."
  [expr]
  (and (term/cons? expr) (= :seq (term/car expr))))

(defn km-bag?
  "True for a list headed by :bag."
  [expr]
  (and (term/cons? expr) (= :bag (term/car expr))))

(defn km-pair-value?
  "True for a list headed by :pair. This is km-pairp."
  [expr]
  (and (term/cons? expr) (= :pair (term/car expr))))

(defn km-args?
  "True for a list headed by :args."
  [expr]
  (and (term/cons? expr) (= :args (term/car expr))))

(defn km-function?
  "True for a list headed by :function."
  [expr]
  (and (term/cons? expr) (= :function (term/car expr))))

(defn km-default?
  "True for a list headed by :default."
  [expr]
  (and (term/cons? expr) (= :default (term/car expr))))

(defn- proper-length [value]
  (loop [value value
         seen 0]
    (cond
      (nil? value) seen
      (term/cons? value) (recur (term/cdr value) (inc seen))
      :else nil)))

(defn km-triple?
  "True for (:triple a b c), after comments and sources are removed.

  The cleaned list has four elements: the keyword and three fields."
  [triple]
  (and (term/cons? triple)
       (= :triple (term/car triple))
       (let [clean (explain/desource-decomment triple)]
         (= 4 (proper-length clean)))))

(defn set-elements
  "The values in a :set, without the keyword."
  [value]
  (term/cdr value))

(defn seq-elements
  "The values in a :seq, :bag, :pair, or :args, without the keyword."
  [value]
  (term/cdr value))

(defn- contains-eql? [item tree]
  (cond
    (utils/eql? item tree) true
    (nil? tree) false
    (term/cons? tree)
    (or (contains-eql? item (term/car tree))
        (contains-eql? item (term/cdr tree)))
    :else false))

(defn the-class?
  "True for (the-class ...)."
  [expr]
  (and (term/cons? expr) (= (symbol "the-class") (term/car expr))))

(defn quoted-description?
  "True for (quote (every ...))."
  [expr]
  (and (utils/quote? expr)
       (let [body (utils/unquote-expr expr)]
         (and (term/cons? body) (= (symbol "every") (term/car body))))))

(defn description?
  "True for (quote (every ...)) or (the-class ...)."
  [expr]
  (or (quoted-description? expr) (the-class? expr)))

(defn val-constraint?
  "True for a list headed by a value constraint such as must-be-a or <>."
  [expr]
  (and (term/cons? expr) (contains? val-constraint-keywords (term/car expr))))

(defn set-constraint?
  "True for the keyword :incomplete or a list headed by a set constraint."
  [expr]
  (or (= expr :incomplete)
      (and (term/cons? expr) (contains? set-constraint-keywords (term/car expr)))))

(defn constraint-expr?
  "True for a value constraint or a set constraint."
  [expr]
  (or (val-constraint? expr) (set-constraint? expr)))

(defn retain-expr?
  "True for (retain-expr ...)."
  [expr]
  (and (term/cons? expr) (= (symbol "retain-expr") (term/car expr))))

(defn- nth-item [coll index]
  (loop [coll coll
         index index]
    (cond
      (or (nil? coll) (not (term/cons? coll))) nil
      (zero? index) (term/car coll)
      :else (recur (term/cdr coll) (dec index)))))

(defn km-boolean?
  "True for a boolean expression, recognized by its head or by an operator."
  [expr]
  (and (term/cons? expr)
       (or (contains? #{(symbol "is-true") (symbol "all-true") (symbol "some-true")
                        (symbol "theoneof") (symbol "theoneof2") (symbol "exists")
                        (symbol "has-value")}
                      (term/car expr))
           (contains? #{(symbol "&?") (symbol "&+?") (symbol "=") (symbol "/=")
                        (symbol ">") (symbol "<") (symbol ">=") (symbol "<=")
                        (symbol "and") (symbol "or") (symbol "not") (symbol "numberp")
                        (symbol "is-subsumed-by") (symbol "subsumes") (symbol "covers")
                        (symbol "isa") (symbol "is") (symbol "includes")
                        (symbol "is-superset-of")}
                      (nth-item expr 1))
           (= (symbol "must") (nth-item expr 2))
           (= (symbol "must") (nth-item expr 4)))))

(defn sometimes?
  "True for (sometimes ...)."
  [expr]
  (and (term/cons? expr) (= (symbol "sometimes") (term/car expr))))

(defn situation-invariant?
  "True for (a ...). The result of the expression can move between situations."
  [expr]
  (and (term/cons? expr) (= (symbol "a") (term/car expr))))

(defn existential?
  "True for (a ...) or (some ...).

  A leading comment tag is skipped, so ([Car1] a Big) is existential.
  (an ...) is not. The interpreter rewrites an before this test matters."
  [expr]
  (and (term/cons? expr)
       (or (contains? existential-heads (term/car expr))
           (and (explain/comment-tag? (term/car expr))
                (existential? (term/cdr expr))))))

(defn fluent-instance-expr?
  "True for (some ...)."
  [expr]
  (and (term/cons? expr) (= (symbol "some") (term/car expr))))

(defn comparison-operator?
  "True for <, >, <=, >=, /=, =, and &?."
  [slot]
  (or (contains? inequality-relations slot)
      (contains? equality-relations slot)))

(defn km-var?
  "True for a symbol or keyword whose name starts with ?."
  [var]
  (and (term/lisp-symbol? var)
       (let [name (term/symbol-name var)]
         (and (pos? (count name)) (= \? (nth name 0))))))

(defn km-tag?
  "True for a non-empty atom, a constraint, or a :set of those."
  [tag]
  (or (and (utils/lisp-atom? tag) (some? tag))
      (constraint-expr? tag)
      (and (km-set? tag)
           (loop [items (set-elements tag)]
             (cond
               (nil? items) true
               (term/cons? items)
               (and (km-tag? (term/car items))
                    (recur (term/cdr items)))
               :else false)))))

(defn is-km-term?
  "True for a value KM treats as already in term shape, including a constraint."
  [concept]
  (or (utils/lisp-atom? concept)
      (description? concept)
      (utils/quote? concept)
      (term/structured-list? concept)
      (km-set? concept)
      (fn? concept)
      (constraint-expr? concept)))

(defn is-simple-km-term?
  "True for an atom that is not a reserved keyword, a description, or a function."
  [concept]
  (or (and (utils/lisp-atom? concept)
           (not (contains? reserved-keywords concept)))
      (description? concept)
      (fn? concept)))

(defn fully-evaluated?
  "True when concept has no unevaluated parts left.

  The symbol * is not evaluated. A quoted form that still contains the
  symbol unquote is not evaluated. A :set is evaluated only inside a
  structured value, and its elements are not themselves structured.
  in-structured? is the Lisp keyword in-structured-exprp."
  [concept & {:keys [in-structured?] :or {in-structured? false}}]
  (or (and (utils/lisp-atom? concept) (not= concept (symbol "*")))
      (and (utils/quote? concept)
           (not (contains-eql? (symbol "unquote") concept)))
      (the-class? concept)
      (and (km-set? concept)
           in-structured?
           (loop [items (set-elements concept)]
             (cond
               (nil? items) true
               (term/cons? items)
               (and (fully-evaluated? (term/car items) :in-structured? false)
                    (recur (term/cdr items)))
               :else false)))
      (and (term/structured-list? concept)
           (loop [items (seq-elements concept)]
             (cond
               (nil? items) true
               (term/cons? items)
               (and (fully-evaluated? (term/car items) :in-structured? true)
                    (recur (term/cdr items)))
               :else false)))))

(defn &-expr?
  "True when the second element is &, &!, &+, or ==.

  &? and &+? are not included."
  [expr]
  (and (term/cons? expr)
       (contains? #{amp (symbol "&!") (symbol "&+") (symbol "==")}
                  (nth-item expr 1))))

(defn &&-expr?
  "True when the second element is &&, &&!, or ===."
  [expr]
  (and (term/cons? expr)
       (contains? set-unification-operators (nth-item expr 1))))

(defn val-unification-operator?
  "True for a value-level unification operator, including &? and &+?."
  [value]
  (contains? val-unification-operators value))

(defn set-unification-operator?
  "True for &&, &&!, or ===."
  [value]
  (contains? set-unification-operators value))

(defn unification-operator?
  "True for a value-level or set-level unification operator."
  [value]
  (contains? unification-operators value))

(def ^:private equality-assertion-operators
  #{(symbol "&") (symbol "&+") (symbol "&+!") (symbol "&!") (symbol "==")})

(def ^:private full-equality-assertion-operators
  #{(symbol "&") (symbol "&!") (symbol "==")})

(defn equality-assertion-operator?
  "True for &, &+, &+!, &!, or ==. &? and &+? are tests, not assertions."
  [value]
  (contains? equality-assertion-operators value))

(defn full-equality-assertion-operator?
  "True for &, &!, or ==. Pushing one of these records both instances."
  [value]
  (contains? full-equality-assertion-operators value))

(defn arg1
  "The first argument of (:args a b ...). This is arg1of."
  [arg-structure]
  (nth-item arg-structure 1))

(defn arg2
  "The second argument of an :args list."
  [arg-structure]
  (nth-item arg-structure 2))

(defn arg3
  "The third argument of an :args list."
  [arg-structure]
  (nth-item arg-structure 3))

(defn arg4
  "The fourth argument of an :args list."
  [arg-structure]
  (nth-item arg-structure 4))

(declare km-equal?)

(defn km-set-equal?
  "True when the two lists hold the same elements under km-equal?.

  Order does not matter. A repeated element does not matter. The lists
  include their :set keyword."
  [left right]
  (nil? (utils/set-exclusive-or left right :test km-equal?)))

(defn- same-length? [left right]
  (loop [left left
         right right]
    (cond
      (and (nil? left) (nil? right)) true
      (and (term/cons? left) (term/cons? right))
      (recur (term/cdr left) (term/cdr right))
      :else false)))

(defn- bag-equal-rest [left right]
  (or (utils/equal? left right)
      (and (term/cons? left)
           (utils/member? (term/car left) right km-equal?)
           (bag-equal-rest (term/cdr left)
                           (utils/remove-items (term/car left) right
                                               :test km-equal?
                                               :count 1)))))

(defn km-bag-equal?
  "True when the two bags hold the same elements, with the same counts.

  Order does not matter. The lists include their :bag keyword."
  [left right]
  (and (same-length? left right)
       (bag-equal-rest left right)))

(defn- seq-equal-rest [left right]
  (or (and (nil? left) (nil? right))
      (and (term/cons? left)
           (term/cons? right)
           (km-equal? (term/car left) (term/car right))
           (seq-equal-rest (term/cdr left) (term/cdr right)))))

(defn km-seq-equal?
  "True when the two lists have the same length and km-equal? elements, in order."
  [left right]
  (and (same-length? left right)
       (seq-equal-rest left right)))

(defn- within-tolerance? [left right]
  (let [difference (abs (- left right))
        scaled (* (max (abs left) (abs right)) tolerance)]
    (<= difference (min tolerance scaled))))

(defn km-equal?
  "True when two slot values are the same value.

  The same symbol matches, by name. The empty list matches the symbol nil.
  A symbol matches only that same symbol. Two numbers match within
  tolerance. A structurally identical list matches, except an
  existential expression and a structured list. Two separately written
  (a Car) expressions do not match. Sets match as sets. Bags match as
  bags. Sequences, pairs, triples, and :args match in order."
  [left right]
  (cond
    (utils/eql? left right) true
    (nil? left) (= right (symbol "nil"))
    (nil? right) (= left (symbol "nil"))
    (or (term/lisp-symbol? left) (term/lisp-symbol? right)) false
    (and (number? left) (number? right)) (within-tolerance? left right)
    (or (number? left) (number? right)) false
    (and (utils/equal? left right)
         (not (existential? left))
         (not (term/structured-list? left))) true
    (or (utils/lisp-atom? left) (utils/lisp-atom? right)) false
    (and (km-set? left) (km-set? right)) (km-set-equal? left right)
    (and (km-bag? left) (km-bag? right)) (km-bag-equal? left right)
    (and (km-args? left) (km-args? right)) (km-seq-equal? left right)
    (and (km-seq? left) (km-seq? right)) (km-seq-equal? left right)
    (and (km-pair-value? left) (km-pair-value? right)) (km-seq-equal? left right)
    (and (km-triple? left) (km-triple? right)) (km-seq-equal? left right)
    :else false))

(defn remove-dup-instances
  "Drop a later value that km-equal? says is already present.

  The earlier value stays in its original position. The Lisp function
  dereferences before comparing. This port compares the values it is
  given. The store will dereference when bindings exist."
  [instances]
  (utils/remove-duplicates instances :test km-equal? :from-end? true))

(defn val-to-vals
  "The list of values inside one KM value.

  The empty list and the symbol nil become nil. A :set becomes its
  elements, without flattening a nested set. Anything else becomes a
  one-element list."
  [val]
  (cond
    (km-null? val) nil
    (km-set? val) (set-elements val)
    :else (term/km-list val)))

(defn vals-to-val
  "One KM value for a list of values.

  Nil stays nil. A one-element list becomes that element. A longer list
  becomes (:set ...). Any other value is an error."
  [vals]
  (cond
    (nil? vals) nil
    (term/singleton? vals) (term/car vals)
    (term/cons? vals) (term/cons-cell :set vals)
    :else (throw (ex-info
                  (str "Expecting a set of values, but just found a single value " vals ".")
                  {:value vals}))))

(defn flatten-set
  "A :set becomes the flattened list of its values. Any other value becomes a one-element list."
  [value]
  (if (km-set? value)
    (utils/mapcan-list flatten-set (set-elements value))
    (term/km-list value)))

(defn flatten-sets
  "Flatten each :set in a list of values. The argument itself is that list, not one :set."
  [vals]
  (utils/mapcan-list flatten-set vals))

(defn &-expr-to-vals
  "The values joined by &. (x & y & z) becomes (x y z).

  A nested & is flattened. An expression that is not an & expression
  becomes a one-element list. When the expression is illegally long and
  the fourth element is not an operator, the Lisp warns and continues
  with the first three elements. The warning is not printed here."
  [expr]
  (cond
    (nil? expr) nil
    (&-expr? expr)
    (if (val-unification-operator? (nth-item expr 3))
      (&-expr-to-vals (term/km-list (term/car expr)
                                    (nth-item expr 3)
                                    (term/cdr (term/cdr expr))))
      (utils/append-lists
       (term/km-list (&-expr-to-vals (term/car expr))
                     (&-expr-to-vals (nth-item expr 2)))))
    :else (term/km-list expr)))

(defn un-andify
  "The pieces of a single-valued slot's values.

  Nil stays nil. One value is split when it is an & expression.
  A longer list is split the same way. The Lisp prints that the slot
  had several values. This function does not print."
  [vals]
  (cond
    (nil? vals) nil
    (term/singleton? vals) (&-expr-to-vals (term/car vals))
    (term/cons? vals) (utils/mapcan-list &-expr-to-vals vals)
    :else (throw (ex-info "A single-valued slot's values are a list."
                          {:values vals}))))

(defn vals-to-&-expr
  "Join values with joiner. Nil stays nil. One value stays that value.

  (a b c) with the default joiner becomes (a & b & c). first-time? is
  for the recursive call: a one-element tail stays a list so it can be
  spliced."
  [vals & {:keys [joiner first-time?] :or {joiner amp first-time? true}}]
  (cond
    (nil? vals) nil
    (term/singleton? vals) (if first-time? (term/car vals) vals)
    :else
    (term/build-list [(term/car vals) joiner]
                     (vals-to-&-expr (term/cdr vals)
                                     :joiner joiner
                                     :first-time? false))))

(defn valsets-to-&&-exprs
  "Join value lists with &&. One value list is returned unwrapped.

  ((a b) (c d) (e f)) becomes (((a b) && (c d) && (e f))).
  ((a b)) becomes (a b)."
  [valsets]
  (cond
    (nil? valsets) nil
    (term/singleton? valsets) (term/car valsets)
    :else (val-to-vals (vals-to-&-expr valsets :joiner amp-amp))))

(defn- triple-list? [value]
  (and (term/cons? value)
       (term/cons? (term/cdr value))
       (term/cons? (term/cdr (term/cdr value)))
       (nil? (term/cdr (term/cdr (term/cdr value))))))

(defn &&-exprs-to-valsets
  "Split one && expression into value lists.

  (a b) becomes ((a b)). A singleton ((a b) && (c d)) becomes ((a b) (c d)).
  A list that is not a singleton is wrapped and not split."
  [exprs]
  (if (term/singleton? exprs)
    (let [expr (term/car exprs)]
      (if (and (term/cons? expr) (set-unification-operator? (nth-item expr 1)))
        (utils/append-lists
         (term/km-list (&&-exprs-to-valsets (term/car expr))
                       (&&-exprs-to-valsets
                        (if (triple-list? expr)
                          (nth-item expr 2)
                          (term/km-list (term/cdr (term/cdr expr)))))))
        (term/km-list exprs)))
    (term/km-list exprs)))

(defn- listify-elements [exprs]
  (loop [exprs exprs
         acc []]
    (cond
      (nil? exprs) (term/build-list acc nil)
      (term/cons? exprs)
      (recur (term/cdr exprs) (conj acc (utils/listify (term/car exprs))))
      :else (throw (ex-info "This list is dotted." {:tail exprs})))))

(defn- any-single-value? [exprs]
  (loop [exprs exprs]
    (cond
      (nil? exprs) false
      (term/cons? exprs)
      (if (utils/lisp-atom? (term/car exprs))
        true
        (recur (term/cdr exprs)))
      :else false)))

(defn- val-sets-to-expr0 [exprs single-valued? joiner]
  (cond
    (nil? exprs) nil
    (nil? (term/car exprs))
    (val-sets-to-expr0 (term/cdr exprs) single-valued? joiner)
    :else
    (let [head (term/car exprs)
          first-item (cond
                       single-valued?
                       (if (term/singleton? head)
                         (term/car head)
                         (vals-to-&-expr head :joiner joiner))
                       :else head)
          linked (val-sets-to-expr0 (term/cdr exprs) single-valued? joiner)]
      (if (nil? linked)
        (term/km-list first-item)
        (term/cons-cell first-item (term/cons-cell joiner linked))))))

(defn val-sets-to-expr
  "One expression for a list of value lists.

  Empty lists are dropped. A structurally identical later list is
  dropped, and the earlier one stays. One remaining list becomes the
  value vals-to-val would produce. single-valued? joins the lists with
  &. Otherwise they are joined with &&. combine-values-by-appending?
  appends every value and removes later km-equal? duplicates.

  A single value where a list was required is wrapped in a list. The
  Lisp prints a warning and continues. The warning is not printed here.
  A single-valued list that holds more than one value is joined with &.
  The Lisp prints a trace line and continues. That line is not printed."
  [exprs & {:keys [single-valued? combine-values-by-appending? joiner]
            :or {single-valued? false combine-values-by-appending? false}}]
  (let [joiner (if (some? joiner) joiner (if single-valued? amp amp-amp))
        kept (utils/remove-duplicates (utils/remove-items nil exprs :test utils/eql?)
                                      :test utils/equal?
                                      :from-end? true)
        exprs (if (any-single-value? kept) (listify-elements kept) kept)]
    (cond
      (nil? exprs) nil
      (term/singleton? exprs) (vals-to-val (term/car exprs))
      combine-values-by-appending?
      (vals-to-val (remove-dup-instances (utils/append-lists exprs)))
      :else (val-sets-to-expr0 exprs single-valued? joiner))))
