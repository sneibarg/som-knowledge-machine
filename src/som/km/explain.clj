(ns som.km.explain
  "Comment tags, source markers, and the KM form of an explanation.

  A user comment is a symbol whose name starts with [ and ends with ].
  It is stored later as (comm [tag] Self). A source is a list whose first
  element is the symbol @. Neither one is a slot value. This namespace
  recognizes them and strips them. It also wraps a value written on a
  class with its (@ Self class slot) source. build-rule turns a sourced
  value into (every Class has ...). cloned-from, added-at,
  projected-from, and every stay as they are. modify-set-explanation
  rewrites a :set before the store decides whether to keep it. Comment
  tags inside an expression are listed here. The frame store keeps the
  (comment ...) text. This namespace does not read the frame store."
  (:require [som.km.term :as term]
            [som.km.utils :as utils]))

(def ^:private at-symbol (symbol "@"))
(def ^:private comm-symbol (symbol "comm"))
(def ^:private self-symbol (symbol "Self"))
(def ^:private instance-of-symbol (symbol "instance-of"))
(def ^:private no-inheritance-symbol (symbol "no-inheritance"))

(defn source?
  "True when tag is a source (@ ...). This is sourcep."
  [tag]
  (and (term/cons? tag) (= at-symbol (term/car tag))))

(defn user-comment?
  "True when tag is a symbol whose name starts with [ and ends with ].
  This is user-commentp. An empty name is not a comment."
  [tag]
  (and (term/lisp-symbol? tag)
       (let [name (term/symbol-name tag)
             size (count name)]
         (and (pos? size)
              (= \[ (nth name 0))
              (= \] (nth name (dec size)))))))

(defn internal-comment?
  "True for (comm ...), the stored form of a user comment."
  [tag]
  (and (term/cons? tag) (= comm-symbol (term/car tag))))

(defn comment-tag?
  "True for a user comment or its stored (comm ...) form. This is comment-tagp."
  [tag]
  (or (internal-comment? tag) (user-comment? tag)))

(defn comment-or-source?
  "True for a comment tag or a source."
  [tag]
  (or (internal-comment? tag) (source? tag) (user-comment? tag)))

(defn- dotted!
  [tail]
  (throw (ex-info "This list is dotted. mapcar would raise an error on that tail."
                  {:tail tail})))

(defn- map-proper
  [f expr]
  (loop [expr expr
         acc []]
    (cond
      (nil? expr) (term/build-list acc nil)
      (term/cons? expr) (recur (term/cdr expr) (conj acc (f (term/car expr))))
      :else (dotted! expr))))

(defn- remove-when
  [pred expr]
  (loop [expr expr
         acc []]
    (cond
      (nil? expr) (term/build-list acc nil)
      (term/cons? expr)
      (recur (term/cdr expr)
             (if (pred (term/car expr)) acc (conj acc (term/car expr))))
      :else (dotted! expr))))

(defn- sourced-pair?
  [expr]
  (and (term/pair? expr)
       (source? (term/car (term/cdr expr)))
       (not (term/structured-list? expr))
       (not= no-inheritance-symbol (term/car expr))))

(defn- commented-pair?
  [expr]
  (and (term/pair? expr)
       (comment-tag? (term/car (term/cdr expr)))
       (not (term/structured-list? expr))
       (not= no-inheritance-symbol (term/car expr))))

(defn desource
  "Remove source markers. A pair whose second element is only a source
  collapses to its first element, except on a structured list or
  no-inheritance. This is desource."
  [expr]
  (cond
    (sourced-pair? expr) (desource (term/car expr))
    (term/cons? expr) (remove-when source? (map-proper desource expr))
    :else expr))

(defn decomment
  "Remove comment tags.

  no-delistification? defaults to true, matching the Lisp keyword. A
  commented pair then stays a list. Pass false to collapse that pair to
  its first element. instance-of keeps its list either way."
  [expr & {:keys [no-delistification?] :or {no-delistification? true}}]
  (cond
    (and (commented-pair? expr) (not no-delistification?))
    (decomment (term/car expr) :no-delistification? no-delistification?)

    (term/cons? expr)
    (remove-when comment-tag?
                 (map-proper #(decomment % :no-delistification? true) expr))

    :else expr))

(defn convert-comment
  "Turn one user comment into (comm comment self). The default self is Self."
  ([user-comment]
   (convert-comment user-comment self-symbol))
  ([user-comment self]
   (term/km-list comm-symbol user-comment self)))

(defn convert-comments
  "Walk a proper list and replace user comments with their stored form.
  This is convert-comments-to-internal-form. A comment that is already
  stored is left as it is."
  ([expr]
   (convert-comments expr self-symbol))
  ([expr self]
   (cond
     (internal-comment? expr) expr
     (user-comment? expr) (convert-comment expr self)
     (term/cons? expr) (map-proper #(convert-comments % self) expr)
     :else expr)))

(declare desource-decomment)

(defn- decomment-tail
  "desource+decomment1. Returns [expr comment-found?].

  A comment or source in the head forces the flag on and keeps only the
  primary value of the tail. The flag from a recursive walk of the head
  is not copied up. That is the Lisp multiple-value behavior: the head
  is passed through desource+decomment, and only the tail reports whether
  a comment was found."
  [expr]
  (cond
    (nil? expr) [nil false]
    (term/cons? expr)
    (let [head (term/car expr)
          tail (term/cdr expr)]
      (cond
        (comment-or-source? head)
        (let [[rest-expr _] (decomment-tail tail)]
          [rest-expr true])

        (and (term/pair? expr) (= instance-of-symbol head))
        (let [[inner _] (decomment-tail (term/car tail))]
          [(term/km-list head inner) false])

        :else
        (let [head-result (desource-decomment head)
              [tail-result found?] (decomment-tail tail)]
          (if (and (identical? head-result head)
                   (identical? tail-result tail))
            [expr false]
            [(term/cons-cell head-result tail-result) found?]))))
    :else [expr false]))

(defn desource-decomment
  "Remove comments and sources.

  This is desource+decomment. When a comment or source was removed and
  delistify? is true, a one-element list collapses to that element.
  A structured list and no-inheritance stay lists. retain-comments?
  returns the expression unchanged. instance-of does not collapse its
  own list of classes."
  [expr & {:keys [retain-comments? delistify?]
           :or {retain-comments? false delistify? true}}]
  (if retain-comments?
    expr
    (let [[result found?] (decomment-tail expr)]
      (if (and delistify?
               found?
               (not (term/structured-list? expr))
               (not (and (term/cons? expr)
                         (= no-inheritance-symbol (term/car expr)))))
        (term/delistify result)
        result))))

(defn desource-decomment-top-level
  "Remove comments and sources from the top of one value.

  A pair whose second element is a comment or a source collapses to its
  first element, except a structured list or no-inheritance. Any other
  list drops comment and source elements and stays a list. This is
  desource+decomment-top-level. Nested markers are left in place."
  [expr]
  (cond
    (and (term/pair? expr)
         (comment-or-source? (term/car (term/cdr expr)))
         (not (term/structured-list? expr))
         (not= no-inheritance-symbol (term/car expr)))
    (term/car expr)

    (term/cons? expr) (remove-when comment-or-source? expr)
    :else expr))

(defn- sourced-pair-collapses?
  [expr]
  (and (term/pair? expr)
       (source? (term/car (term/cdr expr)))
       (not (term/structured-list? expr))
       (not= no-inheritance-symbol (term/car expr))))

(defn desource-top-level
  "Remove source markers from the top of one value.

  A pair whose second element is a source collapses to its first
  element, and that collapse repeats. A structured list and
  no-inheritance stay lists. Any other list drops source elements and
  stays a list. Nested sources below that top are left in place. This
  is desource-top-level."
  [expr]
  (cond
    (sourced-pair-collapses? expr) (desource-top-level (term/car expr))
    (term/cons? expr) (remove-when source? expr)
    :else expr))

(def ^:private atomic-vals-only
  "Slots whose values are stored without a source tag.

  These are the built-in atomic slots. A value on one of them is left
  as it was written."
  (set (map symbol
            ["domain" "range" "cardinality" "arity"
             "slots-to-opportunistically-evaluate"
             "locked-instances" "locked-instance-of"
             "inverse" "inverse2" "inverse3"
             "inherit-with-overrides" "simple-inherit-with-overrides"
             "superclasses" "subclasses" "instances" "instance-of"
             "supersituations" "members" "member-of"
             "prototypes" "prototypes-of"
             "prototype-participants" "prototype-participant-of"
             "clone-built-from" "has-built-clones"
             "cloned-from" "has-clones"
             "domain-of" "range-of" "remove-subsumers" "remove-subsumees"
             "subsituations" "subslots" "superslots" "id"
             "combine-values-by-appending" "dont-cache-values" "ignore-inverses"
             "fluent-status" "called" "uniquely-called" "block-projection-for"])))

(def ^:private annotated-constraints
  (set (map symbol ["must-be-a" "exactly" "at-most" "at-least"])))

(def ^:private constraint-heads
  (into annotated-constraints
        (map symbol ["mustnt-be-a" "possible-values" "excluded-values" "<>"
                     "no-inheritance" "constraint" "set-constraint" "set-filter"
                     "sometimes"])))

(defn- km-var?
  [value]
  (and (term/lisp-symbol? value)
       (let [name (term/symbol-name value)]
         (and (pos? (count name)) (= \? (nth name 0))))))

(defn- skipped-constraint?
  [value]
  (or (utils/eql? value :incomplete)
      (and (term/cons? value)
           (contains? constraint-heads (term/car value))
           (not (contains? annotated-constraints (term/car value))))))

(defn- contains-source?
  [expr]
  (loop [expr expr]
    (cond
      (nil? expr) false
      (not (term/cons? expr)) false
      (source? (term/car expr)) true
      :else (recur (term/cdr expr)))))

(defn make-source
  "The source (@ Self class). This is make-source."
  [class]
  (term/km-list at-symbol self-symbol class))

(defn add-to-source
  "source with item added at the end. This is add-to-source."
  [source item]
  (utils/append-lists (term/km-list source (term/km-list item))))

(defn- attach-source
  "Put source on expr. An atom becomes (expr source). A list gains source
  as its last element, unless a source is already there."
  [expr source]
  (cond
    (and (term/cons? expr) (contains-source? expr)) (term/km-list expr source)
    (term/cons? expr) (utils/append-lists (term/km-list expr (term/km-list source)))
    :else (term/km-list expr source)))

(defn annotate-val
  "expr with source attached, when the value can carry one.

  A number, a string, or a symbol becomes (value source). A list gains
  source as its last element. A comment, a quote, a ?variable, :incomplete,
  and a constraint other than must-be-a, exactly, at-most, or at-least stay
  as they are. & and && are not split into their components, and an
  embedded (a ...) is not walked. The evaluator strips the trailing source
  before it dispatches."
  [expr source]
  (cond
    (or (nil? expr)
        (comment-tag? expr)
        (utils/quote? expr)
        (km-var? expr)
        (skipped-constraint? expr))
    expr

    (or (number? expr) (string? expr) (term/lisp-symbol? expr))
    (attach-source expr source)

    (term/cons? expr) (attach-source expr source)
    :else expr))

(defn- annotate-vals
  [vals source]
  (map-proper #(annotate-val % source) vals))

(defn annotate-slotsvals
  "slotsvals with a source on every value that can carry one.

  source is (@ Self class). The slot name is added to that source.
  A comment pair and a built-in atomic slot are left unchanged."
  [slotsvals source]
  (loop [slotsvals slotsvals
         acc []]
    (cond
      (nil? slotsvals) (term/build-list acc nil)
      (not (term/cons? slotsvals))
      (throw (ex-info "This list is dotted." {:tail slotsvals}))
      :else
      (let [pair (term/car slotsvals)
            slot (when (term/cons? pair) (term/car pair))]
        (recur (term/cdr slotsvals)
               (conj acc
                     (if (or (comment-tag? pair)
                             (contains? atomic-vals-only slot)
                             (not (term/cons? pair)))
                       pair
                       (term/km-list slot
                                     (annotate-vals (term/car (term/cdr pair))
                                                    (add-to-source source slot))))))))))

(defn explanation-type
  "The head of an explanation. Nil when the explanation is not a list."
  [explanation]
  (when (term/cons? explanation) (term/car explanation)))

(defn sources
  "The source markers among the top elements of expr. This is sources."
  [expr]
  (when (term/cons? expr)
    (loop [expr expr
           acc []]
      (cond
        (nil? expr) (term/build-list acc nil)
        (not (term/cons? expr))
        (throw (ex-info "This list is dotted." {:tail expr}))
        (source? (term/car expr)) (recur (term/cdr expr) (conj acc (term/car expr)))
        :else (recur (term/cdr expr) acc)))))

(defn source-path
  "The path a source denotes, after the @ and the instance. This is source-path."
  [source]
  (when (term/cons? source) (term/cdr (term/cdr source))))

(defn desource-all-but-top-level
  "Drop sources nested inside each top element. A source at the top stays.

  (a (b (@ x)) (@ y)) becomes (a b (@ y)). This is
  desource-all-but-top-level."
  [expr]
  (if (term/cons? expr) (map-proper desource expr) expr))

(defn modify-set-explanation
  "Rewrite a :set explanation before it is stored.

  Each element is desourced, and the distinct sources of those elements
  are appended. One remaining value is returned as that value. A longer
  result stays a :set. Anything that is not a :set is returned unchanged.
  This is modify-set-explanation."
  [expr]
  (if-not (and (term/cons? expr) (= :set (term/car expr)))
    expr
    (let [vals (term/cdr expr)
          stripped (map-proper desource vals)
          found (utils/remove-duplicates (utils/mapcan-list sources vals)
                                         :test utils/equal?)
          combined (utils/append-lists (term/km-list stripped found))]
      (cond
        (nil? combined) nil
        (term/singleton? combined) (term/car combined)
        :else (term/cons-cell :set combined)))))

(defn comment-tags
  "Comment tags among the top elements of expr. This is get-comment-tags."
  [expr]
  (when (term/cons? expr)
    (loop [expr expr
           acc []]
      (cond
        (nil? expr) (term/build-list acc nil)
        (not (term/cons? expr))
        (throw (ex-info "This list is dotted." {:tail expr}))
        (comment-tag? (term/car expr))
        (recur (term/cdr expr) (conj acc (term/car expr)))
        :else (recur (term/cdr expr) acc)))))

(defn comment-tags-recursive
  "Every comment tag in expr, including a tag nested in a list.

  A tag is returned as itself and is not walked again. This is
  get-comment-tags-recursive."
  [expr]
  (cond
    (comment-tag? expr) (term/km-list expr)
    (term/cons? expr) (utils/mapcan-list comment-tags-recursive expr)
    :else nil))

(defn- length-of
  [expr]
  (loop [expr expr
         n 0]
    (cond
      (nil? expr) n
      (term/cons? expr) (recur (term/cdr expr) (inc n))
      :else n)))

(defn- nth-value
  [value n]
  (loop [value value
         n n]
    (cond
      (or (nil? value) (not (term/cons? value))) nil
      (zero? n) (term/car value)
      :else (recur (term/cdr value) (dec n)))))

(defn originated-from-class
  "The class a source names. (@ _Cell1 Cell has-part) is Class."
  [source]
  (nth-value source 2))

(def ^:private must-be-a-symbol (symbol "must-be-a"))
(def ^:private a-symbol (symbol "a"))
(def ^:private every-symbol (symbol "every"))
(def ^:private has-symbol (symbol "has"))
(def ^:private with-symbol (symbol "with"))
(def ^:private location-unknown (symbol "<location unknown>"))

(def ^:private kept-explanation-heads
  (set (map symbol ["every" "cloned-from" "added-at" "projected-from"])))

(defn- mentions?
  [expr symbols]
  (cond
    (nil? expr) false
    (term/cons? expr)
    (or (mentions? (term/car expr) symbols)
        (mentions? (term/cdr expr) symbols))
    :else (contains? symbols expr)))

(defn- build-embedded
  "An (a Class with ...) or (every Class has ...) for one source path."
  [path expr every-a has-with]
  (if (nil? path)
    (if (and (utils/eql? every-a must-be-a-symbol)
             (term/cons? expr)
             (utils/eql? (term/car expr) a-symbol))
      (term/cons-cell must-be-a-symbol (term/cdr expr))
      expr)
    (let [class (term/car path)
          slot0 (nth-value path 1)
          must? (and (term/pair? slot0)
                     (utils/eql? (nth-value slot0 1) must-be-a-symbol))
          slot (if must? (term/car slot0) slot0)
          nested (build-embedded (term/cdr (term/cdr path))
                                 expr
                                 (if must? must-be-a-symbol a-symbol)
                                 with-symbol)]
      (term/km-list every-a class has-with (term/km-list slot (term/km-list nested))))))

(defn build-rule
  "The KM rule one explanation prints as.

  cloned-from, added-at, projected-from, and every are returned as they
  are. A sourced value becomes (every Class has (slot (value))). A value
  with no source, or a source path of odd length, becomes
  (<location unknown> value). ignore-constraints? drops a path that
  names must-be-a, exactly, at-most, or at-least. The odd-path sentence
  is left for the caller."
  [expr & {:keys [ignore-constraints?]}]
  (cond
    (and (term/cons? expr) (contains? kept-explanation-heads (term/car expr))) expr
    :else
    (let [source (when (term/cons? expr) (term/car (sources expr)))
          path (source-path source)
          body (desource expr)]
      (cond
        (and ignore-constraints?
             (mentions? path annotated-constraints))
        nil
        (or (nil? path) (odd? (length-of path)))
        (term/km-list location-unknown body)
        :else (build-embedded path body every-symbol has-symbol)))))

(defn- desource1
  [expr]
  (cond
    (and (term/cons? expr)
         (= 3 (length-of expr))
         (utils/eql? (term/car expr) comm-symbol))
    (nth-value expr 1)
    (sourced-pair-collapses? expr) (desource1 (term/car expr))
    (term/cons? expr) (remove-when source? (map-proper desource1 expr))
    :else expr))

(defn desource-for-printing
  "The explanation text the printer shows.

  A (comm [tag] instance) becomes the tag. A sourced pair collapses to
  its value. Developer mode would keep the raw expression. That mode is
  off, so the printed form is this one."
  [expr]
  (desource1 expr))
