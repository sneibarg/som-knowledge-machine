(ns som.km.utils
  "List, set, and binding helpers from utils.lisp.

  These functions do not know about frames. A Knowledge Machine list is
  a cons chain. Nil is the empty list. The symbol nil is a different
  value. Multiple Lisp values are one map or one sequence."
  (:require [som.km.term :as term]))

(defn lisp-list?
  "Lisp listp. Nil and a cons are lists."
  [value]
  (or (nil? value) (term/cons? value)))

(defn lisp-atom?
  "Lisp atom. Nil is an atom. A cons is not."
  [value]
  (not (term/cons? value)))

(defn eql?
  "Lisp eql for the values this port stores.

  Two symbols match when their names match. Each read builds a fresh
  symbol object, and Lisp eql treats that name as one symbol. Two
  integers of the same numeric value match, including a long and a
  bigint. A long and a double do not. A ratio and a double do not."
  [left right]
  (cond
    (identical? left right) true
    (and (term/lisp-symbol? left) (term/lisp-symbol? right)) (= left right)
    (and (char? left) (char? right)) (= left right)
    (and (integer? left) (integer? right)) (== left right)
    (and (ratio? left) (ratio? right)) (== left right)
    (and (float? left) (float? right)) (== left right)
    :else false))

(defn equal?
  "Lisp equal.

  Cons cells match when their cars and cdrs match. Numbers follow eql?,
  so 1 and 1.0 do not match. The symbol nil does not match the empty list.
  Strings match by their characters."
  [left right]
  (cond
    (eql? left right) true
    (and (string? left) (string? right)) (= left right)
    (and (term/cons? left) (term/cons? right))
    (and (equal? (term/car left) (term/car right))
         (equal? (term/cdr left) (term/cdr right)))
    :else false))

(defn elements
  "The elements of a proper list, in order.

  Nil has none. A dotted list is an error. This is the walk minimatch
  uses when it appends captured pieces."
  [value]
  (loop [value value
         acc []]
    (cond
      (nil? value) acc
      (term/cons? value) (recur (term/cdr value) (conj acc (term/car value)))
      :else (throw (ex-info "This list is dotted." {:tail value})))))

(defn listify
  "A list stays a list. Any other value becomes a one-element list.

  Nil is a list, so it stays nil."
  [value]
  (if (lisp-list? value) value (term/km-list value)))

(defn append-lists
  "Append proper lists into one proper list."
  [lists]
  (loop [lists lists
         acc []]
    (cond
      (nil? lists) (term/build-list acc nil)
      (term/cons? lists)
      (recur (term/cdr lists) (into acc (elements (term/car lists))))
      :else (throw (ex-info "This list is dotted." {:tail lists})))))

(defn mapcan-list
  "Append the proper lists returned by f. This is my-mapcan."
  [f coll]
  (loop [coll coll
         acc []]
    (cond
      (nil? coll) (term/build-list acc nil)
      (term/cons? coll)
      (recur (term/cdr coll) (into acc (elements (f (term/car coll)))))
      :else (throw (ex-info "This list is dotted." {:tail coll})))))

(defn member?
  "True when an element of coll satisfies (test item element).

  The default test is eql?, which is the Lisp default. Lisp member
  returns the tail that starts at the element. Callers here only need
  the test."
  ([item coll]
   (member? item coll eql?))
  ([item coll test]
   (loop [coll coll]
     (cond
       (nil? coll) false
       (term/cons? coll)
       (if (test item (term/car coll))
         true
         (recur (term/cdr coll)))
       :else false))))

(defn remove-items
  "Remove elements that satisfy (test value element).

  :count is how many matches to remove. Omitted, every match is removed.
  The default test is eql?, which is the Lisp default."
  [value coll & {:keys [test] :or {test eql?} remove-count :count}]
  (loop [coll coll
         left remove-count
         acc []]
    (cond
      (nil? coll) (term/build-list acc nil)
      (not (term/cons? coll))
      (throw (ex-info "This list is dotted." {:tail coll}))
      (and (test value (term/car coll))
           (or (nil? left) (pos? left)))
      (recur (term/cdr coll) (when (some? left) (dec left)) acc)
      :else
      (recur (term/cdr coll) left (conj acc (term/car coll))))))

(defn remove-duplicates
  "Lisp remove-duplicates. The survivor stays in its original position.

  from-end? false, the default, keeps the later duplicate. (a b c b d d e)
  becomes (a c b d e). from-end? true keeps the earlier duplicate.
  An element is dropped when it matches a survivor already chosen from
  that end. The default test is eql?, which is the Lisp default.
  Pass equal? to compare structure."
  [coll & {:keys [test from-end?] :or {test eql? from-end? false}}]
  (let [items (elements coll)
        n (count items)]
    (if from-end?
      (loop [index 0
             kept []]
        (if (>= index n)
          (term/build-list kept nil)
          (let [item (nth items index)]
            (if (some #(test item %) kept)
              (recur (inc index) kept)
              (recur (inc index) (conj kept item))))))
      (loop [index (dec n)
             kept []]
        (if (neg? index)
          (term/build-list kept nil)
          (let [item (nth items index)]
            (if (some #(test item %) kept)
              (recur (dec index) kept)
              (recur (dec index) (into [item] kept)))))))))

(defn set-exclusive-or
  "Elements that appear on only one side, under test.

  This is the Lisp function of the same name. The result is empty when
  the two lists are the same set under test. The default test is eql?."
  [left right & {:keys [test] :or {test eql?}}]
  (let [only (fn [source other]
               (loop [source source
                      acc []]
                 (cond
                   (nil? source) acc
                   (term/cons? source)
                   (let [item (term/car source)]
                     (recur (term/cdr source)
                            (if (member? item other test) acc (conj acc item))))
                   :else (throw (ex-info "This list is dotted." {:tail source})))))]
    (term/build-list (into (only left right) (only right left)) nil)))

(defn quote?
  "True for a proper list (quote expr)."
  [expr]
  (and (term/pair? expr) (= (symbol "quote") (term/car expr))))

(defn unquote-expr
  "The expression inside (quote expr). This is unquote.

  An expression that is not quoted is returned unchanged. The Lisp
  prints a warning in that case."
  [expr]
  (if (quote? expr)
    (term/car (term/cdr expr))
    expr))

(def null-binding
  "The pair (t . t). It marks a successful match that bound nothing."
  (term/cons-cell (symbol "t") (symbol "t")))

(def null-bindings
  "The binding list ((t . t))."
  (term/km-list null-binding))

(defn bind
  "The dotted pair (var . value)."
  [var value]
  (term/cons-cell var value))

(defn bound-pair
  "The pair (var . value), or nil when var is unbound.

  This is var-boundp. Nil means unbound. A pair whose value is nil means
  the variable is bound to the empty list."
  [var bindings]
  (loop [bindings bindings]
    (cond
      (nil? bindings) nil
      (not (term/cons? bindings)) nil
      :else
      (let [pair (term/car bindings)]
        (if (and (term/cons? pair) (eql? var (term/car pair)))
          pair
          (recur (term/cdr bindings)))))))

(defn val-of
  "The value bound to var.

  Nil means the variable is unbound or bound to the empty list. bound-pair
  tells those two apart."
  [var bindings]
  (let [pair (bound-pair var bindings)]
    (when pair (term/cdr pair))))

(defn- append-two [left right]
  (term/build-list (into (elements left) (elements right)) nil))

(defn combine-bindings
  "Append two binding lists.

  A repeated pair is kept once, and the earlier copy survives. The null
  binding (t . t) is removed. When nothing remains, the result is
  null-bindings."
  [bindings1 bindings2]
  (let [combined (remove-duplicates (append-two bindings1 bindings2)
                                    :test equal?
                                    :from-end? true)
        without-null (remove-items null-binding combined :test equal?)]
    (if (nil? without-null) null-bindings without-null)))

(defn add-binding
  "Add (var . value) to bindings.

  When var and value are eql, the bindings are unchanged. When that same
  pair is already present, the bindings are unchanged. A different value
  for the same var is a second pair. val-of returns the earliest one."
  [var value bindings]
  (cond
    (eql? var value) bindings
    (member? (bind var value) bindings equal?) bindings
    :else (combine-bindings bindings (term/km-list (bind var value)))))
