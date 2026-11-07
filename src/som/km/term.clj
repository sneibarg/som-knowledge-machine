(ns som.km.term
  "Knowledge Machine values.

  The empty list is Clojure nil, as it is in Lisp. The symbol nil is a
  different value, and so are the symbols t and f: they are not true or
  false. A proper list is a chain of cons cells ending in nil. A dotted
  pair keeps an atom in the final cdr, which a Clojure list cannot do."
  )

(defrecord Cons [car cdr])

(def global-situation
  "The global situation's name. The Lisp source writes it as |*Global|."
  (symbol "*Global"))

(def structured-keywords
  "Heads of structured values. A set is not a structured value."
  #{:seq :bag :args :triple :pair :function})

(defn cons-cell
  "One cons cell. The cdr is nil, another cell, or an improper tail."
  [head tail]
  (->Cons head tail))

(defn cons?
  "True for a Knowledge Machine cons cell."
  [value]
  (instance? Cons value))

(defn build-list
  "Cons the elements, in order, onto tail. A nil tail builds a proper list."
  [elems tail]
  (loop [pending (reverse (vec elems))
         built tail]
    (if (empty? pending)
      built
      (recur (rest pending) (->Cons (first pending) built)))))

(defn km-list
  "A proper list of the arguments, in that order. No arguments is nil."
  [& elems]
  (build-list elems nil))

(defn car
  "The head of a cons cell. Nil has no head."
  [value]
  (cond
    (nil? value) nil
    (cons? value) (:car value)
    :else (throw (ex-info "car expects a list." {:value value}))))

(defn cdr
  "The tail of a cons cell. Nil has no tail."
  [value]
  (cond
    (nil? value) nil
    (cons? value) (:cdr value)
    :else (throw (ex-info "cdr expects a list." {:value value}))))

(defn proper?
  "True for nil or a cons chain that ends in nil."
  [value]
  (loop [value value]
    (cond
      (nil? value) true
      (cons? value) (recur (cdr value))
      :else false)))

(defn singleton?
  "True for a proper list of one element."
  [value]
  (and (cons? value) (nil? (cdr value))))

(defn pair?
  "True for a proper list of exactly two elements."
  [value]
  (and (cons? value)
       (cons? (cdr value))
       (nil? (cdr (cdr value)))))

(defn triple?
  "True for a proper list of exactly three elements."
  [value]
  (and (cons? value)
       (cons? (cdr value))
       (cons? (cdr (cdr value)))
       (nil? (cdr (cdr (cdr value))))))

(defn delistify
  "The element of a one-element list. Any other value is returned as it is."
  [value]
  (if (singleton? value) (car value) value))

(defn km-symbol?
  "True for a symbol interned with no namespace. Keywords are not included."
  [value]
  (and (symbol? value) (nil? (namespace value))))

(defn lisp-symbol?
  "Lisp symbolp. A keyword is a symbol in Lisp, and symbol? in Clojure is false for it."
  [value]
  (or (keyword? value) (km-symbol? value)))

(defn symbol-name
  "The stored name of a Knowledge Machine symbol or keyword."
  [value]
  (cond
    (keyword? value) (name value)
    (km-symbol? value) (name value)
    :else (throw (ex-info "Expected a symbol." {:value value}))))

(defn structured-list?
  "True for a :seq, :bag, :args, :triple, :pair, or :function value."
  [value]
  (and (cons? value) (contains? structured-keywords (car value))))
