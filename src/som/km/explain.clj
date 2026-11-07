(ns som.km.explain
  "Comment tags and source markers from explain.lisp.

  A user comment is a symbol whose name starts with [ and ends with ].
  It is stored later as (comm [tag] Self). A source is a list whose first
  element is the symbol @. Neither one is a slot value. This namespace
  recognizes them and strips them. It does not record explanations."
  (:require [som.km.term :as term]))

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
