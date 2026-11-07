(ns som.km.minimatch
  "Pattern matching from minimatch.lisp.

  minimatch returns the matched pieces in the order the variables were
  encountered. The variable names are ignored, so two uses of ?x may
  match different objects. ?any, ?ANY, and ?* match and return nothing.
  &rest returns the rest of the list as one piece.

  full-match returns a binding list. A repeated variable is recorded
  again when the new value differs. val-of returns the earliest pair.
  The header comment in the Lisp says a repeated variable must match
  the same object. add-binding does not check that.

  A match with no captured pieces is the symbol t. Failure is nil.
  full-match uses ((t . t)) for a success that bound nothing."
  (:require [som.km.term :as term]
            [som.km.utils :as utils]))

(def ^:private success (symbol "t"))

(def ^:private anonymous-names #{"?ANY" "?any" "?*"})

(def ^:private rest-names
  #{"&rest" "&rest1" "&rest2" "&rest3" "&rest4" "&rest5"})

(defn anonymous-var?
  "True for ?any, ?ANY, and ?*. The matched text is not returned."
  [value]
  (and (term/km-symbol? value) (contains? anonymous-names (name value))))

(defn wildcard-var?
  "True for ?*. It can consume several elements of a list."
  [value]
  (= value (symbol "?*")))

(defn variable?
  "True for a symbol or keyword whose name starts with ?. This is var-p."
  [value]
  (and (term/lisp-symbol? value)
       (let [name (term/symbol-name value)]
         (and (pos? (count name)) (= \? (nth name 0))))))

(defn rest-var?
  "True for &rest and &rest1 through &rest5."
  [value]
  (and (term/km-symbol? value) (contains? rest-names (name value))))

(defn- join-binds [left right]
  (cond
    (or (nil? left) (nil? right)) nil
    (= left success) right
    (= right success) left
    :else (term/build-list (into (utils/elements left) (utils/elements right)) nil)))

(defn minimatch
  "Match item against pattern.

  Returns the symbol t when the match captures nothing, a list of the
  captured pieces, or nil when it fails."
  [item pattern]
  (cond
    (anonymous-var? pattern) success
    (variable? pattern) (term/km-list item)
    (and (term/singleton? pattern) (rest-var? (term/car pattern)))
    (term/km-list item)
    (utils/lisp-atom? pattern)
    (when (utils/equal? item pattern) success)
    (utils/lisp-list? item)
    (cond
      (and (term/cons? pattern) (wildcard-var? (term/car pattern)))
      (or (minimatch item (term/cdr pattern))
          (and (term/cons? item)
               (minimatch (term/cdr item) (term/cdr pattern)))
          (and (term/cons? item)
               (minimatch (term/cdr item) pattern)))
      (term/cons? item)
      (let [head (minimatch (term/car item) (term/car pattern))]
        (when head
          (join-binds head (minimatch (term/cdr item) (term/cdr pattern))))))
    :else nil))

(defn minimatch1
  "The one piece captured by pattern.

  Nil when the match fails. The Lisp first of a no-capture success
  errors, because that success is the symbol t rather than a list."
  [item pattern]
  (let [matched (minimatch item pattern)]
    (cond
      (nil? matched) nil
      (term/cons? matched) (term/car matched)
      :else (throw (ex-info "minimatch1 expects a pattern that captures one value."
                            {:matched matched})))))

(defn- remove-equal [value coll]
  (utils/remove-items value coll :test utils/equal?))

(defn minimatch-pattern
  "Match each pattern against a different element of coll.

  The captured pieces are appended. An element can satisfy only one
  pattern. Every structurally equal copy of the chosen element is
  removed before the remaining patterns run, which is Lisp remove
  without a count. The pattern list (&rest) captures everything still
  unmatched."
  [coll patterns]
  (cond
    (nil? patterns) success
    (utils/equal? patterns (term/km-list (symbol "&rest")))
    (term/km-list coll)
    :else
    (let [pattern (term/car patterns)]
      (loop [pending coll]
        (cond
          (nil? pending) nil
          (not (term/cons? pending)) nil
          :else
          (let [element (term/car pending)
                first-match (minimatch element pattern)
                rest-match (when first-match
                             (minimatch-pattern (remove-equal element coll)
                                                (term/cdr patterns)))
                joined (join-binds first-match rest-match)]
            (if joined
              joined
              (recur (term/cdr pending)))))))))

(defn find-pattern
  "The minimatch result of the first element that matches pattern."
  [coll pattern]
  (loop [coll coll]
    (cond
      (nil? coll) nil
      (not (term/cons? coll)) nil
      :else
      (or (minimatch (term/car coll) pattern)
          (recur (term/cdr coll))))))

(defn find-pattern1
  "The first captured piece of the first element that matches pattern."
  [coll pattern]
  (let [matched (find-pattern coll pattern)]
    (cond
      (nil? matched) nil
      (term/cons? matched) (term/car matched)
      :else (throw (ex-info "find-pattern1 expects a pattern that captures one value."
                            {:matched matched})))))

(defn- handler-entry
  "One pattern and its handler.

  A cons cell is a record, and a record answers map?, so the list test
  comes first."
  [entry]
  (cond
    (term/pair? entry) {:pattern (term/car entry)
                        :handler (term/car (term/cdr entry))}
    (and (vector? entry) (= 2 (count entry)))
    {:pattern (first entry) :handler (second entry)}
    (map? entry) entry
    :else (throw (ex-info "A handler entry is a pattern and a function."
                          {:entry entry}))))

(defn- handler-entries [handlers]
  (cond
    (nil? handlers) []
    (term/cons? handlers) (mapv handler-entry (utils/elements handlers))
    (sequential? handlers) (mapv handler-entry handlers)
    :else (throw (ex-info "Handlers are a list of pattern and function entries."
                          {:handlers handlers}))))

(defn find-handler
  "The first handler whose pattern matches expr.

  Returns {:handler :bindings :pattern}. :bindings is nil when the
  pattern captures nothing. fail-mode :fail returns nil when nothing
  matches. fail-mode :error throws. The Lisp prints the error and
  returns nil."
  [expr handlers & {:keys [fail-mode] :or {fail-mode :fail}}]
  (loop [entries (handler-entries handlers)]
    (if (empty? entries)
      (when (= fail-mode :error)
        (throw (ex-info (str "Can't find a handler for " expr ".") {:expr expr})))
      (let [{:keys [pattern handler]} (first entries)
            matched (minimatch expr pattern)]
        (cond
          (= matched success) {:handler handler :bindings nil :pattern pattern}
          (some? matched) {:handler handler :bindings matched :pattern pattern}
          :else (recur (rest entries)))))))

(defn apply-handler
  "Call the handler with the captured pieces. No pieces means no arguments."
  [{:keys [handler bindings]}]
  (apply handler (utils/elements bindings)))

(defn find-and-apply-handler
  "Find a handler for expr and call it. Nil when none matches."
  [expr handlers & {:keys [fail-mode] :or {fail-mode :fail}}]
  (when-let [found (find-handler expr handlers :fail-mode fail-mode)]
    (apply-handler found)))

(defn full-match
  "Match item against pattern and return a binding list.

  Failure is nil. A success that binds nothing is ((t . t)). A variable
  is the pair (var . value). ?any adds nothing. &rest binds the rest of
  the list. ?* is not a wildcard here. The same var with a different
  value adds another pair, and the earliest pair is the one val-of
  returns."
  ([item pattern]
   (full-match item pattern utils/null-bindings))
  ([item pattern bindings]
   (cond
     (anonymous-var? pattern) bindings
     (variable? pattern) (utils/add-binding pattern item bindings)
     (and (term/singleton? pattern) (rest-var? (term/car pattern)))
     (utils/add-binding (term/car pattern) item bindings)
     (utils/lisp-atom? pattern)
     (when (utils/equal? item pattern) bindings)
     (and (utils/lisp-list? item) (term/cons? item))
     (when-let [updated (full-match (term/car item) (term/car pattern) bindings)]
       (full-match (term/cdr item) (term/cdr pattern) updated))
     :else nil)))

(defn- lower-case [text]
  (let [out (StringBuilder. (count text))]
    (dotimes [index (count text)]
      (.append out (Character/toLowerCase ^char (.charAt ^String text index))))
    (str out)))

(defn- prefix-at?
  [text anchor start case-sensitive?]
  (let [end (+ start (count anchor))]
    (and (<= end (count text))
         (if case-sensitive?
           (= (subs text start end) anchor)
           (= (lower-case (subs text start end)) (lower-case anchor))))))

(defn- find-anchor [text anchor case-sensitive?]
  (let [last-start (- (count text) (count anchor))]
    (loop [start 0]
      (cond
        (neg? last-start) nil
        (> start last-start) nil
        (prefix-at? text anchor start case-sensitive?) start
        :else (recur (inc start))))))

(defn- or-head? [value]
  (and (term/cons? value) (= (symbol "or") (term/car value))))

(defn- anchor-strings [value]
  (cond
    (string? value) [value]
    (and (or-head? value)
         (loop [items (term/cdr value)]
           (cond
             (nil? items) true
             (and (term/cons? items) (string? (term/car items)))
             (recur (term/cdr items))
             :else false)))
    (utils/elements (term/cdr value))
    :else nil))

(defn- cons-binding [binding bindings]
  (cond
    (or (nil? bindings) (nil? binding)) nil
    (= bindings success) (term/km-list binding)
    :else (term/cons-cell binding bindings)))

(defn string-match
  "Match a string against a pattern of strings and variables.

  The captured pieces are substrings. A match that captures nothing is
  the symbol t. Failure is nil. The match is case-insensitive unless
  case-sensitive? is true. (or \"a\" \"b\") tries each alternative.
  A variable uses the first place its following string occurs. It does
  not try a later copy when the rest of the pattern fails."
  [text pattern & {:keys [case-sensitive?] :or {case-sensitive? false}}]
  (let [pattern-el (when (term/cons? pattern) (term/car pattern))]
    (cond
      (nil? pattern) (when (= text "") success)
      (and (term/singleton? pattern) (rest-var? pattern-el))
      (term/km-list text)
      (or-head? pattern-el)
      (loop [alts (term/cdr pattern-el)]
        (cond
          (nil? alts) nil
          (not (term/cons? alts)) nil
          :else
          (or (string-match text
                            (term/cons-cell (term/car alts) (term/cdr pattern))
                            :case-sensitive? case-sensitive?)
              (recur (term/cdr alts)))))
      (string? pattern-el)
      (when (prefix-at? text pattern-el 0 case-sensitive?)
        (string-match (subs text (count pattern-el))
                      (term/cdr pattern)
                      :case-sensitive? case-sensitive?))
      (and (anonymous-var? pattern-el) (term/singleton? pattern))
      success
      (and (variable? pattern-el) (term/singleton? pattern))
      (term/km-list text)
      (variable? pattern-el)
      (let [anchors (anchor-strings (term/car (term/cdr pattern)))]
        (loop [anchors anchors]
          (when (seq anchors)
            (let [anchor (first anchors)
                  at (find-anchor text anchor case-sensitive?)]
              (if (nil? at)
                (recur (rest anchors))
                (let [rest-matches (string-match (subs text (+ at (count anchor)))
                                                 (term/cdr (term/cdr pattern))
                                                 :case-sensitive? case-sensitive?)]
                  (or (if (anonymous-var? pattern-el)
                        rest-matches
                        (cons-binding (subs text 0 at) rest-matches))
                      (recur (rest anchors)))))))))
      (term/singleton? pattern)
      (string-match text pattern-el :case-sensitive? case-sensitive?)
      :else nil)))

(defn string-match1
  "The one substring captured by pattern."
  [text pattern & {:keys [case-sensitive?] :or {case-sensitive? false}}]
  (let [matched (string-match text pattern :case-sensitive? case-sensitive?)]
    (cond
      (nil? matched) nil
      (term/cons? matched) (term/car matched)
      :else (throw (ex-info "string-match1 expects a pattern that captures one value."
                            {:matched matched})))))
