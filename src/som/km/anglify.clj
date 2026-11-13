(ns som.km.anglify
  "Turn a Knowledge Machine expression into one English string.

  make-sentence flattens a value, or a :set or :seq of values, and joins
  the pieces. An instance is replaced by (the name of instance) until
  that lookup returns the instance. make-phrase is the same string
  without a capital or a terminator. The interpreter is passed in as
  km-int, so this namespace does not require it. htmlify is accepted
  and does not change the text: the HTML wrapper returns nothing."
  (:require [clojure.string :as str]
            [som.km.errors :as errors]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.print :as print]
            [som.km.strings :as strings]
            [som.km.taxonomy :as taxonomy]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(def ^:private whitespace
  #{\space \tab \newline \return \formfeed})

(def ^:private structure-words
  #{:seq :set :bag :pair})

(def ^:private dropped-words
  #{:seq :set :triple})

(defn- refused?
  [state]
  (= "not-ported" (:error state)))

(defn- stopped?
  [result]
  (or (refused? result)
      (refused? (:state result))))

(defn- fail
  [state template & args]
  {:state (apply errors/report-error state :user-error template args)
   :value nil})

(defn- default-expand?
  [state]
  (get-in state [:kb :runtime :default-km-behavior-for-expand-text?] true))

(defn- princ-to-string
  "The characters princ would write for a number or a symbol name."
  [value]
  (cond
    (ratio? value) (str (numerator value) "/" (denominator value))
    (number? value) (str value)
    :else (str value)))

(defn- fixed
  [value digits]
  (String/format java.util.Locale/US
                 (str "%." (max 0 (long digits)) "f")
                 (object-array [(double value)])))

(defn- scientific
  [value digits]
  (String/format java.util.Locale/US
                 (str "%." (max 0 (long digits)) "e")
                 (object-array [(double value)])))

(defn- trim-zeros
  [text]
  (if (str/includes? text ".")
    (str/replace text #"0+$" "")
    text))

(defn- format-number
  "A number for expand-text.

  An integer stays a number, so later printing has no decimal part.
  *verbose-number-to-text* wraps it as (\"the value\" n). A float uses
  *output-precision*, which starts at 3."
  [state value]
  (let [verbose? (get-in state [:kb :runtime :verbose-number-to-text?] false)
        precision (get-in state [:kb :runtime :output-precision] 3)]
    (cond
      verbose? (term/km-list "the value" value)
      (integer? value) value
      (not (number? precision)) value
      (>= (double value) 1.0) (fixed value precision)
      (>= (double value) (Math/pow 10 (- (double precision))))
      (trim-zeros (fixed value
                         (- (long precision)
                            (long (Math/floor (Math/log10 (double value)))))))
      :else (scientific value precision))))

(defn- atomic-cons?
  [value]
  (and (term/cons? value)
       (utils/lisp-atom? (term/car value))
       (utils/lisp-atom? (term/cdr value))))

(defn- flatten-aux
  [value acc]
  (cond
    (nil? value) acc
    (atomic-cons? value) (conj acc (term/car value) (term/cdr value))
    (term/cons? value)
    (flatten-aux (term/cdr value) (flatten-aux (term/car value) acc))
    :else (conj acc value)))

(defn- flatten-km
  "flatten from utils.lisp. A one-element list keeps the empty tail.

  The sentence builder drops that empty tail later."
  [value]
  (if (atomic-cons? value)
    [(term/car value) (term/cdr value)]
    (flatten-aux value [])))

(defn- trim-whitespace
  [text]
  (let [n (count text)]
    (loop [start 0]
      (if (and (< start n) (contains? whitespace (nth text start)))
        (recur (inc start))
        (loop [end n]
          (if (and (> end start)
                   (contains? whitespace (nth text (dec end))))
            (recur (dec end))
            (subs text start end)))))))

(defn- ends-with?
  [text ending]
  (and (>= (count text) (count ending))
       (= ending (subs text (- (count text) (count ending))))))

(defn- first-char
  [text]
  (when (and (string? text) (pos? (count text)))
    (nth text 0)))

(defn- last-char
  [text]
  (when (and (string? text) (pos? (count text)))
    (nth text (dec (count text)))))

(defn- butfirst
  [text]
  (if (and (string? text) (pos? (count text)))
    (subs text 1)
    ""))

(defn- capitalize-word
  [text]
  (if (or (nil? text) (= text ""))
    ""
    (str (str/upper-case (subs text 0 1)) (subs text 1))))

(defn- space-or-tab-only?
  [text]
  (or (= text "")
      (every? #{\space \tab} text)))

(defn- a-space
  [left right]
  (cond
    (contains? #{\( \space} (last-char left)) ""
    (contains? #{\' \) \. \, \space} (first-char right)) ""
    :else " "))

(defn- spacify-list
  [words]
  (cond
    (empty? words) []
    (= (count words) 1) [(first words)]
    (space-or-tab-only? (nth words 1))
    (recur (into [(first words)] (subvec words 2)))
    (= (first words) ".")
    (if (and (= (nth words 1) "\n") (> (count words) 2))
      (into ["." "\n"]
            (spacify-list (into [(capitalize-word (nth words 2))]
                                (subvec words 3))))
      (into [". "]
            (spacify-list (into [(capitalize-word (nth words 1))]
                                (subvec words 2)))))
    (= (first words) "nospace")
    (recur (subvec words 1))
    (= (nth words 1) "nospace")
    (into [(first words)] (spacify-list (subvec words 2)))
    :else
    (into [(first words) (a-space (first words) (nth words 1))]
          (spacify-list (subvec words 1)))))

(defn- symbol-word?
  [value]
  (or (term/km-symbol? value) (keyword? value)))

(defn- down-name
  [value]
  (str/lower-case (term/symbol-name value)))

(defn- starts-with-char?
  [value ch]
  (and (symbol-word? value)
       (let [label (term/symbol-name value)]
         (and (pos? (count label))
              (= ch (nth label 0))))))

(defn- sririam-symbol?
  [item]
  (and (symbol-word? item)
       (not (contains? #{:seq :set (symbol "nil") nil} item))
       (not (kb/kb-object? item))
       (not (kb/km-triple? item))))

(defn- unique-call
  [state expr km-int unique]
  (if (some? unique)
    (unique state expr)
    (let [found (km-int state expr)]
      (cond
        (refused? found) found
        (term/singleton? (:value found))
        (assoc found :value (term/car (:value found)))
        (some? (:value found))
        (assoc found :value (term/car (:value found)))
        :else found))))

(defn- lookup-name
  [state concept km-int unique]
  (if-not (kb/kb-object? concept)
    {:state state :value nil}
    (let [expr (term/km-list (symbol "the") (symbol "name") (symbol "of") concept)
          asked (km-int state expr)]
      (cond
        (refused? asked) {:state asked :value nil}
        (some? (:value asked)) {:state asked :value (term/car (:value asked))}
        :else
        (let [again (unique-call asked expr km-int unique)]
          (if (refused? again)
            {:state again :value nil}
            {:state again :value (:value again)}))))))

(defn- andify-seq
  [items]
  (case (count items)
    0 []
    1 [(first items)]
    2 [(first items) " and " (second items)]
    3 [(first items) ", " (second items) ", and " (nth items 2)]
    (into [(first items) ", "] (andify-seq (subvec (vec items) 1)))))

(defn andify
  "The list (andify ...) builds before it wraps :seq around it.

  No values is nil. One value is a one-element list. Two values use
  \" and \". Longer lists use a comma and a final \", and \"."
  [vals]
  (term/build-list (andify-seq (if (nil? vals) [] (vec (utils/elements vals)))) nil))

(declare expand-text0 km-name)

(defn- name-each
  [state items km-int unique]
  (loop [items items
         state state
         acc []]
    (if (empty? items)
      {:state state :names acc}
      (let [named (km-name state (first items) km-int :unique unique)]
        (if (stopped? named)
          named
          (recur (rest items) (:state named) (conj acc (:value named))))))))

(defn- object-name
  [state vals km-int unique]
  (cond
    (nil? vals) {:state state :value nil}
    (term/singleton? vals) (km-name state (term/car vals) km-int :unique unique)
    :else
    (let [named (name-each state (utils/elements vals) km-int unique)]
      (if (stopped? named)
        named
        {:state (:state named)
         :value (term/cons-cell :seq (andify (term/build-list (:names named) nil)))}))))

(defn- triple-name
  [state triple km-int unique]
  (let [subject (km-name state (kb/arg1 triple) km-int :unique unique)]
    (if (stopped? subject)
      subject
      (let [predicate (km-name (:state subject) (kb/arg2 triple) km-int :unique unique)]
        (if (stopped? predicate)
          predicate
          (let [object (object-name (:state predicate)
                                    (kb/val-to-vals (kb/arg3 triple))
                                    km-int unique)]
            (if (stopped? object)
              object
              {:state (:state object)
               :value (term/km-list :seq
                                    (:value subject)
                                    (:value predicate)
                                    (:value object))})))))))

(defn- anonymous-name
  [state concept km-int unique]
  (let [classes (taxonomy/immediate-classes (:kb state) concept)
        parent (when (some? (:value classes)) (term/car (:value classes)))
        named (if (some? parent)
                 (km-name (assoc state :kb (:kb classes)) parent km-int :unique unique)
                 {:state (assoc state :kb (:kb classes)) :value nil})]
    (if (stopped? named)
      named
      (assoc named :value (term/km-list :seq "the" (:value named))))))

(defn- restore-trace
  "Put the saved trace flag back on a name result or a refused state."
  [result saved]
  (cond
    (and (map? result) (map? (:state result)))
    (assoc result :state (assoc-in (:state result) [:kb :runtime :trace?] saved))
    (and (map? result) (map? (:kb result)))
    (assoc-in result [:kb :runtime :trace?] saved)
    :else result))

(defn- call-with-trace-off
  "Run f with tracing off, then restore the flag the caller had.

  The lookup does not require the trace namespace. An abort restores the
  flag on the knowledge base at the error."
  [state f]
  (let [saved (get-in state [:kb :runtime :trace?] false)
        quiet (assoc-in state [:kb :runtime :trace?] false)]
    (try
      (restore-trace (f quiet) saved)
      (catch clojure.lang.ExceptionInfo thrown
        (if (errors/abort-exception? thrown)
          (let [data (ex-data thrown)]
            (throw (ex-info (.getMessage thrown)
                            (assoc data :state (restore-trace (:state data) saved))
                            thrown)))
          (throw thrown))))))

(defn km-name
  "The name structure for one concept, before it is flattened.

  A stored (the name of concept) is used when it returns one value.
  Several names keep the first. The warning for that is not recorded,
  because that comment stays silent. The lookup runs with trace off,
  and the flag is restored on the way out. An anonymous instance becomes
  (:seq \"the\" class). *pete drops the star. A class name is lower
  case when the default expansion is on."
  [state concept km-int & {:keys [unique]}]
  (call-with-trace-off
   state
   (fn [state]
     (cond
       (string? concept) {:state state :value concept}
       (number? concept) {:state state :value (princ-to-string concept)}
       (kb/km-triple? concept) (triple-name state concept km-int unique)
       :else
       (let [named (lookup-name state concept km-int unique)]
         (cond
           (stopped? named) named
           (some? (:value named)) named
           (starts-with-char? concept \*)
           {:state (:state named)
            :value (butfirst (down-name concept))}
           (and (term/km-symbol? concept)
                (frame/anonymous-instance? (:kb (:state named)) concept))
           (anonymous-name (:state named) concept km-int unique)
           (symbol-word? concept)
           {:state (:state named)
            :value (if (default-expand? (:state named))
                     (down-name concept)
                     (term/symbol-name concept))}
           :else {:state (:state named) :value concept}))))))

(defn- expand-element
  [state item km-int unique depth]
  (if (and (not (default-expand? state))
           (sririam-symbol? item))
    (expand-text0 state (term/symbol-name item) km-int unique depth)
    (expand-text0 state item km-int unique depth)))

(defn- expand-list
  [state items km-int unique depth]
  (loop [items items
         state state
         acc []]
    (cond
      (nil? items) {:state state :value (term/build-list acc nil)}
      (not (term/cons? items))
      {:state state :value (term/build-list acc nil)}
      :else
      (let [one (expand-element state (term/car items) km-int unique depth)]
        (if (stopped? one)
          one
          (recur (term/cdr items) (:state one) (conj acc (:value one))))))))

(defn- expand-text0
  [state item km-int unique depth]
  (cond
    (> depth 100)
    (fail state
          "make-sentence/phrase: Infinite recursion when generating name for %s!"
          (print/km-format item))

    (string? item) {:state state :value item}

    (number? item) {:state state :value (format-number state item)}

    (and (nil? item) (get-in state [:kb :runtime :developer-mode?] false))
    {:state state :value (term/km-list "??")}

    (utils/lisp-list? item)
    (expand-list state item km-int unique (inc depth))

    (contains? structure-words item) {:state state :value item}

    (or (kb/kb-object? item) (kb/km-triple? item))
    (let [named (km-name state item km-int :unique unique)]
      (cond
        (stopped? named) named
        (utils/equal? (:value named) item) named
        :else (expand-text0 (:state named) (:value named) km-int unique (inc depth))))

    :else
    (fail state
          "make-sentence/phrase: Bad element `%s' encountered!!"
          (print/km-format item))))

(defn expand-text
  "The expanded name of item.

  :seq markers are removed. One remaining piece is returned alone. A
  longer result is wrapped in :seq again. The interpreter is km-int."
  [state item km-int & {:keys [unique depth] :or {depth 0}}]
  (let [inner (expand-text0 state item km-int unique depth)]
    (if (stopped? inner)
      inner
      (let [flat (filterv #(not= :seq %) (flatten-km (:value inner)))]
        {:state (:state inner)
         :value (cond
                  (empty? flat) nil
                  (= (count flat) 1) (first flat)
                  :else (term/cons-cell :seq (term/build-list flat nil)))}))))

(defn- stringify
  [state items]
  (loop [items items
         state state
         acc []]
    (cond
      (empty? items) {:state state :words acc}
      (nil? (first items)) (recur (rest items) state acc)
      (string? (first items)) (recur (rest items) state (conj acc (first items)))
      (number? (first items))
      (recur (rest items) state (conj acc (princ-to-string (first items))))
      (contains? dropped-words (first items)) (recur (rest items) state acc)
      (symbol-word? (first items))
      (recur (rest items) state (conj acc (down-name (first items))))
      :else
      {:state (errors/report-error
               state :user-error
               "make-sentence/phrase: Don't know how to convert %s to a string!"
               (print/km-format (first items)))
       :words acc})))

(defn make-sentence
  "One string from text, capitalized and terminated.

  text may be one expression or a :set or :seq of them. :set and :seq
  are dropped and the order of the pieces is kept. capitalize? starts
  true. terminator starts as \".\". An empty result stays empty and
  gains neither a capital nor a terminator. unique is km-unique-int
  when the caller has it."
  [state text km-int & {:keys [capitalize? terminator unique]
                        :or {capitalize? true terminator "."}}]
  (let [expanded (expand-text state text km-int :unique unique)]
    (if (stopped? expanded)
      (assoc expanded :text nil)
      (let [words (stringify (:state expanded)
                             (flatten-km (if (utils/lisp-list? (:value expanded))
                                           (:value expanded)
                                           (term/km-list (:value expanded)))))]
        (if (stopped? words)
          (assoc words :text nil)
          (let [joined (trim-whitespace
                        (strings/concat-list (spacify-list (vec (:words words)))))
                done (cond
                       (= joined "") ""
                       (ends-with? joined (or terminator "")) joined
                       :else (str joined terminator))]
            {:state (:state words)
             :text (if (and capitalize? (not= done ""))
                     (capitalize-word done)
                     done)}))))))

(defn make-phrase
  "make-sentence with no capital and no terminator."
  [state text km-int & {:keys [unique]}]
  (make-sentence state text km-int
                 :capitalize? false
                 :terminator ""
                 :unique unique))
