(ns som.km.read
  "Read one Knowledge Machine expression.

  This is not clojure.core/read and not EDN. The Lisp reader keeps the
  case of every symbol, treats #| ... |# as a comment, and installs #$
  #t and #, as dispatch macros. #: reads an uninterned name and interns
  it here. #. and #= would evaluate Lisp while reading, and those are
  refused."
  (:require [clojure.string :as str]
            [som.km.print :as print]
            [som.km.term :as term]))

(def ^:private whitespace #{\space \tab \newline \return \u000c})

(def ^:private terminating #{\( \) \" \' \` \, \;})

(def ^:private ascii-digits #{\0 \1 \2 \3 \4 \5 \6 \7 \8 \9})

(def ^:private ratio-re #"[+-]?\d+/\d+")

(def ^:private number-re #"[+-]?(?:\d+\.\d*|\.\d+|\d+)(?:[eEsSfFdDlL][+-]?\d+)?")

(defn- fail!
  [index message incomplete?]
  (throw (ex-info message {:km/read true
                           :index index
                           :incomplete incomplete?
                           :error "read"})))

(defn- eof!
  [index what]
  (fail! index (str "The " what " ended early.") true))

(defn- digit? [ch]
  (contains? ascii-digits ch))

(defn- skip-line
  [text index]
  (loop [index index]
    (if (or (>= index (count text)) (= \newline (nth text index)))
      index
      (recur (inc index)))))

(defn- skip-block
  "Index after a #| comment that opened before index. Comments nest."
  [text index depth]
  (loop [index index
         depth depth]
    (cond
      (>= index (count text)) (eof! index "comment")
      (and (= \# (nth text index))
           (< (inc index) (count text))
           (= \| (nth text (inc index))))
      (recur (+ index 2) (inc depth))
      (and (= \| (nth text index))
           (< (inc index) (count text))
           (= \# (nth text (inc index))))
      (if (= depth 1)
        (+ index 2)
        (recur (+ index 2) (dec depth)))
      :else (recur (inc index) depth))))

(defn- skip
  [text index]
  (loop [index index]
    (if (>= index (count text))
      index
      (let [ch (nth text index)]
        (cond
          (whitespace ch) (recur (inc index))
          (= ch \;) (recur (skip-line text (inc index)))
          (and (= ch \#)
               (< (inc index) (count text))
               (= \| (nth text (inc index))))
          (recur (skip-block text (+ index 2) 1))
          :else index)))))

(defn- read-string-literal
  [text index]
  (loop [index index
         out (StringBuilder.)]
    (cond
      (>= index (count text)) (eof! index "string")
      (= \" (nth text index)) [(str out) (inc index)]
      (= \\ (nth text index))
      (if (>= (inc index) (count text))
        (eof! index "string")
        (recur (+ index 2) (.append out (nth text (inc index)))))
      :else (recur (inc index) (.append out (nth text index))))))

(defn- read-token
  "Pieces of one symbol or number token, and the index after it.
  Each piece is {:ch character :escaped? bool}."
  [text index]
  (loop [index index
         pieces []
         escaped? false
         in-bar? false]
    (cond
      (>= index (count text))
      (if in-bar?
        (eof! index "symbol")
        [{:pieces pieces :escaped? escaped?} index])

      in-bar?
      (let [ch (nth text index)]
        (cond
          (= ch \\)
          (if (>= (inc index) (count text))
            (eof! index "symbol")
            (recur (+ index 2)
                   (conj pieces {:ch (nth text (inc index)) :escaped? true})
                   true
                   true))
          (= ch \|) (recur (inc index) pieces true false)
          :else (recur (inc index) (conj pieces {:ch ch :escaped? true}) true true)))

      :else
      (let [ch (nth text index)]
        (cond
          (= ch \\)
          (if (>= (inc index) (count text))
            (eof! index "symbol")
            (recur (+ index 2)
                   (conj pieces {:ch (nth text (inc index)) :escaped? true})
                   true
                   false))
          (= ch \|) (recur (inc index) pieces true true)
          (or (whitespace ch) (terminating ch))
          [{:pieces pieces :escaped? escaped?} index]
          :else (recur (inc index)
                       (conj pieces {:ch ch :escaped? false})
                       escaped?
                       false))))))

(defn- raw-name [pieces]
  (apply str (map :ch pieces)))

(defn- number-kind
  [token]
  (cond
    (re-matches ratio-re token) :ratio
    (re-matches number-re token)
    (if (or (str/includes? token ".") (re-find #"[eEsSfFdDlL]" token))
      :float
      :integer)
    :else nil))

(defn- parse-integer [token]
  (try
    (Long/parseLong token)
    (catch NumberFormatException _
      (bigint (BigInteger. token)))))

(defn- normalize-float [token]
  (let [with-digit (str/replace token #"\.([eEsSfFdDlL])" ".0$1")
        with-trailing (if (str/ends-with? with-digit ".")
                        (str with-digit "0")
                        with-digit)]
    (str/replace with-trailing #"[eEsSfFdDlL]" "e")))

(defn- parse-number [token index]
  (case (number-kind token)
    :ratio
    (let [[num den] (str/split token #"/")
          denominator (BigInteger. den)]
      (when (zero? denominator)
        (fail! index (str "The ratio " token " has a zero denominator.") false))
      (/ (bigint (BigInteger. num)) (bigint denominator)))
    :float (Double/parseDouble (normalize-float token))
    :integer (parse-integer token)))

(defn- unescaped-colon?
  [piece]
  (and (= \: (:ch piece)) (not (:escaped? piece))))

(defn- colon-run
  [pieces index]
  (loop [index index
         seen 0]
    (if (and (< index (count pieces)) (unescaped-colon? (pieces index)))
      (recur (inc index) (inc seen))
      [seen index])))

(defn- any-colon?
  [pieces]
  (some unescaped-colon? pieces))

(defn- take-name [pieces]
  (raw-name pieces))

(defn- qualified-symbol
  [package name index]
  (cond
    (str/blank? package)
    (fail! index "A package marker needs a package name." false)
    (str/blank? name)
    (fail! index "A package marker needs a symbol name." false)
    (#{"km" "KM"} package) (symbol nil name)
    :else (fail! index
                 (str "There is no package " package
                      ". Symbols are read into the km package.")
                 false)))

(defn- interpret-symbol
  [pieces index]
  (let [[leading end-of-leading] (colon-run pieces 0)]
    (cond
      (pos? leading)
      (cond
        (and (= leading 1) (not (any-colon? (subvec pieces end-of-leading))))
        (let [name (take-name (subvec pieces end-of-leading))]
          (when (str/blank? name)
            (fail! index "A keyword needs a name." false))
          (keyword name))
        :else (fail! index "This package marker is not a km symbol or a keyword." false))

      :else
      (loop [at 0]
        (if (>= at (count pieces))
          (symbol nil (take-name pieces))
          (let [[run after] (colon-run pieces at)]
            (if (zero? run)
              (recur (inc at))
              (cond
                (not (#{1 2} run))
                (fail! index "This package marker is not a km symbol or a keyword." false)
                (any-colon? (subvec pieces after))
                (fail! index "This package marker is not a km symbol or a keyword." false)
                :else (qualified-symbol (take-name (subvec pieces 0 at))
                                        (take-name (subvec pieces after))
                                        index)))))))))

(defn- dot-pieces?
  [pieces]
  (= pieces [{:ch \. :escaped? false}]))

(defn- dot-token?
  "True when index is a bare dot, not the start of .5 or a longer token."
  [text index]
  (and (< index (count text))
       (= \. (nth text index))
       (or (>= (inc index) (count text))
           (let [next-ch (nth text (inc index))]
             (or (whitespace next-ch) (terminating next-ch))))))

(declare read-form)

(defn- read-atom
  [text index]
  (let [[{:keys [pieces escaped?]} after] (read-token text index)]
    (cond
      (and (empty? pieces) (not escaped?))
      (fail! index "Expected a symbol." false)

      (and (not escaped?) (dot-pieces? pieces))
      (fail! index "A dot is only valid inside a list." false)

      (and (not escaped?) (number-kind (raw-name pieces)))
      [(parse-number (raw-name pieces) index) after]

      :else [(interpret-symbol pieces index) after])))

(defn- read-list
  [text index opts]
  (loop [index (skip text index)
         elems []]
    (cond
      (>= index (count text)) (eof! index "list")
      (= \) (nth text index)) [(term/build-list elems nil) (inc index)]
      (and (seq elems) (dot-token? text index))
      (let [index (skip text (inc index))]
        (cond
          (>= index (count text)) (eof! index "list")
          (= \) (nth text index))
          (fail! index "A dotted list needs a tail after the dot." false)
          (dot-token? text index)
          (fail! index "A dotted list has one tail." false)
          :else
          (let [[tail index] (read-form text index opts)
                index (skip text index)]
            (cond
              (>= index (count text)) (eof! index "list")
              (= \) (nth text index)) [(term/build-list elems tail) (inc index)]
              :else (fail! index "A dotted list has one tail." false)))))
      (dot-token? text index)
      (fail! index "A dotted list needs an element before the dot." false)
      :else
      (let [[elem index] (read-form text index opts)]
        (recur (skip text index) (conj elems elem))))))

(defn- read-hash-t
  [text index opts]
  (let [[form index] (read-form text index opts)]
    (if-not (term/km-symbol? form)
      (fail! index "#t expects a name." false)
      (let [key (str/upper-case (name form))]
        (if (contains? (:bindings opts) key)
          [(get (:bindings opts) key) index]
          (fail! index
                 (str "No value for #t" (name form)
                      ". #t looks up a name in the map the caller supplies. "
                      "That map is empty at the prompt and on HTTP.")
                 false))))))

(defn- read-hash-comma
  [text index opts]
  (let [[form index] (read-form text index opts)]
    [(term/km-list (symbol "unquote") form) index]))

(defn- read-function
  [text index opts]
  (let [[form index] (read-form text index opts)]
    [(term/km-list (symbol "function") form) index]))

(defn- read-refused-eval
  [text index opts label]
  (let [[form _] (read-form text index opts)]
    (fail! index
           (str label " evaluates Lisp while reading. Refusing "
                (print/km-format form) ".")
           false)))

(def ^:private char-names
  {"space" \space
   "newline" \newline
   "linefeed" \newline
   "tab" \tab
   "return" \return
   "page" \formfeed
   "rubout" \u007f
   "backspace" \backspace
   "null" \u0000})

(defn- constituent?
  [ch]
  (and (some? ch)
       (not (whitespace ch))
       (not (terminating ch))))

(defn- read-character
  [text index]
  (if (>= index (count text))
    (eof! index "character")
    (let [first-ch (nth text index)]
      (loop [index (inc index)
             chars [first-ch]]
        (if (and (< index (count text)) (constituent? (nth text index)))
          (recur (inc index) (conj chars (nth text index)))
          (let [name (apply str chars)]
            (cond
              (= (count chars) 1) [(first chars) index]
              (contains? char-names (str/lower-case name))
              [(get char-names (str/lower-case name)) index]
              :else (fail! index (str "Unknown character name " name ".") false))))))))

(defn- read-uninterned
  "Common Lisp #:name. The following token is a symbol name, even when it
  looks like a number. The port interns that name. A package marker in the
  token is an error, because an uninterned symbol has no package."
  [text index]
  (if (>= index (count text))
    (eof! index "symbol")
    (let [[{:keys [pieces escaped?]} after] (read-token text index)]
      (cond
        (and (empty? pieces) (not escaped?))
        (fail! index "Expected a symbol after #:." false)
        (any-colon? pieces)
        (fail! index "An uninterned symbol does not name a package." false)
        :else [(symbol nil (raw-name pieces)) after]))))

(defn- dispatch-char
  [text index ch opts]
  (case (Character/toLowerCase ^char ch)
    \t (read-hash-t text (inc index) opts)
    \: (read-uninterned text (inc index))
    \$ (read-form text (inc index) opts)
    \, (read-hash-comma text (inc index) opts)
    \' (read-function text (inc index) opts)
    \\ (read-character text (inc index))
    \. (read-refused-eval text (inc index) opts "#.")
    \= (fail! index "The #= reader labels an object while reading. The port refuses it." false)
    \# (fail! index "The ## reader recalls a #= label. The port refuses it." false)
    \+ (fail! index "Reader conditionals are not supported." false)
    \- (fail! index "Reader conditionals are not supported." false)
    \( (fail! index "The #( vector reader is not supported." false)
    \| (read-form text (skip-block text (inc index) 1) opts)
    (fail! index (str "No reader macro for #" ch ".") false)))

(defn- read-dispatch
  [text index opts]
  (cond
    (>= index (count text)) (eof! index "expression")
    (digit? (nth text index))
    (fail! index "A numeric reader argument is not supported." false)
    :else (dispatch-char text index (nth text index) opts)))

(defn- read-quoted
  [text index opts]
  (let [[form index] (read-form text index opts)]
    [(term/km-list (symbol "quote") form) index]))

(defn- read-form
  [text index opts]
  (let [index (skip text index)]
    (if (>= index (count text))
      (eof! index "expression")
      (let [ch (nth text index)]
        (cond
          (= ch \() (read-list text (inc index) opts)
          (= ch \)) (fail! index "Unexpected )." false)
          (= ch \") (read-string-literal text (inc index))
          (= ch \') (read-quoted text (inc index) opts)
          (= ch \`)
          (fail! index
                 "Backquote is different in each Lisp. Knowledge Machine uses #, to unquote, and this reader refuses backquote."
                 false)
          (= ch \,)
          (fail! index
                 "A comma is only valid inside a backquote. Knowledge Machine uses #, to unquote."
                 false)
          (= ch \#) (read-dispatch text (inc index) opts)
          :else (read-atom text index))))))

(defn- normalize-bindings
  [bindings]
  (into {}
        (map (fn [[key value]]
               [(str/upper-case (cond
                                  (string? key) key
                                  (keyword? key) (name key)
                                  (symbol? key) (name key)
                                  :else (str key)))
                value]))
        bindings))

(defn read-next
  "Read the next term from text, starting at index.

  :end is where the next read should start. :error \"empty\" means
  there is nothing left. :error \"read\" means the text at index is
  not a term. :incomplete is true when that text is only a prefix.
  bindings maps a #t name. Names match without regard to case."
  ([text index]
   (read-next text index {}))
  ([text index {:keys [bindings]}]
   (try
     (let [text (str (or text ""))
           opts {:bindings (normalize-bindings bindings)}
           start (skip text (long (or index 0)))]
       (if (>= start (count text))
         {:ok false :error "empty" :end start}
         (let [[form end] (read-form text start opts)]
           {:ok true :value form :end end})))
     (catch clojure.lang.ExceptionInfo thrown
       (if (:km/read (ex-data thrown))
         {:ok false
          :error "read"
          :end (or (:index (ex-data thrown)) index)
          :incomplete (boolean (:incomplete (ex-data thrown)))
          :message (.getMessage thrown)}
         (throw thrown))))))

(defn read-term
  "Read one Knowledge Machine term from text.

  Returns {:ok true :value term :end index} when the text holds one term.
  Returns {:ok false :error \"empty\"} when the text is only whitespace
  or comments. Returns {:ok false :error \"read\" :incomplete bool} when
  the text is not a term. :incomplete is true when the text is a prefix
  of a term.

  :bindings maps a #t name to a term. Names match without regard to case.
  The map is empty when the caller does not supply one."
  ([text]
   (read-term text {}))
  ([text {:keys [bindings]}]
   (try
     (let [text (str (or text ""))
           opts {:bindings (normalize-bindings bindings)}
           start (skip text 0)]
       (if (>= start (count text))
         {:ok false
          :error "empty"
          :message "Type a Knowledge Machine expression."}
         (let [[form end] (read-form text start opts)
               end (skip text end)]
           (if (< end (count text))
             {:ok false
              :error "read"
              :incomplete false
              :message (str "Trailing text after the expression, at character " (inc end) ".")}
             {:ok true :value form :end end}))))
     (catch clojure.lang.ExceptionInfo thrown
       (if (:km/read (ex-data thrown))
         {:ok false
          :error "read"
          :incomplete (boolean (:incomplete (ex-data thrown)))
          :message (.getMessage thrown)}
         (throw thrown))))))
