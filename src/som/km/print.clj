(ns som.km.print
  "Print one Knowledge Machine value the way km-format prints it.

  km-format in case.lisp sets the print case so that a symbol's stored
  characters are what appear, then prints with ~a after add-quotes.
  On the Lisp KM was written for, that setting means case-sensitive."
  (:require [clojure.string :as str]
            [som.km.strings :as strings]
            [som.km.term :as term]))

(def ^:private special-chars
  "Characters that make add-quotes wrap a symbol in vertical bars."
  #{\( \) \space \, \; \: \' \"})

(def ^:private ascii-digits
  #{\0 \1 \2 \3 \4 \5 \6 \7 \8 \9})

(defn- all-ascii-digits?
  "True when every character is an ASCII digit. The empty name is included,
  matching set-difference against the digit set in add-quotes."
  [chars]
  (every? ascii-digits chars))

(defn- prin1-string
  "A string in Common Lisp readable form. Quotes and backslashes are
  escaped. Other characters, including a newline, are written as themselves.
  Clojure's pr-str would turn a newline into a backslash and an n."
  [text]
  (let [out (StringBuilder. "\"")]
    (doseq [ch text]
      (cond
        (= ch \") (.append out "\\\"")
        (= ch \\) (.append out "\\\\")
        :else (.append out ch)))
    (.append out \")
    (str out)))

(defn- bar-form
  "The barred spelling of a symbol name, or nil when the name can stand alone.

  A name gains bars when it contains one of the special characters, or when
  every character is an ASCII digit. An internal vertical bar is written
  with a backslash. A name that contains a bar and nothing else special is
  returned without surrounding bars, which is what add-quotes returns."
  [name]
  (let [chars (strings/explode name)
        pipe? (some #(= \| %) chars)
        escaped (if pipe? (strings/substitute-string "|" "\\|" name) name)]
    (cond
      (or (some special-chars chars)
          (all-ascii-digits? chars))
      (str "|" escaped "|")
      pipe? escaped
      :else nil)))

(defn add-quotes
  "Prepare one value the way add-quotes does before ~a.

  Strings gain quotes. A symbol gains vertical bars when its name needs
  them. A keyword is a symbol in Lisp, so the bar rule runs before the
  colon is added. A keyword whose name needs bars is printed without the
  colon, because the symbol rule returns first. A list is walked along
  its spine. The names (load-lib) returns are one long list, and a
  recursive walk of that spine overflows the stack."
  [value]
  (cond
    (nil? value) nil
    (term/cons? value)
    (loop [cell value
           acc []]
      (let [acc (conj acc (add-quotes (term/car cell)))
            tail (term/cdr cell)]
        (cond
          (nil? tail) (term/build-list acc nil)
          (term/cons? tail) (recur tail acc)
          :else (term/build-list acc (add-quotes tail)))))
    (string? value) (prin1-string value)
    (term/lisp-symbol? value)
    (let [bars (bar-form (term/symbol-name value))]
      (cond
        (some? bars) bars
        (keyword? value) (str ":" (name value))
        :else value))
    :else value))

(defn- print-number
  [value]
  (cond
    (ratio? value) (str (numerator value) "/" (denominator value))
    (integer? value) (str (bigint value))
    :else (str value)))

(defn- render
  [value]
  (cond
    (nil? value) "nil"
    (string? value) value
    (term/cons? value)
    (let [out (StringBuilder. "(")]
      (loop [cell value
             first? true]
        (when-not first?
          (.append out \space))
        (.append out (render (term/car cell)))
        (let [tail (term/cdr cell)]
          (cond
            (nil? tail) (.append out ")")
            (term/cons? tail) (recur tail false)
            :else (do (.append out " . ")
                      (.append out (render tail))
                      (.append out ")")))))
      (str out))
    (term/km-symbol? value) (name value)
    (keyword? value) (str ":" (name value))
    (number? value) (print-number value)
    (char? value) (str value)
    :else (str value)))

(defn km-format
  "The text (km-format stream \"~a\" value) would write.

  The empty list is written as nil. A symbol's stored case is kept.
  Display comments such as #|\"a Car\"|# are not added here. Those are
  written later, from the knowledge base, by write-km-vals."
  [value]
  (render (add-quotes value)))

(defn- walk-term
  "Print value with one element printer. A list uses that printer for each element."
  [value print-one]
  (cond
    (nil? value) "nil"
    (string? value) (print-one value)
    (term/cons? value)
    (let [out (StringBuilder. "(")]
      (loop [cell value
             first? true]
        (when-not first?
          (.append out \space))
        (.append out (walk-term (term/car cell) print-one))
        (let [tail (term/cdr cell)]
          (cond
            (nil? tail) (.append out ")")
            (term/cons? tail) (recur tail false)
            :else (do (.append out " . ")
                      (.append out (walk-term tail print-one))
                      (.append out ")")))))
      (str out))
    (term/km-symbol? value) (print-one value)
    (keyword? value) (print-one value)
    (number? value) (print-number value)
    (char? value) (str value)
    :else (print-one value)))

(defn- princ-one
  "princ of one atom. A string is its characters. A symbol is its name."
  [value]
  (cond
    (string? value) value
    (term/km-symbol? value) (name value)
    (keyword? value) (str ":" (name value))
    (nil? value) "nil"
    :else (str value)))

(defn- prin1-one
  "prin1 of one atom. A string gains quotes. A symbol gains bars when it needs them."
  [value]
  (cond
    (string? value) (prin1-string value)
    (term/lisp-symbol? value)
    (let [bars (bar-form (term/symbol-name value))]
      (cond
        (some? bars) bars
        (keyword? value) (str ":" (name value))
        :else (term/symbol-name value)))
    (nil? value) "nil"
    :else (str value)))

(defn- column-after
  [column text]
  (let [break (str/last-index-of text "\n")]
    (if (nil? break)
      (+ column (count text))
      (- (count text) (inc break)))))

(defn- take-arg
  [args]
  (if (empty? args)
    [nil args :missing]
    [(first args) (rest args) nil]))

(defn- pad-column
  "Spaces that move column to n. A column already past n gains none.

  This is ~n,1T. The default n is 1."
  [column n]
  (let [n (or n 1)
        count (max 0 (- n column))]
    (apply str (repeat count \space))))

(defn format-control
  "The text Common Lisp format would write for control and args.

  ~a and ~A princ. ~s and ~S prin1. ~% is a newline. ~& starts a line.
  ~~ is a tilde. ~d and ~D print a number. ~nT pads to column n.
  Extra arguments are left unused. A missing argument, or a directive
  this printer does not know, is :error."
  [control args]
  (when-not (string? control)
    (throw (ex-info "A format control is a string." {:control control})))
  (let [args (vec args)
        length (count control)]
    (loop [index 0
           args args
           column 0
           out (StringBuilder.)]
      (if (>= index length)
        {:text (str out)}
        (let [ch (nth control index)]
          (if (not= ch \~)
            (let [text (str ch)]
              (recur (inc index) args (column-after column text) (.append out text)))
            (let [body (loop [at (inc index)
                              digits ""]
                         (cond
                           (>= at length) nil
                           (Character/isDigit (nth control at))
                           (recur (inc at) (str digits (nth control at)))
                           :else {:at at :digits digits :char (nth control at)}))]
              (if (nil? body)
                {:error "A format directive is missing its character."}
                (let [directive (:char body)
                      prefix (when (seq (:digits body)) (Integer/parseInt (:digits body)))
                      next (inc (:at body))
                      letter (Character/toLowerCase directive)]
                  (cond
                    (= directive \~)
                    (recur next args (column-after column "~") (.append out \~))

                    (= directive \%)
                    (recur next args 0 (.append out \newline))

                    (= directive \&)
                    (if (zero? column)
                      (recur next args column out)
                      (recur next args 0 (.append out \newline)))

                    (contains? #{\a \s \d} letter)
                    (let [[arg left missing] (take-arg args)]
                      (if missing
                        {:error "Not enough arguments for the format control."}
                        (let [text (case letter
                                     \a (walk-term arg princ-one)
                                     \s (walk-term arg prin1-one)
                                     \d (cond
                                          (number? arg) (print-number arg)
                                          :else (walk-term arg princ-one)))]
                          (recur next left (column-after column text) (.append out text)))))

                    (= letter \t)
                    (let [text (pad-column column prefix)]
                      (recur next args (column-after column text) (.append out text)))

                    :else {:error (str "Unknown format directive ~" directive)}))))))))))

(defn km-format-control
  "format-control after add-quotes, which is what (km-format nil control args) returns.

  A string argument is already quoted, so ~a prints the quotes."
  [control args]
  (format-control control (map add-quotes args)))
