(ns som.km.print
  "Print one Knowledge Machine value the way km-format prints it.

  km-format in case.lisp sets the print case so that a symbol's stored
  characters are what appear, then prints with ~a after add-quotes.
  On the Lisp KM was written for, that setting means case-sensitive."
  (:require [som.km.strings :as strings]
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
  colon, because the symbol rule returns first."
  [value]
  (cond
    (nil? value) nil
    (term/cons? value)
    (term/cons-cell (add-quotes (term/car value))
                    (add-quotes (term/cdr value)))
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
