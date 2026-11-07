(ns som.km.read-test
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.print :as print]
            [som.km.read :as read]
            [som.km.term :as term]))

(defn- term [text]
  (:value (read/read-term text)))

(defn- printed [text]
  (print/km-format (term text)))

(deftest case-and-strings-match-the-km-format-example
  (is (= "(The BIG big \"car\" 2)"
         (printed "(The BIG big \"car\" 2)")))
  (is (= (term/km-list (symbol "The") (symbol "BIG") (symbol "big") "car" 2)
         (term "(The BIG big \"car\" 2)"))))

(deftest the-empty-list-is-nil-and-the-symbol-nil-is-not
  (is (nil? (term "()")))
  (is (nil? (term "( )")))
  (is (= (symbol "nil") (term "nil")))
  (is (not= (term "nil") (term "()")))
  (is (= "nil" (print/km-format nil)))
  (is (= "nil" (print/km-format (symbol "nil")))))

(deftest t-and-f-are-symbols
  (is (= (symbol "t") (term "t")))
  (is (= (symbol "f") (term "f")))
  (is (= (symbol "T") (term "T")))
  (is (not= (term "t") (term "T")))
  (is (term/km-symbol? (term "true")))
  (is (term/km-symbol? (term "false"))))

(deftest vertical-bars-keep-the-stored-name
  (is (= (symbol "the Dog") (term "|the Dog|")))
  (is (= "|the Dog|" (print/km-format (symbol "the Dog"))))
  (is (= (symbol "1943") (term "|1943|")))
  (is (= "|1943|" (printed "|1943|")))
  (is (= 1943 (term "1943")))
  (is (= (symbol "a|b") (term "|a\\|b|")))
  (is (= "a\\|b" (print/km-format (symbol "a|b"))))
  (is (= term/global-situation (term "|*Global|")))
  (is (= term/global-situation (term "*Global")))
  (is (= "*Global" (printed "|*Global|"))))

(deftest a-dotted-pair-keeps-its-tail
  (is (not (term/proper? (term "(baz . bar)"))))
  (is (= "(baz . bar)" (printed "(baz . bar)")))
  (is (= (term "(a)") (term "(a . ())")))
  (is (not (term/proper? (term "(a . nil)"))))
  (is (= "(a . nil)" (printed "(a . nil)"))))

(deftest a-dot-before-a-list-continues-that-list
  (is (= (term "(a b c)") (term "(a b . (c))")))
  (let [spliced (term "'(:set (a Car) . #,(a Car))")
        nested (term "'(:set (a Car) #,(a Car))")
        body #(term/car (term/cdr %))]
    (is (term/proper? (body spliced)))
    (is (= (symbol "unquote") (term/car (term/cdr (term/cdr (body spliced))))))
    (is (term/cons? (term/car (term/cdr (term/cdr (body nested))))))
    (is (= "(quote (:set (a Car) unquote (a Car)))" (print/km-format spliced)))
    (is (= "(quote (:set (a Car) (unquote (a Car))))" (print/km-format nested)))))

(deftest quote-function-and-unquote-use-lowercase-names
  (is (= (term/km-list (symbol "quote") (symbol "Fred")) (term "'Fred")))
  (is (= "(quote Fred)" (printed "'Fred")))
  (is (= (term/km-list (symbol "function") (symbol "dog")) (term "#'dog")))
  (is (= "(:seq _Car2 |the Dog| (baz . bar) (unquote (the (function dog))))"
         (printed "(:seq _Car2 |the Dog| (baz . bar) #,(the #'dog))"))))

(deftest comments-are-discarded-including-display-comments
  (is (= (term "(a Cat)") (term "(a #|comment|# Cat)")))
  (is (= (term "(a b)") (term "(a #| outer #| inner |# still |# b)")))
  (is (= (term "(a Cat)") (term "(a ; remark\n Cat)")))
  (is (= (term "(_Car2)") (term "(_Car2 #|\"a Car\"|#)")))
  (is (= "\"#|hi|#\"" (printed "\"#|hi|#\""))))

(deftest numbers-stay-exact-where-lisp-would
  (is (= 4 (term "4")))
  (is (= 3 (term "+3")))
  (is (= "3" (printed "+3")))
  (is (= 1/2 (term "1/2")))
  (is (= "1/2" (printed "1/2")))
  (is (= -4 (term "-4")))
  (is (== 1.0 (term "1.")))
  (is (= "1.0" (printed "1.")))
  (is (== 1.5 (term "1.5")))
  (is (== 100.0 (term "1e2")))
  (is (= "100.0" (printed "1e2")))
  (is (term/km-symbol? (term "1+")))
  (let [wide "999999999999999999999"]
    (is (= (bigint wide) (term wide)))
    (is (= wide (printed wide)))))

(deftest strings-escape-quotes-and-keep-newlines
  (is (= "say \"hi\"" (term "\"say \\\"hi\\\"\"")))
  (is (= "\"say \\\"hi\\\"\"" (printed "\"say \\\"hi\\\"\"")))
  (is (= "anb" (term "\"a\\nb\"")))
  (is (= "(\"a\nb\")" (print/km-format (term/km-list "a\nb"))))
  (is (not (str/includes? (print/km-format (term/km-list "a\nb")) "\\n"))))

(deftest keywords-keep-their-case
  (is (= :seq (term ":seq")))
  (is (= :Seq (term ":Seq")))
  (is (not= (term ":seq") (term ":Seq")))
  (is (= ":seq" (print/km-format :seq)))
  (is (= "|1943|" (print/km-format (keyword "1943")))))

(deftest hash-dollar-reads-one-form
  (is (= (term "(the Car)") (term "#$(the Car)")))
  (is (= (term "(the Car)") (term "(#$the Car)"))))

(deftest hash-t-looks-up-a-name-without-regard-to-case
  (is (re-find #"No value for #t" (:message (read/read-term "#tcar-instance"))))
  (is (= (symbol "_Car1")
         (:value (read/read-term "#tcar-instance"
                                 {:bindings {"CAR-INSTANCE" (symbol "_Car1")}}))))
  (is (= (term "(the parts of _Car1)")
         (:value (read/read-term "(the parts of #tCar-Instance)"
                                 {:bindings {"car-instance" (symbol "_Car1")}})))))

(deftest characters-use-the-lisp-names
  (is (= \A (term "#\\A")))
  (is (= \space (term "#\\Space")))
  (is (= \newline (term "#\\newline")))
  (is (= "A" (print/km-format \A))))

(deftest read-errors-name-the-problem
  (is (:incomplete (read/read-term "(a")))
  (is (:incomplete (read/read-term "\"unterminated")))
  (is (not (:incomplete (read/read-term ")"))))
  (is (re-find #"Unexpected" (:message (read/read-term ")"))))
  (is (re-find #"Trailing text" (:message (read/read-term "(a) (b)"))))
  (is (re-find #"only valid inside a list" (:message (read/read-term "."))))
  (is (re-find #"before the dot" (:message (read/read-term "(. a)"))))
  (is (re-find #"tail after the dot" (:message (read/read-term "(a .)"))))
  (is (re-find #"one tail" (:message (read/read-term "(a . b c)"))))
  (is (re-find #"Backquote" (:message (read/read-term "`(a)"))))
  (is (re-find #"comma" (:message (read/read-term ",a"))))
  (is (re-find #"#\." (:message (read/read-term "#.foo"))))
  (is (re-find #"foo" (:message (read/read-term "#.foo"))))
  (is (re-find #"#=" (:message (read/read-term "#=foo"))))
  (is (re-find #"package" (:message (read/read-term "user::Car"))))
  (is (= (symbol "Car") (term "km::Car")))
  (is (= "empty" (:error (read/read-term "   ; only a comment"))))
  (is (= (symbol "Car") (term "#:Car")))
  (is (= (symbol "the Dog") (term "#:|the Dog|")))
  (is (= (symbol "1943") (term "#:1943")))
  (is (re-find #"package" (:message (read/read-term "#:km::Car")))))

(deftest a-stable-term-round-trips
  (doseq [text ["(the age of Fred)"
                "(The BIG big \"car\" 2)"
                "(:seq _Car2 |the Dog| (baz . bar))"
                "|1943|"
                "\"say \\\"hi\\\"\""
                "1/2"
                "-4"
                ":seq"
                "nil"
                "t"
                "f"
                "T"
                "*Global"]]
    (is (= (term text) (term (printed text))) text)))
