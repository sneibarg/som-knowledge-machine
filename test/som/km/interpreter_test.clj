(ns som.km.interpreter-test
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.frame :as frame]
            [som.km.read :as read]
            [som.km.term :as term]))

(defn- term [text]
  (:value (read/read-term text)))

(defn- answer [text]
  (engine/evaluate text))

(defn- value [text]
  (:value (answer text)))

(defn- on
  "Evaluate text on the result of a previous evaluation."
  [previous text]
  (engine/evaluate text {:kb (:kb previous) :query (:query previous)}))

(deftest literals-and-structures
  (is (nil? (value "nil")))
  (is (nil? (value "#$nil")))
  (is (= (term "(*)") (value "*")))
  (is (= (term "((quote Fred))") (value "'Fred")))
  (is (= (term "((quote (Fred 3)))") (value "(quote (Fred #,(1 + 2)))")))
  (is (some #(re-find #"can't unquote" %) (:errors (answer "#,Fred"))))
  (is (= (term "(1 2)") (value "(:set 1 (1 + 1))")))
  (is (= (term "((:seq))") (value "(:seq)")))
  (is (= (term "((:seq 1 2))") (value "(:seq 1 (1 + 1))")))
  (is (= (term "((:bag 1))") (value "(:bag 1)")))
  (is (= (term "((:pair 1 2))") (value "(:pair 1 2)")))
  (is (= (term "((:pair 1))") (value "(:pair 1)")))
  (is (some #(re-find #"exactly two elements" %) (:errors (answer "(:pair 1)"))))
  (is (= (term "((:triple Fred color red))") (value "(:triple Fred color red)")))
  (is (= (term "((:args 1))") (value "(:args 1)")))
  (is (= (term "((:function 1))") (value "(:function 1)"))))

(deftest arithmetic-keeps-exact-numbers
  (is (= (term "(3)") (value "(1 + 2)")))
  (is (= (term "(6)") (value "(1 + 2 + 3)")))
  (is (= (term "(-4)") (value "(1 - 2 - 3)")))
  (is (= (term "(1/2)") (value "(1 / 2)")))
  (is (= (term "(1)") (value "(0 / 0)")))
  (is (= (term "(999999)") (value "(1 / 0)")))
  (is (= (term "(0)") (value "(0 / 2)")))
  (is (= (term "(1)") (value "(0.0 / 0.0)")))
  (is (= (term "(999999)") (value "(1.0 / 0.0)")))
  (is (= (term "(0)") (value "(0.0 / 2)")))
  (is (= (term "(1024)") (value "(2 ^ 10)")))
  (is (= (term "(1267650600228229401496703205376)") (value "(2 ^ 100)")))
  (is (= (term "(1/4)") (value "(2 ^ -2)")))
  (is (= (term "(1)") (value "(0 ^ 0)")))
  (is (= 2 (get-in (answer "(1 + 2)") [:query :query-directed-inferences])))
  (is (= 1 (get-in (answer "(2 ^ 10)") [:query :query-directed-inferences]))))

(deftest tests-that-do-not-use-the-store
  (is (= (term "(t)") (value "(1 > 0)")))
  (is (nil? (value "(1 < 0)")))
  (is (= (term "(t)") (value "(1 = 1)")))
  (is (= (term "(t)") (value "(1 = 1.0)")))
  (is (nil? (value "(1 = 2)")))
  (is (= (term "(t)") (value "(1 /= 2)")))
  (is (nil? (value "(1 /= 1)")))
  (is (= (term "(t)") (value "(1 = 2 +/- 1)")))
  (is (= (term "(t)") (value "(100 = 90 +/- 10 %)")))
  (is (= (term "(2)") (value "(1 and 2)")))
  (let [skipped (answer "(nil and (a Cat))")]
    (is (nil? (:value skipped)))
    (is (not= "not-ported" (:error skipped))))
  (is (= (term "(2)") (value "(nil or 2)")))
  (is (= (term "(f)") (value "(f or 2)")))
  (is (= (term "(t)") (value "(not nil)")))
  (is (nil? (value "(not t)")))
  (is (= (term "(t)") (value "(numberp (1 + 2))")))
  (is (nil? (value "(numberp t)")))
  (let [joined (answer "((a == b) and (a Cat))")]
    (is (= "not-ported" (:error joined)))
    (is (re-find #"\(a == b\) and \(a Cat\)" (:message joined)))))

(deftest local-assert-and-lookup
  (let [stored (answer "(Fred has (color (red)))")
        read (on stored "(the color of Fred)")
        classes (on stored "(the subclasses of Sequence)")
        every (on stored "(every Cat has (color (black)))")
        cat (on every "(the color of Cat)")
        asserted (on stored "(assert (:triple Sue age 30))")
        age (on asserted "(the age of Sue)")
        gone (on asserted "(delete Sue)")
        missing (on gone "(the age of Sue)")]
    (is (= (term "(red)") (:value read)))
    (is (= (term "(Triple Pair)") (:value classes)))
    (is (= "not-ported" (:error every)))
    (is (nil? (:value cat)))
    (is (= (term "(Sue)") (:value asserted)))
    (is (= (term "(30)") (:value age)))
    (is (= (term "(t)") (:value gone)))
    (is (nil? (:value missing))))
  (is (= (term "(2)") (value "(the number of (:set 1 2))")))
  (is (= (term "(6)") (value "(the sum of (:bag 1 2 3))")))
  (is (= (term "(3)") (value "(the min of 3)"))))

(deftest a-looping-read-removes-the-slot
  (let [stored (answer "(Fred has (age ((the age of Fred))))")
        looped (on stored "(the age of Fred)")
        again (on looped "(the age of Fred)")]
    (is (nil? (:value looped)))
    (is (:looping? (:query looped)))
    (is (not (:message looped)))
    (is (nil? (:value (frame/get-vals (:kb looped) (symbol "Fred") (symbol "age")))))
    (is (not (:looping? (:query again))))))

(deftest a-stored-constraint-survives-a-read
  (let [stored (answer "(Pat has (color ((must-be-a Color))))")
        read (on stored "(the color of Pat)")
        again (frame/get-vals (:kb read) (symbol "Pat") (symbol "color"))]
    (is (nil? (:value read)))
    (is (frame/are-some? (:kb read) :constraints))
    (is (= (term "((must-be-a Color))") (:value again)))))

(deftest constraints-are-recorded-and-not-enforced
  (let [must (answer "(must-be-a Cat)")
        sometimes (on must "(sometimes (1 + 2))")
        check (on sometimes "(sanity-check (Fred has (color (red))))")]
    (is (nil? (:value must)))
    (is (frame/are-some? (:kb must) :constraints))
    (is (nil? (:value sometimes)))
    (is (= (term "(t)") (:value check)))
    (is (nil? (:value (frame/get-vals (:kb check) (symbol "Fred") (symbol "color"))))))
  (is (= "not-ported" (:error (answer "(retain-expr (1 + 2))"))))
  (is (= "not-ported" (:error (answer "(an instance of Cat)"))))
  (let [syntax (answer "(an Cat)")]
    (is (:ok syntax))
    (is (nil? (:value syntax)))
    (is (some #(re-find #"Syntax error" %) (:errors syntax)))
    (is (not (:error syntax)))))

(deftest commands-from-the-goal-stack-step
  (let [reset (answer "(reset-kb)")
        goals (answer "(show-goal-stack)")
        stored (answer "(Fred has (color (red)))")
        stack (on stored "(show-obj-stack)")
        cleared (on stack "(new-context)")
        empty (on cleared "(show-obj-stack)")
        noisy (answer "(fail-noisily)")
        next (on noisy "(the color of Nobody)")]
    (is (= (term "(t)") (:value reset)))
    (is (zero? (get-in reset [:query :query-directed-inferences])))
    (is (nil? (:value goals)))
    (is (str/includes? (:text goals) "CURRENT GOAL STACK IS AS FOLLOWS:"))
    (is (not (str/includes? (:text goals) "Fred")))
    (is (str/includes? (:text stack) "Fred"))
    (is (= (term "(t)") (:value stack)))
    (is (= (term "(t)") (:value cleared)))
    (is (= 1 (get-in cleared [:query :query-directed-inferences])))
    (is (not (str/includes? (:text empty) "Fred")))
    (is (some #(re-find #"No values found" %) (:errors next))))
  (is (= "not-ported" (:error (answer "(eval (1 + 2))"))))
  (is (re-find #"setq is not evaluated" (:message (answer "(setq x 1)"))))
  (is (re-find #"function is not evaluated" (:message (answer "(function foo)"))))
  (is (re-find #"Tracing is not ported yet" (:message (answer "(trace)"))))
  (is (re-find #"Embedded Lisp is refused" (:message (answer "(Trace)"))))
  (is (re-find #"not ported yet" (:message (answer "(load-kb \"x\")"))))
  (is (re-find #"fastsave stays unported" (:message (answer "(fastsave-kb \"x\")")))))

(deftest a-depth-limit-stops-the-inner-sum
  (let [base (engine/session)
        result (engine/evaluate "(1 + 2 + 3)"
                                {:kb (:kb base)
                                 :query (assoc (:query base) :km-depth-limit 0)})]
    (is (nil? (:value result)))
    (is (:looping? (:query result)))))

(deftest several-values-keep-the-first
  (let [result (answer "(numberp (:set 1 2))")]
    (is (= (term "(t)") (:value result)))
    (is (some #(re-find #"multiple values" %) (:errors result)))))
