(ns som.km.repl-test
  (:require [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.repl :as repl]
            [som.km.term :as term]))

(deftest q-leaves-the-prompt
  (is (:leave (repl/respond "q")))
  (is (:leave (repl/respond "  q  ")))
  (is (:leave (repl/respond "q ; done")))
  (is (:leave (repl/respond "#|note|# q"))))

(deftest q-is-case-sensitive-and-a-list-is-not-the-command
  (is (= false (:leave (repl/respond "Q"))))
  (is (= "(Q)" (:text (repl/respond "Q"))))
  (is (= false (:leave (repl/respond "(q)"))))
  (is (= "(q)" (:text (repl/respond "(q)")))))

(deftest a-refusal-is-printed-from-the-engine
  (let [reply (repl/respond "  (a Cat) ")]
    (is (= false (:leave reply)))
    (is (= "This form is not ported yet: (a Cat)." (:text reply)))
    (is (= (repl/reply-text (engine/evaluate "  (a Cat) ")) (:text reply)))))

(deftest an-unfinished-line-reports-the-read-error
  (is (repl/continue? "(every Car has"))
  (is (not (repl/continue? "(a Cat)")))
  (is (re-find #"ended early" (:text (repl/respond "(every Car has")))))

(deftest an-answer-is-the-knowledge-machine-text
  (is (= "(a Cat)" (repl/reply-text {:ok true
                                       :value (term/km-list (symbol "a") (symbol "Cat"))})))
  (is (= "nil   ; (WARNING: Errors occurred during reasoning)"
         (repl/reply-text {:ok true :value nil :errors ["ERROR! missing"]})))
  (is (= "Type a Knowledge Machine expression."
         (repl/reply-text {:ok false :message "Type a Knowledge Machine expression."}))))

(deftest a-prompt-session-keeps-an-assertion
  (let [session (repl/session)]
    (is (= "(Fred)" (:text (repl/respond "(Fred has (color (red)))" session))))
    (is (= "(red)" (:text (repl/respond "(the color of Fred)" session))))
    (is (= "nil" (:text (repl/respond "(the color of Fred)"))))))

(deftest banner-names-the-knowledge-machine-version
  (is (re-find #"v2\.5\.45" (repl/banner)))
  (is (re-find #"q leaves the prompt" (repl/banner))))
