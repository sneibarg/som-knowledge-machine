(ns som.km.repl-test
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.repl :as repl]
            [som.km.term :as term]))

(deftest q-leaves-the-prompt
  (is (:leave (repl/respond "q")))
  (is (:leave (repl/respond "  q  ")))
  (is (:leave (repl/respond "q ; done")))
  (is (:leave (repl/respond "#|note|# q"))))

(deftest q-is-case-sensitive-and-a-list-is-not-the-command
  (let [upper (:text (repl/respond "Q"))
        listed (:text (repl/respond "(q)"))]
    (is (= false (:leave (repl/respond "Q"))))
    (is (= "(Q)" (first (str/split-lines upper))))
    (is (str/includes? upper "inferences"))
    (is (= false (:leave (repl/respond "(q)"))))
    (is (= "(q)" (first (str/split-lines listed))))
    (is (str/includes? listed "inferences"))))

(deftest a-refusal-is-printed-from-the-engine
  (let [reply (repl/respond "  (a Cat) ")]
    (is (= false (:leave reply)))
    (is (= "This form is not ported yet: (a Cat)." (:text reply)))
    (is (= (repl/reply-text (engine/evaluate "  (a Cat) ")) (:text reply)))))

(deftest an-unfinished-line-reports-the-read-error
  (let [reply (repl/respond "(every Car has")]
    (is (repl/continue? "(every Car has"))
    (is (not (repl/continue? "(a Cat)")))
    (is (re-find #"ended early" (:text reply)))
    (is (not (str/includes? (:text reply) "inferences")))))

(deftest an-answer-is-the-knowledge-machine-text
  (is (= "(a Cat)" (repl/reply-text {:ok true
                                       :value (term/km-list (symbol "a") (symbol "Cat"))})))
  (is (= "nil   ; (WARNING: Errors occurred during reasoning)"
         (repl/reply-text {:ok true :value nil :errors ["ERROR! missing"]})))
  (is (= "Type a Knowledge Machine expression."
         (repl/reply-text {:ok false :message "Type a Knowledge Machine expression."}))))

(deftest statistics-follow-the-answer-and-the-warning
  (is (= "(Fred)\n(2 inferences and 0 KB accesses in 0.0 sec)\n"
         (repl/reply-text {:ok true
                           :value (term/km-list (symbol "Fred"))
                           :statistics "(2 inferences and 0 KB accesses in 0.0 sec)\n"})))
  (is (= "nil   ; (WARNING: Errors occurred during reasoning)\n(0 inferences and 0 KB accesses in 0.0 sec)\n"
         (repl/reply-text {:ok true
                           :value nil
                           :errors ["ERROR! missing"]
                           :statistics "(0 inferences and 0 KB accesses in 0.0 sec)\n"}))))

(deftest a-prompt-session-keeps-an-assertion
  (let [session (repl/session)
        stored (:text (repl/respond "(Fred has (color (red)))" session))
        seen (:text (repl/respond "(the color of Fred)" session))
        apart (:text (repl/respond "(the color of Fred)"))]
    (is (= "(Fred)" (first (str/split-lines stored))))
    (is (str/includes? stored "inferences"))
    (is (= "(red)" (first (str/split-lines seen))))
    (is (str/includes? seen "inferences"))
    (is (= "nil" (first (str/split-lines apart))))
    (is (str/includes? apart "inferences"))))

(deftest banner-names-the-knowledge-machine-version
  (is (re-find #"v2\.5\.45" (repl/banner)))
  (is (re-find #"q leaves the prompt" (repl/banner))))
