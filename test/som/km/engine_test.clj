(ns som.km.engine-test
  (:require [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.frame :as frame]
            [som.km.read :as read]
            [som.km.term :as term]))

(defn- term [text]
  (:value (read/read-term text)))

(deftest status-names-the-build-and-both-fronts
  (let [status (engine/status)]
    (is (= "2.5.45" (:km-version status)))
    (is (= "som-knowledge-machine" (:name status)))
    (is (= ["repl" "http"] (:interfaces status)))
    (is (= "interpreter" (:evaluator status)))))

(deftest blank-text-is-refused
  (is (= {:ok false
          :error "empty"
          :message "Type a Knowledge Machine expression."}
         (engine/evaluate nil)))
  (is (= "empty" (:error (engine/evaluate "   "))))
  (is (not (contains? (engine/evaluate "   ") :input)))
  (is (not (contains? (engine/evaluate "   ") :kb))))

(deftest a-sum-is-the-answer-list
  (let [result (engine/evaluate "  (1 + 2)  ")]
    (is (:ok result))
    (is (= "(1 + 2)" (:input result)))
    (is (= (term/km-list 3) (:value result)))
    (is (not (contains? result :message)))
    (is (= [] (:errors result)))
    (is (= [] (:warnings result)))
    (is (frame/known-frame? (:kb result) (symbol "Thing")))
    (is (contains? result :query))))

(deftest a-form-that-is-not-ported-is-refused
  (let [cat (engine/evaluate "(a Cat)")
        lower (engine/evaluate "(a cat)")]
    (is (= false (:ok cat)))
    (is (= "not-ported" (:error cat)))
    (is (= "This form is not ported yet: (a Cat)." (:message cat)))
    (is (nil? (:value cat)))
    (is (not= (:message cat) (:message lower)))
    (is (frame/known-frame? (:kb cat) (symbol "Thing")))))

(deftest nil-t-and-f-are-answer-lists
  (is (nil? (:value (engine/evaluate "nil"))))
  (is (nil? (:value (engine/evaluate "()"))))
  (is (= (term "(t)") (:value (engine/evaluate "t"))))
  (is (= (term "(f)") (:value (engine/evaluate "f"))))
  (is (= (term "(T)") (:value (engine/evaluate "T"))))
  (is (= (term "(*Global)") (:value (engine/evaluate "|*Global|")))))

(deftest an-unfinished-expression-is-a-read-error
  (let [result (engine/evaluate "(every Car has")]
    (is (= false (:ok result)))
    (is (= "read" (:error result)))
    (is (:incomplete result))
    (is (re-find #"ended early" (:message result)))
    (is (not (contains? result :kb)))))

(deftest hash-t-needs-a-caller-supplied-value
  (let [missing (engine/evaluate "(the parts of #tcar-instance)")]
    (is (= "read" (:error missing)))
    (is (re-find #"#t" (:message missing)))
    (is (not (:incomplete missing))))
  (let [bound (engine/evaluate "#tcar-instance"
                               {:bindings {"car-instance" (symbol "_Car1")}})]
    (is (= (term "(_Car1)") (:value bound)))))

(deftest hash-dot-is-refused-by-name
  (let [result (engine/evaluate "#.(reset-kb)")]
    (is (= "read" (:error result)))
    (is (clojure.string/includes? (:message result) "#."))
    (is (re-find #"reset-kb" (:message result)))))

(deftest a-later-call-sees-an-assertion-only-on-the-same-value
  (let [stored (engine/evaluate "(Fred has (color (red)))")
        seen (engine/evaluate "(the color of Fred)"
                              {:kb (:kb stored) :query (:query stored)})
        fresh (engine/evaluate "(the color of Fred)")]
    (is (= (term "(Fred)") (:value stored)))
    (is (= (term "(red)") (:value seen)))
    (is (nil? (:value fresh)))))

(deftest fail-noisily-sticks-on-the-query
  (let [noisy (engine/evaluate "(fail-noisily)")
        quiet (engine/evaluate "(the color of Sue)")
        loud (engine/evaluate "(the color of Sue)"
                              {:kb (:kb noisy) :query (:query noisy)})]
    (is (= (term "(t)") (:value noisy)))
    (is (= [] (:errors quiet)))
    (is (some #(re-find #"No values found" %) (:errors loud)))))
