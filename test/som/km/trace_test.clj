(ns som.km.trace-test
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.license :as license]
            [som.km.read :as read]
            [som.km.stats :as stats]
            [som.km.term :as term]))

(defn- term-of [text]
  (:value (read/read-term text)))

(defn- answer [text]
  (engine/evaluate text))

(defn- on
  [previous text]
  (engine/evaluate text {:kb (:kb previous) :query (:query previous)}))

(defn- name-of [result]
  (term/symbol-name (term/car (:value result))))

(defn- slash [path]
  (str/replace path "\\" "/"))

(defn- load-temp
  [body]
  (let [path (.getAbsolutePath (java.io.File/createTempFile "km-step15-" ".km"))]
    (try
      (spit path body :encoding "UTF-8")
      (answer (str "(load-kb \"" (slash path) "\")"))
      (finally
        (io/delete-file path true)))))

(deftest trace-and-untrace-answer-t-and-say-when-they-are-already-set
  (let [started (answer "(trace)")
        again (on started "(trace)")
        off (on again "(untrace)")
        still (on off "(untrace)")]
    (is (= (term-of "(t)") (:value started)))
    (is (str/includes? (:text started) "(Tracing of KM switched on)"))
    (is (not (str/includes? (:text started) "->")))
    (is (= (term-of "(t)") (:value again)))
    (is (str/includes? (:text again) "(Tracing of KM is already switched on)"))
    (is (= (term-of "(t)") (:value off)))
    (is (str/includes? (:text off) "(Tracing of KM switched off)"))
    (is (= (term-of "(t)") (:value still)))
    (is (str/includes? (:text still) "(Tracing of KM is already switched off)"))))

(deftest a-slot-read-is-traced-and-the-trace-command-is-not-a-goal
  (let [stored (answer "(Fred has (color (red)))")
        traced (on stored "(trace)")
        seen (on traced "(the color of Fred)")]
    (is (= (term-of "(red)") (:value seen)))
    (is (str/includes? (:text seen) "-> (the color of Fred)"))
    (is (str/includes? (:text seen) "<-"))
    (is (not (str/includes? (:text traced) "-> (trace)")))))

(deftest a-name-lookup-suspends-trace-and-the-next-read-traces
  (let [named (answer "(Fred has (name (\"FRED\")))")
        traced (on named "(trace)")
        phrase (on traced "(make-phrase Fred)")
        again (on phrase "(the name of Fred)")]
    (is (str/includes? (:text phrase) "make-phrase"))
    (is (not (str/includes? (str (:text phrase)) "(the name of Fred)")))
    (is (str/includes? (:text again) "(the name of Fred)"))))

(deftest a-spypoint-turns-tracing-on-and-unspy-clears-the-points
  (let [watched (answer "(spy (the color of Fred))")
        stored (on watched "(Fred has (color (red)))")
        first (on stored "(the color of Fred)")
        second (on first "(the color of Fred)")
        cleared (on second "(unspy)")
        later (on cleared "(the color of Fred)")]
    (is (str/includes? (:text watched) "expressions/patterns"))
    (is (str/includes? (:text watched) "(the color of Fred)"))
    (is (str/includes? (:text first) "(Spypoint reached!)"))
    (is (str/includes? (:text first) "(Tracing of KM switched on)"))
    (is (str/includes? (:text first) "(the color of Fred)"))
    (is (str/includes? (:text second) "(Tracing of KM is already switched on)"))
    (is (str/includes? (:text cleared) "(All spypoints removed)"))
    (is (not (str/includes? (str (:text later)) "Spypoint reached!")))))

(deftest profile-reports-the-sum-without-a-fixed-time
  (let [ran (answer "(profile (1 + 2))")]
    (is (= (term-of "(3)") (:value ran)))
    (is (str/includes? (:text ran) "(1 + 2)"))
    (is (str/includes? (:text ran) "CPU-TIME"))
    (is (str/includes? (:text ran) "# CALLS"))))

(deftest trace-to-file-appends-the-same-line-the-answer-records
  (let [file (java.io.File/createTempFile "km-step15-" ".km")
        path (slash (.getAbsolutePath file))]
    (try
      (let [opened (answer (str "(t2f-on \"" path "\")"))
            traced (on opened "(trace)")
            stored (on traced "(Fred has (color (red)))")
            seen (on stored "(the color of Fred)")]
        (is (= (term-of "(t)") (:value opened)))
        (is (str/includes? (:text opened) "(Trace-to-file switched on)"))
        (is (str/includes? (:text seen) "(the color of Fred)"))
        (is (str/includes? (slurp file :encoding "UTF-8") "(the color of Fred)")))
      (finally
        (io/delete-file file true)))))

(deftest a-file-setq-of-trace-traces-the-load-and-leaves-interactive-trace-off
  (let [loaded (load-temp "(SETQ *TRACE* t)\n(Fred has (color (red)))\n(the color of Fred)\n")]
    (is (true? (get-in loaded [:kb :runtime :trace?])))
    (is (false? (get-in loaded [:kb :runtime :interactive-trace?])))
    (is (str/includes? (:text loaded) "(the color of Fred)"))))

(deftest disabled-reset-keeps-the-inference-count-across-two-sums
  (let [loaded (load-temp "(SETQ *RESET-STATISTICS-ENABLED* nil)\n")
        first (on loaded "(1 + 2)")
        second (on first "(1 + 2)")]
    (is (= 2 (get-in first [:query :query-directed-inferences])))
    (is (= 4 (get-in second [:query :query-directed-inferences])))))

(deftest print-statistics-prints-the-short-report
  (let [loaded (let [path (.getAbsolutePath (java.io.File/createTempFile "km-step15-" ".km"))]
                 (try
                   (spit path "\n" :encoding "UTF-8")
                   (answer (str "(load-kb \"" (slash path) "\" :print-statistics t)"))
                   (finally
                     (io/delete-file path true))))]
    (is (str/includes? (:text loaded) "inferences"))
    (is (not (str/includes? (:text loaded) "not ported")))))

(deftest a-report-frequency-prints-a-spot-line-on-the-next-query
  (let [loaded (load-temp "(SETQ *INFERENCE-REPORT-FREQUENCY* 1)\n(Fred has (color (red)))\n")
        seen (on loaded "(the color of Fred)")]
    (is (= (term-of "(red)") (:value seen)))
    (is (str/includes? (:text seen) "logical inferences done"))))

(deftest license-and-licence-print-the-repository-text-and-answer-nil
  (let [file (slurp "LICENSE" :encoding "UTF-8")
        american (answer "(license)")
        british (answer "(licence)")]
    (is (= file (license/text)))
    (is (= file license/fallback-text))
    (is (= file (:text american)))
    (is (nil? (:value american)))
    (is (= file (:text british)))
    (is (nil? (:value british)))))

(deftest the-long-report-names-skolem-instances-and-the-maximum-depth
  (let [text (stats/report-long {} {:skolems 2
                                    :unifications 3
                                    :max-depth 4
                                    :query-directed-inferences 5
                                    :classification-inferences 0
                                    :classifications-attempted 0
                                    :classifications-succeeded 0})]
    (is (str/includes? text "Skolem"))
    (is (str/includes? text "maximum depth"))
    (is (str/includes? text "2 Skolem instances created"))))

(deftest a-zero-interval-report-has-one-closing-parenthesis
  (is (= "(0 inferences and 0 KB accesses in 0.0 sec)\n" (stats/report {} {}))))

(deftest an-extra-trace-argument-stays-an-embedded-lisp-refusal
  (let [extra (answer "(trace extra)")
        mixed (answer "(Trace)")]
    (is (= "not-ported" (:error extra)))
    (is (str/includes? (:message extra) "Embedded Lisp is refused"))
    (is (= "not-ported" (:error mixed)))))

(defn- plan [texts]
  (reduce on (answer (first texts)) (rest texts)))

(def ^:private structural
  ["(next-event has (fluent-status (*Non-Fluent)))"
   "(next-event-test has (fluent-status (*Non-Fluent)))"
   "(first-subevent has (fluent-status (*Non-Fluent)))"])

(deftest a-plan-walks-two-events-and-a-comment-can-be-silenced
  (let [ready (plan (into structural
                          ["(_Start has (add-list ((:triple Fred color green))))"
                           "(_Start has (next-event (_Next)))"
                           "(_Next has (add-list ((:triple Fred color blue))))"
                           "(_Plan has (first-subevent (_Start)))"]))
        sit (on ready "(new-situation)")
        walked (on sit "(do-plan _Plan)")
        color (on walked "(the color of Fred)")
        quiet (on ready "(nocomments)")
        quiet-sit (on quiet "(new-situation)")
        silent (on quiet-sit "(do-plan _Plan)")]
    (is (str/includes? (:text walked) "(COMMENT: Executing event"))
    (is (= (term-of "(blue)") (:value color)))
    (is (str/starts-with? (name-of walked) "_Situation"))
    (is (= (term-of "(t)") (:value quiet)))
    (is (str/includes? (:text quiet) "(Display of comments is switched off)"))
    (is (not (str/includes? (str (:text silent)) "COMMENT:")))))

(deftest a-next-event-test-selects-the-matching-event
  (let [ready (plan (into structural
                          ["(_Start has (add-list ((:triple Fred color green))))"
                           "(_Start has (next-event-test ((quote (the color of Fred)))))"
                           "(_Start has (next-event ((:args green _OnGreen) (:args red _OnRed))))"
                           "(_OnGreen has (add-list ((:triple Fred size large))))"
                           "(_OnRed has (add-list ((:triple Fred size small))))"
                           "(_Choice has (first-subevent (_Start)))"]))
        sit (on ready "(new-situation)")
        walked (on sit "(do-plan _Choice)")
        size (on walked "(the size of Fred)")]
    (is (= (term-of "(large)") (:value size)))
    (is (empty? (:errors walked)))))

(deftest a-plan-with-no-first-subevent-records-the-error
  (let [missing (answer "(do-plan Fred)")]
    (is (nil? (:value missing)))
    (is (some #(str/includes? % "no first-subevent") (:errors missing)))))

(deftest multiple-next-events-use-the-swapped-sentence-and-still-finish
  (let [ready (plan (into structural
                          ["(_Start has (add-list ((:triple Fred color green))))"
                           "(_Start has (next-event (_Next _Later)))"
                           "(_Plan has (first-subevent (_Start)))"]))
        sit (on ready "(new-situation)")
        walked (on sit "(do-plan _Plan)")
        here (on walked "(curr-situation)")]
    (is (some #(str/includes? % "Multiple next-events _Start specified for event (_Next _Later)!")
              (:errors walked)))
    (is (str/includes? (:text walked) "Finishing simulation"))
    (is (= (:value walked) (:value here)))))

(deftest unification-and-access-counters-follow-the-commit-and-the-read
  (let [same (answer "(1 & 1)")
        left (answer "(_Cat1 has (instance-of (Cat)))")
        both (on left "(_Cat2 has (instance-of (Cat)))")
        unified (on both "(_Cat1 & _Cat2)")
        bare (answer "(1)")
        traced (answer "(trace)")
        sum (answer "(1 + 2)")
        stored (answer "(Fred has (color (red)))")
        seen (on stored "(the color of Fred)")
        sit (answer "(new-situation)")]
    (is (zero? (get-in same [:query :unifications] 0)))
    (is (>= (get-in unified [:query :unifications] 0) 1))
    (is (zero? (get-in bare [:kb :runtime :kb-accesses] 0)))
    (is (>= (get-in seen [:kb :runtime :kb-accesses] 0) 1))
    (is (zero? (get-in traced [:query :max-depth] 0)))
    (is (>= (get-in bare [:query :max-depth] 0) 1))
    (is (>= (get-in sum [:query :max-depth] 0) 1))
    (is (>= (get-in sit [:query :skolems] 0) 1))))
