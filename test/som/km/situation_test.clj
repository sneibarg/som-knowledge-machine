(ns som.km.situation-test
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.frame :as frame]
            [som.km.print :as print]
            [som.km.read :as read]
            [som.km.situations :as situations]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(defn- term-of [text]
  (:value (read/read-term text)))

(defn- answer [text]
  (engine/evaluate text))

(defn- on
  [previous text]
  (engine/evaluate text {:kb (:kb previous) :query (:query previous)}))

(defn- name-of [result]
  (term/symbol-name (term/car (:value result))))

(deftest a-new-situation-is-entered-and-a-body-restores-global
  (let [created (answer "(new-situation)")
        left (on created "(global-situation)")
        read (on left "(in-situation _Situation1 (the color of Fred))")
        back (on read "(curr-situation)")
        closed (on created "(end-situation)")
        global (on created "(global-situation)")]
    (is (:ok created))
    (is (= (term-of "(_Situation1)") (:value created)))
    (is (= (term-of "(_Situation1)") (:value (on created "(curr-situation)"))))
    (is (= (term-of "(*Global)") (:value back)))
    (is (= (term-of "(*Global)") (:value closed)))
    (is (= (term-of "(*Global)") (:value global)))
    (is (empty? (:errors created)))))

(deftest a-cat-stays-refused-and-a-situation-is-created
  (let [cat (answer "(a Cat)")
        with (answer "(a Cat with (color (black)))")
        made (answer "(a Situation)")]
    (is (= "not-ported" (:error cat)))
    (is (= "This form is not ported yet: (a Cat)." (:message cat)))
    (is (= "not-ported" (:error with)))
    (is (= "This form is not ported yet: (a Cat with (color (black)))." (:message with)))
    (is (:ok made))
    (is (str/starts-with? (name-of made) "_Situation"))
    (is (nil? (:error made)))))

(deftest a-local-fluent-stays-out-of-global-and-global-fluents-are-refused
  (let [sit (answer "(new-situation)")
        stored (on sit "(Fred has (color (red)))")
        seen (on stored "(the color of Fred)")
        global (frame/get-vals (:kb seen) (symbol "Fred") (symbol "color")
                               :situation (symbol "*Global")
                               :dereference? false)
        earlier (answer "(Fred has (color (red)))")
        entered (on earlier "(new-situation)")
        returned (on entered "(global-situation)")
        blocked (on returned "(the color of Fred)")]
    (is (= (term-of "(red)") (:value seen)))
    (is (empty? (:errors seen)))
    (is (nil? (:value global)))
    (is (nil? (:value blocked)))
    (is (:ok blocked))
    (is (str/includes? (first (:errors blocked)) "global situation"))))

(deftest an-inertial-value-projects-and-a-fluent-does-not
  (let [declared (answer "(location has (fluent-status (*Inertial-Fluent)))")
        sit (on declared "(new-situation)")
        home (on sit "(Fred has (location (home)))")
        nxt (on home "(next-situation)")
        seen (on nxt "(the location of Fred)")
        why (on seen "(why)")
        colored (answer "(new-situation)")
        red (on colored "(Fred has (color (red)))")
        moved (on red "(next-situation)")
        faded (on moved "(the color of Fred)")]
    (is (= (term-of "(home)") (:value seen)))
    (is (empty? (:errors seen)))
    (is (str/includes? (print/km-format
                        (frame/explanations (:kb seen) (symbol "Fred")
                                            :situation (frame/current-situation (:kb seen))))
                       "projected-from"))
    (is (= (term-of "(t)") (:value why)))
    (is (nil? (:value faded)))
    (is (empty? (:errors faded)))))

(deftest a-single-valued-inertial-slot-projects-its-value
  (let [declared (answer "(age has (fluent-status (*Inertial-Fluent)))")
        card (on declared "(age has (cardinality (N-to-1)))")
        sit (on card "(new-situation)")
        aged (on sit "(Fred has (age (30)))")
        nxt (on aged "(next-situation)")
        seen (on nxt "(the age of Fred)")]
    (is (= (term-of "(30)") (:value seen)))
    (is (empty? (:errors seen)))))

(deftest a-global-fluent-is-visible-through-the-supersituation-climb
  (let [stored (answer "(Fred has (color (red)))")
        sit (on stored "(new-situation)")
        seen (on sit "(the color of Fred)")
        supers (on sit "(the supersituations of _Situation1)")]
    (is (= (term-of "(red)") (:value seen)))
    (is (empty? (:errors seen)))
    (is (= (term-of "(*Global)") (:value supers)))))

(deftest a-non-fluent-in-a-theory-stays-in-that-theory
  (let [made (answer "(a Theory)")
        theory (term/car (:value made))
        declared (on made "(secret has (fluent-status (*Non-Fluent)))")
        entered (on declared (str "(in-theory " (print/km-format theory)
                                  " (Fred has (secret (hidden))))"))
        local (frame/get-vals (:kb entered) (symbol "Fred") (symbol "secret")
                              :situation theory
                              :dereference? false)
        global (frame/get-vals (:kb local) (symbol "Fred") (symbol "secret")
                               :situation (symbol "*Global")
                               :dereference? false)
        back (on entered "(curr-situation)")]
    (is (str/starts-with? (term/symbol-name theory) "_Theory"))
    (is (utils/member? (symbol "hidden") (:value local)))
    (is (nil? (:value global)))
    (is (= (term-of "(*Global)") (:value back)))))

(deftest seeing-a-theory-exposes-its-fluent-and-hiding-it-removes-that-fluent
  (let [made (answer "(a Theory)")
        theory (term/car (:value made))
        entered (on made (str "(in-theory " (print/km-format theory)
                              " (Fred has (color (red))))"))
        other (on entered (str "(in-theory " (print/km-format theory)
                               " (Sue has (color (blue))))"))
        missed (on other "(the color of Fred)")
        shown (on missed (str "(see-theory " (print/km-format theory) ")"))
        seen (on shown "(the color of Fred)")
        hidden (on seen (str "(hide-theory " (print/km-format theory) ")"))
        cached (on hidden "(the color of Fred)")
        unseen (on hidden "(the color of Sue)")]
    (is (nil? (:value missed)))
    (is (utils/member? theory (:value shown)))
    (is (= (term-of "(red)") (:value seen)))
    (is (= (term-of "(t)") (:value hidden)))
    (is (= (term-of "(red)") (:value cached)))
    (is (nil? (:value unseen)))))

(deftest an-action-asserts-its-add-list-in-the-next-situation
  (let [sit (answer "(new-situation)")
        act (on sit "(_Move has (add-list ((:triple Fred color green))))")
        done (on act "(do _Move)")
        next-name (term/car (:value done))
        here (on done "(curr-situation)")
        seen (on done (str "(in-situation " (print/km-format next-name)
                           " (the color of Fred))"))
        stayed (on act "(do-and-next _Move)")
        there (on stayed "(curr-situation)")]
    (is (= (term-of "(green)") (:value seen)))
    (is (utils/eql? (term/car (:value sit)) (term/car (:value here))))
    (is (not (utils/eql? next-name (term/car (:value here)))))
    (is (utils/eql? (term/car (:value stayed)) (term/car (:value there))))))

(deftest a-deletion-blocks-projection-of-an-inertial-value
  (let [declared (answer "(location has (fluent-status (*Inertial-Fluent)))")
        sit (on declared "(new-situation)")
        home (on sit "(Fred has (location (home)))")
        act (on home "(_Move has (del-list ((:triple Fred location home))))")
        done (on act "(do-and-next _Move)")
        seen (on done "(the location of Fred)")]
    (is (nil? (:value seen)))
    (is (not (utils/member? (symbol "home") (:value seen))))))

(deftest a-bad-situation-is-a-user-error-and-prototype-entry-stays-blocked
  (let [bad (answer "(in-situation Fred)")
        sit (answer "(new-situation)")
        blocked (on sit "(a-prototype Cat)")]
    (is (:ok bad))
    (is (nil? (:value bad)))
    (is (not= "not-ported" (:error bad)))
    (is (str/includes? (first (:errors bad)) "isn't declared an instance of Situation"))
    (is (nil? (:value blocked)))
    (is (some #(str/includes? % "Can't enter prototype mode when in a Situation!")
              (:errors blocked)))))

(deftest the-prompt-names-the-current-situation-or-theory
  (let [sit (answer "(new-situation)")
        made (answer "(a Theory)")
        theory (term/car (:value made))
        entered (on made (str "(in-theory " (print/km-format theory) ")"))]
    (is (= (str "[" (name-of sit) "] KM> ")
           (situations/prompt-text (:kb sit))))
    (is (= (str "{" (term/symbol-name theory) "} KM> ")
           (situations/prompt-text (:kb entered))))
    (is (= "KM> " (situations/prompt-text (:kb (answer "(curr-situation)")))))))
