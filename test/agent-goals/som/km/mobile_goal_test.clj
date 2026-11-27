(ns som.km.mobile-goal-test
  (:require [clojure.data.json :as json]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [som.km.engine :as engine]
            [som.km.print :as print]
            [som.km.repl :as repl]
            [som.km.server :as server]))

(def ^:private loaded
  (engine/evaluate
   "(load-lib \"src/resources/som-component-library\" :silent t)"
   (engine/session)))

(defn- on [state expression]
  (let [result (engine/evaluate expression state)]
    (is (:ok result) (pr-str (select-keys result [:error :message])))
    (is (empty? (:errors result)) (pr-str (:errors result)))
    result))

(defn- in [state player expression]
  (on state (str "(in-situation " player " " expression ")")))

(defn- assert-in [state player expressions]
  (reduce #(in %1 player %2) state expressions))

(defn- answer [state player expression expected]
  (let [result (in state player expression)]
    (is (= expected (print/km-format (:value result))) expression)
    result))

(defn- query [state slot expected]
  (answer state "*PlayerA" (str "(the " slot " of *View)") expected))

(defn- mobile [id room experience level player]
  (str "(" id " has (instance-of (Som-Mobile)) (som-mobile-name (" id "))"
       (when room (str " (som-mobile-last-room (" room "))"))
       (when (some? experience) (str " (som-mobile-experience (" experience "))"))
       (when (some? level) (str " (som-mobile-experience-level (" level "))"))
       (when player (str " (som-player (" player "))")) ")"))

(def ^:private base-forms
  ["(*Goal has (instance-of (Som-Level-Goal)) (som-target-level (5))
               (som-risk-ceiling (cautious)) (som-budget-minutes (0)))"
   "(*Clock has (instance-of (Som-Progress-Projection)) (som-clock-kind (level))
                (som-clock-target (5)) (som-level (1)))"
   "(*View has (instance-of (Som-Goal-View)) (som-goal (*Goal))
               (som-progress (*Clock)) (som-mobile-search-from (*Start)))"
   "(*Start has (instance-of (Som-Explored-Room)) (som-room-exit ((:seq *East))))"
   "(*Hunt has (instance-of (Som-Explored-Room)))"
   "(*Lost has (instance-of (Som-Explored-Room)))"
   "(*East has (instance-of (Som-Room-Exit)) (som-exit-direction (east))
               (som-exit-to (*Hunt)) (som-requires-open (t)))"])

(defn- scenario
  ([forms] (scenario "*PlayerA" forms))
  ([player forms]
   (let [named (on loaded (str "(" player " has (instance-of (Som-Agentic-Player)))"))]
     (assert-in named player
                (concat base-forms
                        [(str "(" player " has (som-explored-room ((:seq *Start *Hunt *Lost))))")]
                        forms)))))

(deftest mobile-vocabulary-loads-with-fluent-player-owned-relations
  (is (:ok loaded))
  (is (empty? (:errors loaded)))
  (let [state (scenario [(mobile "*Rat" "*Hunt" 50 1 "f")
                         "(*PlayerA has (som-known-mobile ((:seq *Rat))))"])]
    (query state "som-mobile-search-status" "(ready)")
    (answer state "*PlayerA" "(the fluent-status of som-known-mobile)" "(*Fluent)")
    (answer state "*PlayerA" "(the inverse of som-known-mobile)" "(som-known-mobile-of)")
    (answer state "*PlayerA" "(the inverse of som-mobile-last-room)" "(som-mobile-last-room-of)")
    (answer state "*PlayerA" "(the som-mobile-last-room of *Rat)" "(*Hunt)")
    (let [request (in state "*PlayerA" "(*Path has (instance-of (Som-Route)))")]
      (answer request "*PlayerA" "(the som-route-context of *Path)" "(*Path)"))))

(deftest positive-experience-requires-an-identified-nonplayer-and-current-level-evidence
  (let [state (scenario [(mobile "*Rat" "*Hunt" 50 1 "f")
                         (mobile "*Zero" "*Hunt" 0 1 "f")
                         (mobile "*Negative" "*Hunt" -2 1 "f")
                         (mobile "*Old" "*Hunt" 900 2 "f")
                         (mobile "*Player" "*Hunt" 999 1 "t")
                         (mobile "*Unknown" "*Hunt" 999 1 nil)
                         "(*Nameless has (instance-of (Som-Mobile)) (som-player (f))
                                         (som-mobile-experience (999)) (som-mobile-experience-level (1)))"
                         "(*PlayerA has (som-known-mobile ((:seq *Rat *Zero *Negative *Old *Player *Unknown *Nameless))))"])]
    (query state "som-experience-mobile" "((:seq *Rat))")))

(deftest missing-evidence-is-an-investigation-question
  (let [state (scenario [(mobile "*Unmeasured" "*Hunt" nil nil "f")
                         (mobile "*Old" "*Hunt" 50 2 "f")
                         (mobile "*Unknown" "*Hunt" 50 1 nil)
                         (mobile "*Unlocated" nil 50 1 "f")
                         (mobile "*Zero" "*Hunt" 0 1 "f")
                         (mobile "*Player" "*Hunt" nil nil "t")
                         "(*PlayerA has (som-known-mobile ((:seq *Unmeasured *Old *Unknown *Unlocated *Zero *Player))))"])]
    (query state "som-mobile-needs-evidence" "((:seq *Unmeasured *Old *Unknown *Unlocated))")
    (query state "som-experience-mobile" "((:seq *Unlocated))")
    (query state "som-reachable-mobile" "((:seq))")
    (query state "som-mobile-target" "nil")))

(deftest target-selection-ranks-reachable-yields-and-keeps-encounter-order-on-ties
  (let [state (scenario [(mobile "*Low" "*Hunt" 20 1 "f")
                         (mobile "*First" "*Hunt" 50 1 "f")
                         (mobile "*Second" "*Hunt" 50 1 "f")
                         (mobile "*Unreachable" "*Lost" 999 1 "f")
                         "(*PlayerA has (som-known-mobile ((:seq *Low *First *Second *Unreachable))))"])]
    (query state "som-reachable-mobile" "((:seq *Low *First *Second))")
    (query state "som-mobile-target" "(*First)")
    (query state "som-mobile-destination" "(*Hunt)")
    (query state "som-mobile-route" "((:seq *East))")
    (answer state "*PlayerA" "(the som-requires-open of *East)" "(t)")))

(deftest an-empty-route-is-a-supported-arrival-and-not-a-missing-path
  (let [state (scenario [(mobile "*Here" "*Start" 50 1 "f")
                         "(*PlayerA has (som-known-mobile ((:seq *Here))))"])]
    (query state "som-mobile-target" "(*Here)")
    (query state "som-mobile-route" "((:seq))")))

(deftest a-last-room-outside-the-explored-map-is-not-reachable
  (let [state (scenario [(mobile "*Outside" "*Elsewhere" 50 1 "f")
                         "(*PlayerA has (som-known-mobile ((:seq *Outside))))"])]
    (query state "som-experience-mobile" "((:seq *Outside))")
    (query state "som-reachable-mobile" "((:seq))")
    (query state "som-mobile-route" "nil")))

(deftest no-records-and-no-route-context-have-different-results
  (let [empty-state (scenario [])
        no-origin (in empty-state "*PlayerA" "(*View now-has (som-mobile-search-from ()))")]
    (query empty-state "som-experience-mobile" "((:seq))")
    (query empty-state "som-reachable-mobile" "((:seq))")
    (query no-origin "som-reachable-mobile" "nil")
    (query empty-state "som-mobile-target" "nil")))

(deftest inactive-or-incomplete-level-goals-do-not-select-mobiles
  (doseq [[form status]
          [["(*Goal now-has (som-target-level (1)))" "(stale)"]
           ["(*Clock now-has (som-level (5)))" "(met)"]
           ["(*Clock now-has (som-level ()))" "(incomplete)"]
           ["(*Goal now-has (som-kind-in (gear)))" "(unsupported-goal)"]
           ["(*View now-has (som-goal ()))" "(needs-goal)"]
           ["(*View now-has (som-progress ()))" "(needs-progress)"]]]
    (testing status
      (let [state (in (scenario [(mobile "*Rat" "*Hunt" 50 1 "f")
                                 "(*PlayerA has (som-known-mobile ((:seq *Rat))))"])
                      "*PlayerA" form)]
        (query state "som-mobile-search-status" status)
        (query state "som-experience-mobile" "nil")
        (query state "som-mobile-target" "nil")))))

(deftest a-new-level-needs-new-experience-evidence
  (let [state (scenario [(mobile "*Rat" "*Hunt" 50 1 "f")
                         "(*PlayerA has (som-known-mobile ((:seq *Rat))))"
                         "(*Clock now-has (som-level (2)))"])]
    (query state "som-experience-mobile" "((:seq))")
    (query state "som-mobile-needs-evidence" "((:seq *Rat))")))

(deftest a-new-view-reconsiders-replaced-evidence-and-a-changed-map
  (let [state (scenario [(mobile "*Rat" "*Hunt" 50 1 "f")
                         "(*PlayerA has (som-known-mobile ((:seq *Rat))))"])
        queried (query state "som-mobile-target" "(*Rat)")
        revised (assert-in queried "*PlayerA"
                           ["(*Rat now-has (som-mobile-experience (0)))"
                            "(*NewView has (instance-of (Som-Goal-View)) (som-goal (*Goal))
                                           (som-progress (*Clock)) (som-mobile-search-from (*Start)))"])
        rerouted (assert-in queried "*PlayerA"
                            ["(*Start now-has (som-room-exit ((:seq *NewExit))))"
                             "(*NewExit has (instance-of (Som-Room-Exit)) (som-exit-to (*Hunt)))"
                             "(*NewView has (instance-of (Som-Goal-View)) (som-goal (*Goal))
                                            (som-progress (*Clock)) (som-mobile-search-from (*Start)))"])]
    (answer revised "*PlayerA" "(the som-mobile-target of *NewView)" "nil")
    (answer rerouted "*PlayerA" "(the som-mobile-route of *NewView)" "((:seq *NewExit))")))

(deftest players-keep-their-mobile-evidence-and-conclusions-separate
  (let [first-player (scenario [(mobile "*Rat" "*Hunt" 50 1 "f")
                                "(*PlayerA has (som-known-mobile ((:seq *Rat))))"])
        second-player (on first-player "(*PlayerB has (instance-of (Som-Agentic-Player)))")
        both (assert-in second-player "*PlayerB"
                        (concat base-forms
                                ["(*PlayerB has (som-explored-room ((:seq *Start *Hunt))))"
                                 (mobile "*Rat" "*Hunt" 0 1 "f")
                                 "(*PlayerB has (som-known-mobile ((:seq *Rat))))"]))]
    (query both "som-mobile-target" "(*Rat)")
    (answer both "*PlayerB" "(the som-mobile-target of *View)" "nil")
    (answer both "*PlayerB" "(the som-mobile-experience of *Rat)" "(0)")
    (answer both "*PlayerB" "(the som-known-mobile of *PlayerA)" "nil")))

(deftest a-new-view-reconsiders-an-intermediate-route-change
  (let [state (scenario [(mobile "*Rat" "*Lost" 50 1 "f")
                         "(*PlayerA has (som-known-mobile ((:seq *Rat))))"
                         "(*Hunt has (som-room-exit ((:seq *South))))"
                         "(*South has (instance-of (Som-Room-Exit)) (som-exit-to (*Lost)))"])
        queried (query state "som-mobile-route" "((:seq *East *South))")
        changed (assert-in queried "*PlayerA"
                           ["(*Hunt now-has (som-room-exit ((:seq *OtherExit))))"
                            "(*OtherExit has (instance-of (Som-Room-Exit)) (som-exit-to (*Lost)))"
                            "(*NewView has (instance-of (Som-Goal-View)) (som-goal (*Goal))
                                           (som-progress (*Clock)) (som-mobile-search-from (*Start)))"])]
    (answer changed "*PlayerA" "(the som-mobile-route of *NewView)"
            "((:seq *East *OtherExit))")))

(deftest prompt-and-http-query-the-same-mobile-conclusion
  (let [state (scenario [(mobile "*Rat" "*Hunt" 50 1 "f")
                         "(*PlayerA has (som-known-mobile ((:seq *Rat))))"])
        expression "(in-situation *PlayerA (the som-mobile-target of *View))"
        reply (repl/respond expression (atom state))
        response (server/handler
                  {:request-method :post :uri "/query"
                   :headers {"content-type" "text/plain"}
                   :body (java.io.ByteArrayInputStream.
                          (.getBytes expression java.nio.charset.StandardCharsets/UTF_8))}
                  (atom state))
        body (json/read-str (:body response) :key-fn keyword)]
    (is (false? (:leave reply)))
    (is (str/starts-with? (:text reply) "(*Rat)"))
    (is (= 200 (:status response)))
    (is (empty? (:errors body)))
    (is (= [{:symbol "*Rat"}] (:value body)))))
