(ns som.km.gear-recovery-test
  (:require [clojure.data.json :as json]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [som.km.engine :as engine]
            [som.km.print :as print]
            [som.km.repl :as repl]
            [som.km.server :as server]))

(def ^:private loaded
  (engine/evaluate "(load-lib \"src/resources/som-component-library\" :silent t)"
                   (engine/session)))

(defn- on [state expression]
  (let [result (engine/evaluate expression state)]
    (is (:ok result) (pr-str (select-keys result [:error :message])))
    (is (empty? (:errors result)) (pr-str [expression (:errors result)]))
    result))

(defn- inside [state player expression]
  (on state (str "(in-situation " player " " expression ")")))

(defn- assert-in [state player forms]
  (reduce #(inside %1 player %2) state forms))

(defn- ask [state expression expected]
  (let [result (inside state "*PlayerA" expression)]
    (is (= expected (print/km-format (:value result))) expression)
    result))

(defn- answer [state slot expected]
  (ask state (str "(the " slot " of *Request)") expected))

(defn- piece [name slot & [extras]]
  (str "(" name " has (instance-of (Som-Gear-Piece))"
       " (som-short (\"" (subs name 1) "\")) (som-keyword (gear))"
       " (som-worn-slot (" slot ")) (som-gear-usable (t)) " extras ")"))

(defn- source [name kind item & [extras holder]]
  (str "(" name " has (instance-of (Som-Gear-Source))"
       " (som-gear-source-kind (" kind ")) (som-gear-source-item (" item "))"
       " (som-gear-source-room (*Start)) (som-holder (" (or holder "*Provider") "))"
       " (som-gear-source-available (t)) (som-gear-source-permitted (t))"
       " (som-gear-source-accessible (t)) " extras ")"))

(def ^:private base
  ["(*Start has (instance-of (Som-Explored-Room)))"
   "(*PlayerA has (som-explored-room ((:seq *Start))))"
   "(*Observed has (instance-of (Som-Gear-State)) (som-gear-confirmed (t))
                   (som-gear-owned ((:seq))) (som-gear-equipped ((:seq)))
                   (som-gear-coins (20)) (som-gear-room (*Start)) (som-level (1))
                   (som-alignment-side (good)))"
   "(*PlayerA has (som-gear-state (*Observed)))"
   "(*Goal has (instance-of (Som-Gear-Goal)) (som-gear-action (regear))
               (som-gear-risk (cautious)) (som-gear-wanted ((:seq *Sword))))"
   "(*Request has (instance-of (Som-Regear-Request))
                  (som-regear-goal (*Goal)) (som-regear-start (*Observed)))"
   "(*Provider has (instance-of (Som-Mobile)) (som-player (f)))"])

(defn- scenario [forms]
  (let [named (on loaded "(*PlayerA has (instance-of (Som-Agentic-Player)))")]
    (assert-in named "*PlayerA" (concat base forms))))

(defn- kinds [state expected]
  (ask state "(the som-step-kind of (the som-regear-strategy of *Request))" expected))

(defn- mobile-model [& [requires]]
  (str " (som-gear-source-loot-known (t)) (som-gear-source-model-known (t))"
       " (som-gear-source-assessed-level (1)) (som-gear-source-risk (cautious))"
       " (som-gear-source-requires ((:seq " requires ")))"))

(deftest a-room-piece-produces-a-proposal-without-changing-observed-ownership
  (is (empty? (:errors loaded)))
  (let [state (scenario [(piece "*Sword" "wield")
                         (source "*Floor" "room" "*Sword")
                         "(*PlayerA has (som-known-gear-source ((:seq *Floor))))"])
        planned (answer state "som-regear-status" "(planned)")]
    (kinds planned "((:seq take equip))")
    (answer planned "som-regear-cost" "(0)")
    (ask planned "(the som-gear-equipped of (the som-regear-final-state of *Request))" "((:seq *Sword))")
    (ask planned "(the som-gear-owned of *Observed)" "((:seq))")
    (ask planned "(the som-gear-state of *PlayerA)" "(*Observed)")))

(deftest a-purchase-debits-the-projected-purse-only
  (let [state (scenario [(piece "*Sword" "wield")
                         (source "*Shop" "shop" "*Sword" "(som-gear-source-price (7))")
                         "(*PlayerA has (som-known-gear-source ((:seq *Shop))))"])]
    (answer state "som-regear-status" "(planned)")
    (kinds state "((:seq buy equip))")
    (answer state "som-regear-cost" "(7)")
    (ask state "(the som-gear-coins of (the som-regear-final-state of *Request))" "(13)")
    (ask state "(the som-gear-coins of *Observed)" "(20)")))

(deftest a-shop-and-intermediate-mob-chain-enables-stronger-gear
  (let [state (scenario [(piece "*Sword" "wield")
                         (piece "*Club" "wield")
                         (piece "*Spear" "wield")
                         "(*Bandit-mob has (instance-of (Som-Mobile)) (som-player (f)))"
                         "(*Guard-mob has (instance-of (Som-Mobile)) (som-player (f)))"
                         (source "*Club-shop" "shop" "*Club" "(som-gear-source-price (5))")
                         (source "*Bandit" "mobile" "*Spear" (mobile-model "*Club") "*Bandit-mob")
                         (source "*Guard" "mobile" "*Sword" (mobile-model "*Spear") "*Guard-mob")
                         "(*PlayerA has (som-known-gear-source ((:seq *Guard *Bandit *Club-shop))))"])]
    (answer state "som-regear-status" "(planned)")
    (kinds state "((:seq buy equip defeat-loot equip defeat-loot equip))")
    (answer state "som-regear-cost" "(5)")
    (ask state "(the som-gear-equipped of (the som-regear-final-state of *Request))" "((:seq *Sword))")
    (ask state "(the som-gear-owned of *Observed)" "((:seq))")))

(deftest corpse-loot-is-distinct-from-examined-player-and-mobile-equipment
  (let [state (scenario [(piece "*Sword" "wield")
                         (source "*Inspection" "player" "*Sword")
                         (source "*Mob-wearing" "mobile" "*Sword"
                                 "(som-gear-source-model-known (t)) (som-gear-source-assessed-level (1))
                                  (som-gear-source-risk (cautious)) (som-gear-source-requires ((:seq)))")
                         "(*PlayerA has (som-known-gear-source ((:seq *Inspection *Mob-wearing))))"])
        corpse (assert-in state "*PlayerA"
                          [(source "*Corpse" "corpse" "*Sword")
                           "(*PlayerA now-has (som-known-gear-source ((:seq *Inspection *Mob-wearing *Corpse))))"])]
    (answer state "som-regear-observations" "((:seq *Inspection *Mob-wearing))")
    (answer state "som-regear-status" "(blocked)")
    (answer state "som-regear-next-step" "nil")
    (answer corpse "som-regear-status" "(planned)")
    (kinds corpse "((:seq loot equip))")))

(deftest prices-and-the-emergency-reserve-bound-purchases
  (doseq [[extra request status]
          [["(som-gear-source-price (21))" nil "(blocked)"]
           ["(som-gear-source-price (-1))" nil "(blocked)"]
           [nil nil "(blocked)"]
           ["(som-gear-source-price (6))" "(*Request has (som-regear-reserve-in (15)))" "(blocked)"]
           ["(som-gear-source-price (5))" "(*Request has (som-regear-reserve-in (15)))" "(planned)"]]]
    (let [state (scenario (cond-> [(piece "*Sword" "wield")
                                   (source "*Shop" "shop" "*Sword" extra)
                                   "(*PlayerA has (som-known-gear-source ((:seq *Shop))))"]
                           request (conj request)))]
      (answer state "som-regear-status" status))))

(deftest cumulative-purchases-use-one-purse-and-select-supported-cheaper-options
  (let [state (scenario [(piece "*Sword" "wield") (piece "*Armor" "body")
                         "(*Goal now-has (som-gear-wanted ((:seq *Sword *Armor))))"
                         (source "*Sword-shop" "shop" "*Sword" "(som-gear-source-price (12))")
                         (source "*Armor-shop" "shop" "*Armor" "(som-gear-source-price (12))")
                         "(*PlayerA has (som-known-gear-source ((:seq *Sword-shop *Armor-shop))))"])
        cheaper (assert-in state "*PlayerA"
                           [(source "*Cheap-armor" "shop" "*Armor" "(som-gear-source-price (7))")
                            "(*PlayerA now-has (som-known-gear-source ((:seq *Sword-shop *Armor-shop *Cheap-armor))))"])]
    (answer state "som-regear-status" "(blocked)")
    (answer cheaper "som-regear-status" "(planned)")
    (answer cheaper "som-regear-cost" "(19)")
    (ask cheaper "(the som-gear-coins of (the som-regear-final-state of *Request))" "(1)")
    (kinds cheaper "((:seq buy equip buy equip))")))

(deftest shared-intermediate-gear-is-not-purchased-twice-and-conflicting-weapons-are-reequipped
  (let [state (scenario [(piece "*Sword" "wield") (piece "*Armor" "body") (piece "*Club" "wield")
                         "(*Goal now-has (som-gear-wanted ((:seq *Sword *Armor))))"
                         (source "*Shop" "shop" "*Club" "(som-gear-source-price (5))")
                         "(*Armor-provider has (instance-of (Som-Mobile)) (som-player (f)))"
                         (source "*Sword-mob" "mobile" "*Sword" (mobile-model "*Club"))
                         (source "*Armor-mob" "mobile" "*Armor" (mobile-model "*Club") "*Armor-provider")
                         "(*PlayerA has (som-known-gear-source ((:seq *Sword-mob *Armor-mob *Shop))))"])]
    (answer state "som-regear-status" "(planned)")
    (answer state "som-regear-cost" "(5)")
    (kinds state "((:seq buy equip defeat-loot equip equip defeat-loot equip equip))")
    (ask state "(the som-gear-equipped of (the som-regear-final-state of *Request))" "((:seq *Armor *Sword))")))

(deftest ancestors-reserve-their-purchase-cost-while-obtaining-prerequisites
  (let [state (scenario [(piece "*Sword" "wield") (piece "*Club" "wield")
                         (source "*Expensive-club" "shop" "*Club" "(som-gear-source-price (15))")
                         (source "*Cheap-club" "shop" "*Club" "(som-gear-source-price (5))")
                         (source "*Sword-shop" "shop" "*Sword"
                                 "(som-gear-source-price (10)) (som-gear-source-requires ((:seq *Club)))")
                         "(*PlayerA has (som-known-gear-source ((:seq *Sword-shop *Expensive-club *Cheap-club))))"])]
    (answer state "som-regear-status" "(planned)")
    (answer state "som-regear-cost" "(15)")
    (ask state "(the som-step-source of (the som-regear-next-step of *Request))" "(*Cheap-club)")))

(deftest current-gear-and-empty-goals-have-valid-empty-or-equip-only-strategies
  (let [state (scenario [(piece "*Sword" "wield")
                         "(*Observed now-has (som-gear-owned ((:seq *Sword))))"])
        worn (inside state "*PlayerA" "(*Observed now-has (som-gear-equipped ((:seq *Sword))))")
        no-goal (inside state "*PlayerA" "(*Goal now-has (som-gear-wanted ((:seq))))")]
    (kinds state "((:seq equip))")
    (answer worn "som-regear-status" "(complete)")
    (answer worn "som-regear-strategy" "((:seq))")
    (answer no-goal "som-regear-status" "(complete)")
    (answer no-goal "som-regear-next-step" "nil")))

(deftest incompatible-final-slots-are-rejected-but-paired-slots-are-distinct
  (let [state (scenario [(piece "*Sword" "finger" "(som-slot-index (1))")
                         (piece "*Ring" "finger" "(som-slot-index (1))")
                         "(*Goal now-has (som-gear-wanted ((:seq *Sword *Ring))))"
                         "(*Observed now-has (som-gear-owned ((:seq *Sword *Ring))))"])
        paired (inside state "*PlayerA" "(*Ring now-has (som-slot-index (2)))")]
    (answer state "som-regear-status" "(incompatible-goals)")
    (answer state "som-regear-strategy" "nil")
    (answer paired "som-regear-status" "(planned)")
    (kinds paired "((:seq equip equip))")))

(deftest unusable-or-restricted-gear-does-not-become-a-viable-target
  (doseq [change ["(*Sword now-has (som-gear-usable (f)))"
                  "(*Sword now-has (som-gear-usable ()))"
                  "(*Sword has (som-object-level (2)))"
                  "(*Sword has (som-level-block (refused)))"
                  "(*Sword has (som-alignment-block (zapped)))"
                  "(*Sword has (som-rejects ((:seq good))))"]]
    (let [state (scenario [(piece "*Sword" "wield")
                           (source "*Floor" "room" "*Sword")
                           "(*PlayerA has (som-known-gear-source ((:seq *Floor))))" change])]
      (answer state "som-regear-status" "(blocked)")
      (answer state "som-regear-next-step" "nil"))))

(deftest cycles-and-transition-limits-produce-bounded-refusals
  (let [state (scenario [(piece "*Sword" "wield") (piece "*Club" "wield")
                         (source "*Sword-mob" "mobile" "*Sword" (mobile-model "*Club"))
                         (source "*Club-mob" "mobile" "*Club" (mobile-model "*Sword"))
                         "(*PlayerA has (som-known-gear-source ((:seq *Sword-mob *Club-mob))))"])
        no-steps (scenario [(piece "*Sword" "wield")
                            (source "*Floor" "room" "*Sword")
                            "(*PlayerA has (som-known-gear-source ((:seq *Floor))))"
                            "(*Request has (som-regear-limit-in (1)))"])]
    (answer state "som-regear-status" "(blocked)")
    (answer state "som-regear-strategy" "nil")
    (answer no-steps "som-regear-status" "(blocked)")))

(deftest known-unavailable-or-unpermitted-sources-do-not-authorize-acquisition
  (doseq [change ["(*Floor now-has (som-gear-source-available (f)))"
                  "(*Floor now-has (som-gear-source-permitted (f)))"
                  "(*Floor now-has (som-gear-source-accessible (f)))"]]
    (let [state (scenario [(piece "*Sword" "wield") (source "*Floor" "corpse" "*Sword")
                           "(*PlayerA has (som-known-gear-source ((:seq *Floor))))" change])]
      (answer state "som-regear-status" "(blocked)"))))

(deftest mobile-loot-requires-current-level-models-allowed-risk-and-a-nonplayer
  (doseq [change ["(*Mob now-has (som-gear-source-assessed-level (2)))"
                  "(*Mob now-has (som-gear-source-risk (bold)))"
                  "(*Mob now-has (som-gear-source-model-known ()))"
                  "(*Mob now-has (som-gear-source-requires ()))"
                  "(*Provider now-has (som-player (t)))"]]
    (let [state (scenario [(piece "*Sword" "wield")
                           (source "*Mob" "mobile" "*Sword" (mobile-model))
                           "(*PlayerA has (som-known-gear-source ((:seq *Mob))))" change])]
      (answer state "som-regear-status" "(blocked)")))
  (let [state (scenario [(piece "*Sword" "wield")
                         (source "*Mob" "mobile" "*Sword" (mobile-model))
                         "(*PlayerA has (som-known-gear-source ((:seq *Mob))))"
                         "(*Mob now-has (som-gear-source-risk (bold)))"
                         "(*Goal now-has (som-gear-risk (bold)))"])]
    (answer state "som-regear-status" "(planned)")))

(deftest travel-reuses-the-route-chain-and-updates-only-the-projected-room
  (let [state (scenario [(piece "*Sword" "wield")
                         "(*Market has (instance-of (Som-Explored-Room)))"
                         "(*East has (instance-of (Som-Room-Exit)) (som-exit-direction (east))
                                     (som-exit-to (*Market)) (som-requires-open (t)))"
                         "(*Start has (som-room-exit ((:seq *East))))"
                         "(*PlayerA now-has (som-explored-room ((:seq *Start *Market))))"
                         (source "*Shop" "shop" "*Sword" "(som-gear-source-price (2))")
                         "(*Shop now-has (som-gear-source-room (*Market)))"
                         "(*PlayerA has (som-known-gear-source ((:seq *Shop))))"])]
    (answer state "som-regear-status" "(planned)")
    (kinds state "((:seq travel buy equip))")
    (ask state "(the som-step-route of (the som-regear-next-step of *Request))" "((:seq *East))")
    (ask state "(the som-gear-room of (the som-regear-final-state of *Request))" "(*Market)")
    (ask state "(the som-gear-room of *Observed)" "(*Start)")))

(deftest death-discards-lost-equipment-and-replans-through-an-affordable-intermediate
  (let [state (scenario [(piece "*Sword" "wield") (piece "*Club" "wield")
                         "(*Observed now-has (som-gear-owned ((:seq *Sword))) (som-gear-equipped ((:seq *Sword))))"
                         "(*Goal has (som-gear-met (t)))"])
        old (answer state "som-regear-status" "(complete)")
        died (assert-in old "*PlayerA"
                        ["(*After-death has (instance-of (Som-Gear-State)) (som-gear-confirmed (t))
                                           (som-gear-owned ((:seq))) (som-gear-equipped ((:seq)))
                                           (som-gear-coins (2)) (som-gear-room (*Start)) (som-level (1)))"
                         "(*PlayerA now-has (som-gear-state (*After-death)))"
                         (source "*Club-shop" "shop" "*Club" "(som-gear-source-price (1))")
                         (source "*Mob" "mobile" "*Sword" (mobile-model "*Club"))
                         "(*PlayerA has (som-known-gear-source ((:seq *Mob *Club-shop))))"
                         "(*Stale has (instance-of (Som-Regear-Request)) (som-regear-goal (*Goal)) (som-regear-start (*Observed)))"
                         "(*Recovery has (instance-of (Som-Regear-Request)) (som-regear-goal (*Goal)) (som-regear-start (*After-death)))"])]
    (ask died "(the som-regear-status of *Stale)" "(stale)")
    (ask died "(the som-regear-status of *Recovery)" "(planned)")
    (ask died "(the som-step-kind of (the som-regear-strategy of *Recovery))"
         "((:seq buy equip defeat-loot equip))")
    (ask died "(the som-regear-cost of *Recovery)" "(1)")
    (ask died "(the som-gear-owned of *After-death)" "((:seq))")))

(deftest incomplete-inconsistent-and-unsupported-inputs-have-domain-results
  (doseq [[change expected]
          [["(*Observed now-has (som-gear-coins ()))" "(incomplete)"]
           ["(*Observed now-has (som-gear-equipped ((:seq *Sword))))" "(inconsistent)"]
           ["(*Observed now-has (som-gear-confirmed (f)))" "(inconsistent)"]
           ["(*Goal now-has (som-gear-action (enchant)))" "(unsupported-goal)"]
           ["(*Request has (som-regear-limit-in (-1)))" "(invalid)"]]]
    (let [state (scenario [(piece "*Sword" "wield") change])]
      (answer state "som-regear-status" expected)
      (answer state "som-regear-strategy" "nil"))))

(deftest player-situations-isolate-sources-purses-and-regearing-results
  (let [state (scenario [(piece "*Sword" "wield") (source "*Floor" "room" "*Sword")
                         "(*PlayerA has (som-known-gear-source ((:seq *Floor))))"])
        named (on state "(*PlayerB has (instance-of (Som-Agentic-Player)))")
        both (assert-in named "*PlayerB"
                        (concat (map #(str/replace % "*PlayerA" "*PlayerB") base)
                                [(piece "*Sword" "wield") (source "*Floor" "room" "*Sword")
                                 "(*Floor now-has (som-gear-source-permitted (f)))"
                                 "(*PlayerB has (som-known-gear-source ((:seq *Floor))))"]))
        second (inside both "*PlayerB" "(the som-regear-status of *Request)")]
    (is (= "(blocked)" (print/km-format (:value second))))
    (answer both "som-regear-status" "(planned)")))

(deftest prompt-and-http-expose-the-same-regearing-conclusion
  (let [state (scenario [(piece "*Sword" "wield") (source "*Floor" "room" "*Sword")
                         "(*PlayerA has (som-known-gear-source ((:seq *Floor))))"])
        expression "(in-situation *PlayerA (the som-regear-status of *Request))"
        reply (repl/respond expression (atom state))
        response (server/handler {:request-method :post :uri "/query"
                                  :headers {"content-type" "text/plain"}
                                  :body (java.io.ByteArrayInputStream. (.getBytes expression "UTF-8"))}
                                 (atom state))
        body (json/read-str (:body response) :key-fn keyword)]
    (is (str/starts-with? (:text reply) "(planned)"))
    (is (= 200 (:status response)))
    (is (= [{:symbol "planned"}] (:value body)))
    (is (empty? (:errors body)))))

(deftest contradictory-worn-slots-and-unknown-target-slots-have-distinct-results
  (let [state (scenario [(piece "*Sword" "wield") (piece "*Club" "wield")
                         "(*Observed now-has (som-gear-owned ((:seq *Sword *Club)))
                                            (som-gear-equipped ((:seq *Sword *Club))))"])
        unknown (scenario ["(*Sword has (instance-of (Som-Gear-Piece)) (som-gear-usable (t)))"])]
    (answer state "som-regear-status" "(inconsistent)")
    (answer state "som-regear-strategy" "nil")
    (answer unknown "som-regear-status" "(needs-gear-evidence)")))

(deftest predicted-equipment-is-not-a-confirmed-observation
  (let [state (scenario [(piece "*Sword" "wield") (source "*Floor" "room" "*Sword")
                         "(*PlayerA has (som-known-gear-source ((:seq *Floor))))"])
        planned (answer state "som-regear-status" "(planned)")
        promoted (assert-in planned "*PlayerA"
                            ["(*PlayerA now-has (som-gear-state ((the som-regear-final-state of *Request))))"
                             "(*Prediction has (instance-of (Som-Regear-Request)) (som-regear-goal (*Goal))
                                               (som-regear-start ((the som-regear-final-state of *Request))))"])]
    (ask planned "(the som-gear-confirmed of (the som-regear-final-state of *Request))" "nil")
    (ask promoted "(the som-regear-status of *Prediction)" "(incomplete)")))

(deftest one-mob-cannot-be-defeated-twice-but-an-evidenced-loot-bundle-can-supply-two-pieces
  (let [state (scenario [(piece "*Sword" "wield") (piece "*Armor" "body")
                         "(*Goal now-has (som-gear-wanted ((:seq *Sword *Armor))))"
                         (source "*Sword-drop" "mobile" "*Sword" (mobile-model))
                         (source "*Armor-drop" "mobile" "*Armor" (mobile-model))
                         "(*PlayerA has (som-known-gear-source ((:seq *Sword-drop *Armor-drop))))"])
        bundled (inside state "*PlayerA"
                        "(*Sword-drop has (som-gear-source-yields ((:seq *Sword *Armor))))")]
    (answer state "som-regear-status" "(blocked)")
    (answer bundled "som-regear-status" "(planned)")
    (kinds bundled "((:seq defeat-loot equip equip))")
    (ask bundled "(the som-gear-defeated of (the som-regear-final-state of *Request))"
         "((:seq *Provider))")))

(deftest a-prerequisite-fight-cannot-consume-the-mob-needed-by-its-parent
  (let [state (scenario [(piece "*Sword" "wield") (piece "*Armor" "body")
                         "(*Goal now-has (som-gear-wanted ((:seq *Armor))))"
                         (source "*Sword-drop" "mobile" "*Sword" (mobile-model))
                         (source "*Armor-drop" "mobile" "*Armor" (mobile-model "*Sword"))
                         "(*PlayerA has (som-known-gear-source ((:seq *Sword-drop *Armor-drop))))"])]
    (answer state "som-regear-status" "(blocked)")
    (answer state "som-regear-strategy" "nil")))

(deftest any-explicitly-evidenced-piece-in-a-loot-bundle-can-serve-the-goal
  (let [state (scenario [(piece "*Sword" "wield") (piece "*Armor" "body")
                         "(*Goal now-has (som-gear-wanted ((:seq *Armor))))"
                         (source "*Bundle" "mobile" "*Sword"
                                 (str (mobile-model) " (som-gear-source-yields ((:seq *Sword *Armor)))"))
                         "(*PlayerA has (som-known-gear-source ((:seq *Bundle))))"])]
    (answer state "som-regear-status" "(planned)")
    (kinds state "((:seq defeat-loot equip))")
    (ask state "(the som-gear-equipped of (the som-regear-final-state of *Request))" "((:seq *Armor))")))
