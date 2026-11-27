(ns som.km.som-agent-goal-test
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [som.kb :as kb]
            [som.km.engine :as engine]
            [som.km.frame :as frame]
            [som.km.read :as read]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(def ^:private agent-dir
  "src/resources/som-component-library")

(def ^:private goal-file
  "src/resources/km-component-library/rkf-clib/components/core/Goal.km")

(def ^:private loaded
  (let [session (engine/session)]
    (kb/load-lib (:kb session) (:query session) agent-dir :silent true)))

(defn- term [text]
  (:value (read/read-term text)))

(defn- on
  [previous text]
  (engine/evaluate text {:kb (:kb previous) :query (:query previous)}))

(defn- frame-has
  [frame pairs]
  (str "(" frame " has "
       (str/join " "
                 (map (fn [[slot value]]
                        (str "(" slot " (" value "))"))
                      pairs))
       ")"))

(defn- emit
  [frame slot-map]
  (frame-has frame (remove (fn [[_ value]] (nil? value)) slot-map)))

(defn- project-from
  [start goal clock extras & {:keys [situation]}]
  (let [clock (merge {"som-clock-kind" (get goal "som-kind-in" "level")
                      "som-clock-target" (get goal "som-target-level")}
                     clock)
        steps (concat [(emit "*Goal" goal)
                       (emit "*Clock" clock)]
                      extras
                      ["(*View has (instance-of (Som-Goal-View))
                                 (som-goal (*Goal))
                                 (som-progress (*Clock)))"])
        steps (if situation
                (map #(str "(in-situation " situation " " % ")") steps)
                steps)]
    (reduce on start steps)))

(defn- project
  [goal clock extras]
  (project-from loaded goal clock extras))

(defn- q
  [state slot]
  (on state (str "(the " slot " of *View)")))

(defn- value-is
  [result expected]
  (is (empty? (:errors result)) (pr-str (:errors result)))
  (is (= (term expected) (:value result))))

(defn- value-nil
  [result]
  (is (empty? (:errors result)) (pr-str (:errors result)))
  (is (nil? (:value result))))

(def ^:private budgeted
  {"instance-of" "Som-Level-Goal"
   "som-target-level" "5"
   "som-risk-ceiling" "bold"
   "som-budget-minutes" "10"
   "som-score-every-in" "15"})

(def ^:private base-clock
  {"instance-of" "Som-Progress-Projection"
   "som-event" "view"
   "som-start-level" "1"
   "som-start-fraction" "0"
   "som-level" "1"
   "som-exp-to-level" "1000"
   "som-exp-span" "1000"
   "som-elapsed-minutes" "0"
   "som-score-count" "1"
   "som-prior-notch" "cautious"
   "som-cooldown-steps" "0"
   "som-saves" "1"
   "som-score-steps" "0"
   "som-areas-known" "t"})

(def ^:private pace-on-goal
  {"instance-of" "Som-Level-Goal"
   "som-target-level" "21"
   "som-risk-ceiling" "bold"
   "som-budget-minutes" "30"
   "som-score-every-in" "15"})

(def ^:private pace-on-clock
  (merge base-clock
         {"som-level" "17"
          "som-elapsed-minutes" "25"
          "som-score-count" "2"}))

(def ^:private behind-clock
  (merge base-clock
         {"som-elapsed-minutes" "5"
          "som-score-count" "2"}))

(def ^:private open-goal
  {"instance-of" "Som-Level-Goal"
   "som-target-level" "5"
   "som-risk-ceiling" "bold"
   "som-budget-minutes" "0"
   "som-score-every-in" "15"})

(defn- mobile
  [frame name-symbol extras]
  (emit frame (merge {"instance-of" "Som-Mobile-Reading"
                      "som-mobile-name" name-symbol}
                     extras)))

(defn- known
  [frame name category]
  (emit frame (merge {"instance-of" "Som-Known-Command"
                      "som-command-name" name}
                     (when category {"som-command-category" category}))))

(defn- learned
  [rows]
  (let [forms (mapv (fn [[frame name category]]
                      (known frame name category))
                    rows)
        command-seq (str "(:seq " (str/join " " (map first rows)) ")")]
    (conj forms (emit "*Global" {"som-known-command" command-seq}))))

(def ^:private travel-commands
  (learned [["*Cmd-north" "north" "movement"]
            ["*Cmd-recall" "recall" "movement"]
            ["*Cmd-where" "\"where\"" "\"information / communication\""]]))

(defn- expect-rule
  [state number]
  (value-is (q state "som-licensed-rule") (str "(" number ")")))

(defn- expect-attempts
  [state expected]
  (let [social (on state "(the som-allow-social of (the som-licensed-directive of *View))")
        attempts (on state "(the som-attempts of (the som-licensed-directive of *View))")]
    (value-is social "(no)")
    (value-is attempts expected)
    (doseq [word ["practice" "train" "eat" "drink" "follow" "group" "kick"
                  "cast" "backstab" "disarm" "rescue" "wimpy" "quit"
                  "delete" "murder" "steal" "password"]]
      (is (not (str/includes? (pr-str (:value attempts)) word)) word))))

(defn- expect-yield
  [state]
  (value-nil (q state "som-licensed-directive")))

(deftest som-agent-loads-the-component-library
  (is (empty? (:errors loaded)) (pr-str (:errors loaded)))
  (is (= [] (:lisp loaded)))
  (is (= #{"Som-Agentic-Player" "Som-Goal-View" "Som-Level-Directive"
           "Som-Level-Goal" "Som-Mobile-Reading" "Som-Progress-Projection"
           "som-goal" "som-licensed-directive" "som-progress" "som-reading"
           "Som-Alignment" "Som-Area" "Som-Area-Choice" "Som-Gain-Offer"
           "Som-Gear-Goal" "Som-Gear-Piece" "Som-Gear-Report"
           "Som-Command-Choice" "Som-Known-Command" "Som-Learned-Ability"
           "Som-Personality" "Som-Practice-Room" "Som-Practice-State"
           "Som-Social-Connection" "Som-Weapon-Skill" "som-known-area"
           "som-player-command" "Som-Explored-Room" "Som-Room-Exit"
           "Som-Route" "som-explored-exit" "som-player-room"
           "Som-Mobile" "Som-Mobile-Choice" "som-player-mobile"
           "Som-Gear-State" "Som-Gear-Projection" "Som-Gear-Source" "Som-Gear-Step" "Som-Regear-Task" "Som-Regear-Choice" "Som-Regear-Request" "som-player-gear-source" "som-player-gear-state"}
         (set (utils/elements (:value loaded)))))
  (value-is (on loaded "(the superclasses of Som-Agentic-Player)") "(Situation)")
  (value-is (on loaded "(the superclasses of Som-Level-Goal)") "(Thing)")
  (value-is (on loaded "(the superclasses of Som-Area)") "(Thing)")
  (value-is (on loaded "(the superclasses of Som-Personality)") "(Thing)")
  (value-is (on loaded "(the superclasses of Som-Explored-Room)") "(Thing)")
  (value-is (on loaded "(the superclasses of Som-Room-Exit)") "(Thing)")
  (value-is (on loaded "(the superclasses of Som-Route)") "(Thing)")
  (value-is (on loaded "(the fluent-status of som-target-level)") "(*Fluent)")
  (value-is (on loaded "(the fluent-status of som-goal-of)") "(*Fluent)")
  (value-is (on loaded "(the fluent-status of som-pace)") "(*Fluent)")
  (value-is (on loaded "(the fluent-status of som-bootstrap)") "(*Fluent)")
  (value-is (on loaded "(the fluent-status of som-explored)") "(*Fluent)")
  (value-is (on loaded "(the fluent-status of som-optimal-area)") "(*Fluent)")
  (value-is (on loaded "(the fluent-status of som-bearing)") "(*Fluent)")
  (value-is (on loaded "(the fluent-status of som-known-command)") "(*Fluent)")
  (value-is (on loaded "(the fluent-status of som-command-heading)") "(*Fluent)")
  (value-is (on loaded "(the fluent-status of som-command-goal)") "(*Fluent)")
  (value-is (on loaded "(the fluent-status of som-exploration-attempt)") "(*Fluent)")
  (value-is (on loaded "(the fluent-status of som-route-exits)") "(*Fluent)")
  (value-is (on loaded "(the fluent-status of som-requires-open)") "(*Fluent)")
  (value-is (on loaded "(the fluent-status of som-explored-room)") "(*Fluent)")
  (value-is (on loaded "(the fluent-status of som-place-name)") "(*Fluent)")
  (value-is (on loaded "(the inverse of som-progress)") "(som-progress-of)")
  (value-is (on loaded "(the inverse of som-goal)") "(som-goal-of)")
  (value-is (on loaded "(the inverse of som-reading)") "(som-reading-of)")
  (value-is (on loaded "(the inverse of som-licensed-directive)")
            "(som-licensed-directive-of)")
  (value-is (on loaded "(the inverse of som-area)") "(som-area-of)")
  (value-is (on loaded "(the inverse of som-known-command)") "(som-known-command-of)")
  (value-is (on loaded "(the inverse of som-room-exit)") "(som-room-exit-of)")
  (value-is (on loaded "(the inverse of som-explored-room)") "(som-explored-room-of)")
  (doseq [name ["Goal" "Event" "Entity" "Action" "Planning" "Intentional"
                "Command" "has-goal" "objective" "agent" "Agent-Role"
                "subevent" "next-event" "resulting-state"]]
    (is (not (frame/known-frame? (:kb loaded) (symbol name))) name))
  (let [created (on loaded "(a Som-Level-Goal)")
        classes (on created "(the instance-of of _Som-Level-Goal1)")]
    (is (empty? (:errors created)))
    (value-is classes "(Som-Level-Goal)")))

(deftest one-situation-per-agentic-player-keeps-its-own-answers
  (let [named (reduce on loaded
                      ["(*PlayerA has (instance-of (Som-Agentic-Player)))"
                       "(*PlayerB has (instance-of (Som-Agentic-Player)))"])
        both (-> named
                 (project-from budgeted behind-clock nil :situation "*PlayerA")
                 (project-from (assoc budgeted "som-target-level" "9"
                                      "som-budget-minutes" "0")
                               (merge behind-clock {"som-event" "score"})
                               nil
                               :situation "*PlayerB"))
        ask (fn [player frame slot]
              (on both (str "(in-situation " player " (the " slot " of " frame "))")))]
    (value-is (ask "*PlayerA" "*Goal" "som-target-level") "(5)")
    (value-is (ask "*PlayerB" "*Goal" "som-target-level") "(9)")
    (value-is (ask "*PlayerA" "*View" "som-pace") "(behind)")
    (value-is (ask "*PlayerB" "*View" "som-pace") "(open)")))

(deftest a-completed-bootstrap-stays-in-that-players-situation
  (let [named (reduce on loaded
                      ["(*PlayerA has (instance-of (Som-Agentic-Player)))"
                       "(*PlayerB has (instance-of (Som-Agentic-Player)))"])
        marked (on named
                   "(in-situation *PlayerA (*PlayerA has (som-bootstrap (t))))")
        ask (fn [player frame]
              (on marked (str "(in-situation " player
                              " (the som-bootstrap of " frame "))")))]
    (value-is (ask "*PlayerA" "*PlayerA") "(t)")
    (value-nil (ask "*PlayerB" "*PlayerA"))
    (value-nil (ask "*PlayerB" "*PlayerB"))))

(deftest the-component-text-does-not-use-refused-forms
  (let [files (->> (io/file agent-dir)
                   file-seq
                   (filter #(and (.isFile %) (str/ends-with? (.getName %) ".km"))))]
    (is (= 44 (count files)))
    (doseq [file files
            :let [text (slurp file)]]
      (is (not (str/includes? text "anonymous-instancep")) (.getName file))
      (is (not (str/includes? (str/lower-case text) "lambda")) (.getName file)))
    (let [view-text (slurp (io/file agent-dir "level/Som-Goal-View.km"))
          directive-text (slurp (io/file agent-dir "level/Som-Level-Directive.km"))]
      (is (str/includes? view-text "(the som-clock-stale of Self) = t"))
      (is (not (str/includes? view-text "(the som-clock-stale of Self) >")))
      (is (str/includes? directive-text "(the som-clock-stale of Self) = t"))
      (is (not (str/includes? directive-text "(the som-clock-stale of Self) >")))
      (doseq [word ["practice" "train" "eat" "drink" "follow" "group" "kick"
                    "cast" "backstab" "disarm" "rescue" "wimpy" "quit"
                    "delete" "murder" "steal" "password"]]
        (is (not (re-find (re-pattern (str "(?i)(?<![A-Za-z])" word "(?![A-Za-z])"))
                          directive-text))
            word)))))

(deftest a-level-goal-defaults-kind-and-cadence
  (let [stated (project budgeted base-clock nil)
        kind (on stated "(the som-kind of *Goal)")
        every (on stated "(the som-score-every of *Goal)")
        sentence (on stated "(the text-gen of *Goal)")
        overridden (project (assoc budgeted "som-score-every-in" "20") base-clock nil)
        cadence (on overridden "(the som-score-every of *Goal)")]
    (value-is kind "(level)")
    (value-is every "(15)")
    (is (empty? (:errors sentence)) (pr-str (:errors sentence)))
    (is (str/includes? (pr-str (:value sentence)) "5"))
    (is (str/includes? (pr-str (:value sentence)) "bold"))
    (value-is cadence "(20)")))

(deftest the-first-score-is-still-sampling
  (let [state (project budgeted
                       (merge base-clock
                              {"som-event" "score"
                               "som-first-score" "t"
                               "som-score-count" "1"
                               "som-score-steps" "0"
                               "som-elapsed-minutes" "0"})
                       nil)]
    (value-is (q state "som-fraction") "(0)")
    (value-is (q state "som-span-reading") "(first-reading-counted-as-width)")
    (value-is (q state "som-levels-earned") "(0)")
    (value-is (q state "som-pace") "(sampling)")
    (value-nil (q state "som-score-due"))))

(deftest a-fraction-of-three-fifths-matches-six-tenths
  (let [state (project budgeted
                       (merge base-clock
                              {"som-exp-to-level" "400"
                               "som-score-count" "2"})
                       nil)]
    (value-is (q state "som-fraction") "(3/5)")
    (value-is (on state "((the som-fraction of *View) = 0.6)") "(t)")
    (value-is (q state "som-span-reading") "(first-reading-counted-as-width)")))

(deftest a-mid-level-span-is-not-rewritten
  (let [opened (project budgeted
                        (merge base-clock
                               {"som-exp-to-level" "400"
                                "som-exp-span" "400"})
                        nil)
        spent (project budgeted
                       (merge base-clock
                              {"som-exp-to-level" "0"
                               "som-exp-span" "400"
                               "som-score-count" "2"})
                       nil)
        next-level (project budgeted
                            (merge base-clock
                                   {"som-level" "2"
                                    "som-exp-to-level" "500"
                                    "som-exp-span" "500"})
                            nil)]
    (value-is (q opened "som-fraction") "(0)")
    (value-is (q opened "som-span-reading") "(first-reading-counted-as-width)")
    (value-is (q spent "som-fraction") "(1)")
    (value-is (q spent "som-levels-earned") "(1)")
    (value-is (q spent "som-span-reading") "(first-reading-counted-as-width)")
    (value-is (q next-level "som-fraction") "(0)")
    (value-is (q next-level "som-span-reading") "(first-reading-counted-as-width)")))

(deftest a-zero-span-does-not-divide
  (let [state (project budgeted
                       (merge base-clock {"som-exp-span" "0"
                                          "som-exp-to-level" "0"})
                       nil)]
    (value-nil (q state "som-fraction"))
    (value-nil (q state "som-span-reading"))))

(deftest met-is-the-target-or-the-stored-flag
  (let [reached (project budgeted (merge base-clock {"som-level" "5"}) nil)
        stored (project budgeted
                        (merge base-clock {"som-level" "4" "som-met-in" "t"})
                        nil)
        short (project budgeted (merge base-clock {"som-level" "4"}) nil)]
    (value-is (q reached "som-met") "(t)")
    (value-is (q stored "som-met") "(t)")
    (value-nil (q short "som-met"))))

(deftest pace-behind-raises-one-step-and-stops-at-the-ceiling
  (let [cautious (project budgeted
                          (merge behind-clock
                                 {"som-event" "score"
                                  "som-prior-notch" "cautious"
                                  "som-cooldown-steps" "0"})
                          nil)
        steady (project budgeted
                        (merge behind-clock
                               {"som-event" "score"
                                "som-prior-notch" "steady"
                                "som-cooldown-steps" "0"})
                        nil)
        bold (project budgeted
                      (merge behind-clock
                             {"som-event" "score"
                              "som-prior-notch" "bold"
                              "som-cooldown-steps" "0"})
                      nil)]
    (value-is (q cautious "som-pace") "(behind)")
    (value-is (q cautious "som-notch") "(steady)")
    (value-is (q cautious "som-notch-moved") "(raised)")
    (value-is (q steady "som-notch") "(bold)")
    (value-is (q steady "som-notch-moved") "(raised)")
    (value-is (q bold "som-notch") "(bold)")
    (value-is (q bold "som-notch-moved") "(unchanged)")))

(deftest pace-boundaries-are-on
  (let [behind-edge (project pace-on-goal pace-on-clock nil)
        ahead-edge (project (assoc pace-on-goal "som-target-level" "29")
                            (merge pace-on-clock {"som-level" "25"})
                            nil)]
    (value-is (q behind-edge "som-pace") "(on)")
    (value-is (q ahead-edge "som-pace") "(on)")))

(deftest pace-ahead-drops-one-step
  (let [clock (merge base-clock
                     {"som-event" "score"
                      "som-level" "4"
                      "som-elapsed-minutes" "5"
                      "som-score-count" "2"
                      "som-cooldown-steps" "0"})
        steady (project budgeted (assoc clock "som-prior-notch" "steady") nil)
        cautious (project budgeted (assoc clock "som-prior-notch" "cautious") nil)
        bold (project budgeted (assoc clock "som-prior-notch" "bold") nil)]
    (value-is (q steady "som-pace") "(ahead)")
    (value-is (q steady "som-notch") "(cautious)")
    (value-is (q steady "som-notch-moved") "(dropped)")
    (value-is (q cautious "som-notch") "(cautious)")
    (value-is (q cautious "som-notch-moved") "(unchanged)")
    (value-is (q bold "som-notch") "(steady)")
    (value-is (q bold "som-notch-moved") "(dropped)")))

(deftest a-death-lands-on-cautious-and-starts-the-cooldown
  (let [steady (project budgeted
                        (merge base-clock
                               {"som-event" "death"
                                "som-prior-notch" "steady"})
                        nil)
        cooled (project budgeted
                        (merge behind-clock
                               {"som-event" "score"
                                "som-prior-notch" "cautious"
                                "som-cooldown-steps" "30"})
                        nil)
        from-bold (project budgeted
                           (merge base-clock
                                  {"som-event" "death"
                                   "som-prior-notch" "bold"})
                           nil)
        from-cautious (project budgeted
                               (merge base-clock
                                      {"som-event" "death"
                                       "som-prior-notch" "cautious"})
                               nil)]
    (value-is (q steady "som-notch") "(cautious)")
    (value-is (q steady "som-cooldown-next") "(30)")
    (value-is (q steady "som-notch-moved") "(dropped)")
    (value-is (q cooled "som-pace") "(behind)")
    (value-is (q cooled "som-notch") "(cautious)")
    (value-is (q cooled "som-notch-moved") "(unchanged)")
    (value-is (q from-bold "som-notch") "(cautious)")
    (value-is (q from-bold "som-cooldown-next") "(30)")
    (value-is (q from-cautious "som-notch") "(cautious)")
    (value-is (q from-cautious "som-cooldown-next") "(30)")))

(deftest an-open-budget-sets-the-ceiling-once
  (let [goal (assoc open-goal "som-risk-ceiling" "steady")
        first-score (project goal
                             (merge base-clock
                                    {"som-event" "score"
                                     "som-first-score" "t"
                                     "som-prior-notch" "cautious"})
                             nil)
        later (project goal
                       (merge behind-clock
                              {"som-event" "score"
                               "som-prior-notch" "steady"})
                       nil)
        died (project goal
                      (merge base-clock
                             {"som-event" "death"
                              "som-prior-notch" "steady"})
                      nil)
        after (project goal
                       (merge base-clock
                              {"som-event" "score"
                               "som-prior-notch" "cautious"})
                       nil)]
    (value-is (q first-score "som-pace") "(open)")
    (value-is (q first-score "som-notch") "(steady)")
    (value-is (q first-score "som-notch-moved") "(ceiling)")
    (value-is (q later "som-pace") "(open)")
    (value-is (q later "som-notch") "(steady)")
    (value-is (q later "som-notch-moved") "(unchanged)")
    (value-is (q died "som-notch") "(cautious)")
    (value-is (q died "som-cooldown-next") "(30)")
    (value-is (q after "som-pace") "(open)")
    (value-is (q after "som-notch") "(cautious)")
    (value-is (q after "som-notch-moved") "(unchanged)")))

(deftest omitted-minutes-and-asserted-zero-are-open
  (let [omitted (project (dissoc budgeted "som-budget-minutes")
                         (merge behind-clock {"som-event" "score"})
                         nil)
        asserted (project (assoc budgeted "som-budget-minutes" "0")
                          (merge behind-clock {"som-event" "score"})
                          nil)]
    (value-is (q omitted "som-pace") "(open)")
    (value-is (q asserted "som-pace") "(open)")))

(deftest a-used-up-unmet-budget-is-behind-without-a-quotient
  (let [missed (project budgeted
                        (merge base-clock
                               {"som-event" "score"
                                "som-elapsed-minutes" "10"
                                "som-score-count" "2"
                                "som-prior-notch" "cautious"
                                "som-cooldown-steps" "0"})
                        nil)
        held (project budgeted
                      (merge base-clock
                             {"som-event" "view"
                              "som-elapsed-minutes" "10"
                              "som-deadline-in" "t"
                              "som-prior-notch" "bold"})
                      nil)
        met (project budgeted
                     (merge base-clock
                            {"som-level" "5"
                             "som-elapsed-minutes" "10"})
                     nil)]
    (value-is (q missed "som-deadline-missed") "(t)")
    (value-is (q missed "som-pace") "(behind)")
    (value-nil (q missed "som-pace-withheld"))
    (value-is (q missed "som-notch") "(bold)")
    (value-is (q missed "som-notch-moved") "(ceiling)")
    (value-is (q held "som-notch") "(bold)")
    (value-is (q held "som-notch-moved") "(unchanged)")
    (value-is (q met "som-met") "(t)")
    (value-nil (q met "som-deadline-missed"))
    (value-nil (q met "som-pace"))
    (value-nil (q met "som-pace-withheld"))))

(deftest a-score-page-replaces-an-experience-estimate
  (let [estimated (project budgeted
                           (merge base-clock {"som-exp-estimate" "900"})
                           nil)
        replaced (project budgeted
                          (merge base-clock
                                 {"som-exp-estimate" "900"
                                  "som-score-page-exp" "400"})
                          nil)]
    (value-is (q estimated "som-exp-used") "(900)")
    (value-nil (q estimated "som-estimate-overwritten"))
    (value-is (q replaced "som-exp-used") "(400)")
    (value-is (q replaced "som-estimate-overwritten") "(t)")
    (value-is (q replaced "som-fraction") "(3/5)")))

(deftest a-restored-clock-with-a-different-target-is-stale
  (let [stale (project budgeted
                       (merge base-clock
                              {"som-clock-target" "4"
                               "som-fighting" "t"
                               "som-reading" "(:seq *Goblin)"})
                       [(mobile "*Goblin" "goblin"
                                {"som-outlook" "safe" "som-fresh" "t"})])
        fresh (project budgeted behind-clock nil)]
    (value-is (q stale "som-clock-stale") "(t)")
    (value-nil (q stale "som-pace"))
    (value-nil (q stale "som-notch"))
    (value-nil (q stale "som-met"))
    (value-nil (q stale "som-score-due"))
    (value-nil (q stale "som-licensed-rule"))
    (expect-yield stale)
    (value-is (q fresh "som-pace") "(behind)")))

(deftest score-due-and-checkpoint-due-follow-the-counters
  (let [due (project budgeted
                     (merge base-clock
                            {"som-score-count" "1"
                             "som-score-steps" "15"})
                     nil)
        early (project budgeted
                       (merge base-clock
                              {"som-score-count" "1"
                               "som-score-steps" "14"})
                       nil)
        forced (project budgeted
                        (merge base-clock
                               {"som-score-count" "1"
                                "som-score-steps" "14"
                                "som-score-forced" "t"})
                        nil)
        none (project budgeted
                      (merge base-clock
                             {"som-score-count" "0"
                              "som-score-steps" "0"})
                      nil)
        folded (project budgeted
                        (merge base-clock
                               {"som-score-count" "2"
                                "som-score-steps" "0"})
                        nil)
        save (project budgeted (merge base-clock {"som-saves" "0"}) nil)
        saved (project budgeted (merge base-clock {"som-saves" "1"}) nil)
        stale (project budgeted
                      (merge base-clock
                             {"som-clock-target" "4"
                              "som-score-count" "0"
                              "som-saves" "0"})
                      nil)]
    (value-is (q due "som-score-due") "(t)")
    (value-nil (q early "som-score-due"))
    (value-is (q forced "som-score-due") "(t)")
    (value-is (q none "som-score-due") "(t)")
    (value-nil (q folded "som-score-due"))
    (value-is (q save "som-checkpoint-due") "(t)")
    (value-nil (q saved "som-checkpoint-due"))
    (value-nil (q stale "som-score-due"))
    (value-nil (q stale "som-checkpoint-due"))))

(deftest the-directive-licenses-the-first-matching-rule
  (testing "met with an empty gear gate yields"
    (let [state (project budgeted
                         (merge base-clock {"som-level" "5"})
                         nil)]
      (expect-rule state 1)
      (expect-yield state)))
  (testing "a gear gate falls through to the fresh mobile"
    (let [state (project budgeted
                         (merge base-clock
                                {"som-level" "5"
                                 "som-elapsed-minutes" "1"
                                 "som-gear-gate" "9"
                                 "som-reading" "(:seq *Goblin)"})
                         [(mobile "*Goblin" "goblin"
                                  {"som-outlook" "safe" "som-fresh" "t"})])]
      (expect-rule state 9)
      (expect-attempts state
                       "((:args engage combat kill goblin))")))
  (testing "a due score is rule 2"
    (let [state (project budgeted
                         (merge base-clock
                                {"som-score-steps" "15"})
                         nil)]
      (expect-rule state 2)
      (expect-attempts state
                       "((:args survey \"information / communication\" score \"\"))")))
  (testing "unknown areas after a score are rule 3"
    (let [state (project budgeted
                         (merge base-clock
                                {"som-score-count" "2"
                                 "som-areas-known" nil})
                         nil)]
      (expect-rule state 3)
      (expect-attempts state
                       "((:seq (:args survey \"information / communication\" areas \"\") (:args survey \"information / communication\" where \"\")))")))
  (testing "cautious and on recalls, and behind takes the exit"
    (let [recall (project pace-on-goal
                          (merge pace-on-clock
                                 {"som-untried-exits" "(:seq north)"})
                          travel-commands)
          travel (project budgeted
                          (merge behind-clock
                                 {"som-untried-exits" "(:seq north)"})
                          travel-commands)]
      (expect-rule recall 12)
      (expect-attempts recall
                       "((:seq (:args travel movement recall \"\") (:args survey \"information / communication\" where \"\")))")
      (expect-rule travel 10)
      (expect-attempts travel
                       "((:seq (:args travel movement north \"\")))")))
  (testing "a used-up unmet budget lets cautious take the exit"
    (let [state (project (assoc budgeted "som-risk-ceiling" "cautious")
                         (merge base-clock
                                {"som-elapsed-minutes" "10"
                                 "som-score-count" "2"
                                 "som-prior-notch" "cautious"
                                 "som-untried-exits" "(:seq north)"})
                         travel-commands)]
      (value-is (q state "som-pace") "(behind)")
      (expect-rule state 10)
      (expect-attempts state
                       "((:seq (:args travel movement north \"\")))")))
  (testing "steady takes the only exit"
    (let [state (project open-goal
                         (merge base-clock
                                {"som-prior-notch" "steady"
                                 "som-untried-exits" "(:seq north)"})
                         travel-commands)]
      (expect-rule state 10)
      (expect-attempts state
                       "((:seq (:args travel movement north \"\")))")))
  (testing "a repop room on pace holds, and a stale room looks"
    (let [held (project pace-on-goal
                        (assoc pace-on-clock "som-repop-room" "t")
                        nil)
          looked (project pace-on-goal
                          (merge pace-on-clock
                                 {"som-repop-room" "t"
                                  "som-room-stale" "t"})
                          nil)
          role (on held "(the som-directive-role of (the som-licensed-directive of *View))")]
      (expect-rule held 11)
      (expect-attempts held "((:seq))")
      (value-is role "(hold)")
      (expect-rule looked 11)
      (expect-attempts looked "((:args survey objects look \"\"))")))
  (testing "a missed health line flees, rests, or stands"
    (let [flee (project open-goal
                        (merge base-clock
                               {"som-fighting" "t"
                                "som-hit" "50"
                                "som-max-hit" "100"})
                        nil)
          rest (project open-goal
                        (merge base-clock
                               {"som-hit" "50"
                                "som-max-hit" "100"})
                        nil)
          stand (project open-goal
                         (merge base-clock
                                {"som-hit" "100"
                                 "som-max-hit" "100"
                                 "som-position" "resting"})
                         nil)]
      (expect-rule flee 4)
      (expect-attempts flee "((:args escape combat flee \"\"))")
      (expect-rule rest 7)
      (expect-attempts rest "((:args recover movement rest \"\"))")
      (expect-rule stand 7)
      (expect-attempts stand "((:args recover movement stand \"\"))")))
  (testing "fighting without a missed line and without a mobile yields"
    (let [healthy (project open-goal
                           (merge base-clock
                                  {"som-fighting" "t"
                                   "som-hit" "100"
                                   "som-max-hit" "100"})
                           nil)
          no-max (project open-goal
                          (merge base-clock
                                 {"som-fighting" "t"
                                  "som-prior-notch" "bold"
                                  "som-hit" "20"
                                  "som-flee-floor" "20"})
                          nil)]
      (expect-rule healthy 14)
      (expect-yield healthy)
      (expect-rule no-max 14)
      (expect-yield no-max)))
  (testing "a mobile with no consider is a survey, including a player ahead of a goblin"
    (let [one (project open-goal
                       (merge base-clock
                              {"som-fighting" "t"
                               "som-hit" "100"
                               "som-max-hit" "100"
                               "som-reading" "(:seq *Wolf)"})
                       [(mobile "*Wolf" "wolf" {})])
          both (project open-goal
                        (merge base-clock
                               {"som-reading" "(:seq *Player *Goblin)"})
                        [(mobile "*Player" "player" {"som-player" "t"})
                         (mobile "*Goblin" "goblin"
                                 {"som-outlook" "safe" "som-fresh" "t"})])]
      (expect-rule one 8)
      (expect-attempts one
                       "((:args survey \"information / communication\" consider wolf))")
      (expect-rule both 8)
      (expect-attempts both
                       "((:args survey \"information / communication\" consider player))")))
  (testing "two fresh mobiles keep projection order"
    (let [state (project open-goal
                         (merge base-clock
                                {"som-reading" "(:seq *Alpha *Beta)"})
                         [(mobile "*Alpha" "alpha"
                                  {"som-outlook" "safe" "som-fresh" "t"})
                          (mobile "*Beta" "beta"
                                  {"som-outlook" "safe" "som-fresh" "t"})])]
      (expect-rule state 9)
      (expect-attempts state "((:args engage combat kill alpha))")))
  (testing "checkpoint due saves once, then the idle view yields"
    (let [due (project pace-on-goal
                       (assoc pace-on-clock "som-saves" "0")
                       nil)
          done (project pace-on-goal pace-on-clock nil)]
      (expect-rule due 13)
      (expect-attempts due "((:args checkpoint other save \"\"))")
      (expect-rule done 14)
      (expect-yield done))))

(deftest loading-core-goal-does-not-change-the-som-answer
  (let [with-goal (on loaded (str "(load-kb \"" goal-file "\")"))
        parents (on with-goal "(the superclasses of Goal)")
        som-parents (on with-goal "(the superclasses of Som-Level-Goal)")
        behind (project-from with-goal budgeted behind-clock nil)]
    (is (empty? (:errors with-goal)) (pr-str (:errors with-goal)))
    (value-is parents "(Event)")
    (value-is som-parents "(Thing)")
    (is (not (frame/known-frame? (:kb with-goal) (symbol "text-indef-determiner"))))
    (value-is (q behind "som-pace") "(behind)")))

(defn- area
  [frame low high explored]
  (emit frame (merge {"instance-of" "Som-Area"
                      "som-area-name" (str "\"" (subs frame 1) "\"")
                      "som-level-low" (str low)
                      "som-level-high" (str high)}
                     (when explored {"som-explored" "t"}))))

(deftest an-explored-area-inside-the-level-range-is-optimal
  (let [ranked (project open-goal
                        (merge base-clock
                               {"som-level" "6"
                                "som-area" "(:seq *Grove *Warren *Crypt *Pit)"})
                        [(area "*Grove" 1 10 true)
                         (area "*Warren" 5 8 true)
                         (area "*Crypt" 10 20 true)
                         (area "*Pit" 6 7 false)])
        tied (project open-goal
                      (merge base-clock
                             {"som-level" "6"
                              "som-area" "(:seq *First *Second)"})
                      [(area "*First" 5 8 true)
                       (area "*Second" 5 8 true)])
        tighter (project open-goal
                         (merge base-clock
                                {"som-level" "6"
                                 "som-area" "(:seq *Wide *Tight)"})
                         [(area "*Wide" 5 15 true)
                          (area "*Tight" 5 8 true)])
        open-bound (project open-goal
                            (merge base-clock
                                   {"som-level" "6"
                                    "som-area" "(:seq *Open *Grove)"})
                            [(emit "*Open" {"instance-of" "Som-Area"
                                            "som-area-name" "\"Open\""
                                            "som-level-low" "1"
                                            "som-explored" "t"})
                             (area "*Grove" 1 10 true)])
        none (project open-goal base-clock nil)
        too-high (project open-goal
                          (merge base-clock
                                 {"som-level" "6"
                                  "som-area" "(:seq *Crypt)"})
                          [(area "*Crypt" 10 20 true)])]
    (value-is (q ranked "som-explored-area") "((:seq *Grove *Warren *Crypt))")
    (value-is (q ranked "som-fitting-area") "((:seq *Grove *Warren))")
    (value-is (q ranked "som-optimal-area") "(*Warren)")
    (value-is (q tied "som-optimal-area") "(*First)")
    (value-is (q tighter "som-optimal-area") "(*Tight)")
    (value-is (q open-bound "som-optimal-area") "(*Grove)")
    (value-nil (q none "som-optimal-area"))
    (value-nil (q none "som-explored-area"))
    (value-nil (q too-high "som-optimal-area"))
    (value-is (q too-high "som-explored-area") "((:seq *Crypt))")))

(deftest an-explored-area-stays-in-that-players-situation
  (let [clock (merge base-clock
                     {"som-level" "1"
                      "som-area" "(:seq *Grove *City)"})
        named (reduce on loaded
                      ["(*PlayerA has (instance-of (Som-Agentic-Player)))"
                       "(*PlayerB has (instance-of (Som-Agentic-Player)))"])
        both (-> named
                 (project-from open-goal clock
                               [(area "*Grove" 1 5 true)
                                (area "*City" 1 5 false)]
                               :situation "*PlayerA")
                 (project-from open-goal clock
                               [(area "*Grove" 1 5 false)
                                (area "*City" 1 5 true)]
                               :situation "*PlayerB"))
        ask (fn [player expr]
              (on both (str "(in-situation " player " " expr ")")))]
    (value-is (ask "*PlayerA" "(the som-optimal-area of *View)") "(*Grove)")
    (value-is (ask "*PlayerB" "(the som-optimal-area of *View)") "(*City)")
    (value-is (ask "*PlayerA" "(the som-explored of *Grove)") "(t)")
    (value-nil (ask "*PlayerB" "(the som-explored of *Grove)"))))

(deftest known-commands-serve-the-asked-goal
  (let [rows [["*Cmd-score" "score" nil]
              ["*Cmd-kill" "kill" "movement"]
              ["*Cmd-where" "\"where\"" nil]
              ["*Cmd-password" "password" nil]
              ["*Cmd-save" "save" nil]
              ["*Cmd-quit" "quit" nil]
              ["*Cmd-north" "north" nil]
              ["*Cmd-bang" "\"!\"" nil]
              ["*Cmd-xyzzy" "xyzzy" nil]]
        base (project open-goal base-clock (learned rows))
        ask (fn [goal]
              (q (on base (str "(*View has (som-command-goal (" goal ")))"))
                 "som-command-for-goal"))]
    (value-is (on base "(the som-command-heading of *Cmd-north)") "(movement)")
    (value-is (on base "(the som-command-heading of *Cmd-kill)") "(movement)")
    (value-is (on base "(the som-command-heading of *Cmd-where)")
              "(\"information / communication\")")
    (value-is (on base "(the som-command-heading of *Cmd-bang)") "(other)")
    (value-nil (on base "(the som-command-heading of *Cmd-xyzzy)"))
    (value-nil (on base "(the som-command-allowed of *Cmd-quit)"))
    (value-is (ask "survey") "((:seq *Cmd-score *Cmd-where))")
    (value-is (ask "explore") "((:seq *Cmd-kill *Cmd-north))")
    (value-is (ask "engage") "((:seq))")
    (value-is (ask "checkpoint") "((:seq *Cmd-save))")
    (value-is (ask "look") "((:seq))")))

(deftest exploration-follows-the-known-commands
  (let [misfiled (project open-goal
                          (merge base-clock
                                 {"som-prior-notch" "steady"
                                  "som-untried-exits" "(:seq north east)"})
                          (learned [["*Cmd-north" "north" "combat"]
                                    ["*Cmd-east" "east" nil]]))
        nowhere (project open-goal
                         (merge base-clock
                                {"som-prior-notch" "steady"
                                 "som-untried-exits" "(:seq north)"})
                         nil)
        located (project pace-on-goal
                         (merge pace-on-clock
                                {"som-untried-exits" "(:seq north)"})
                         (learned [["*Cmd-where" "\"where\"" nil]]))
        ranked (project (assoc open-goal "som-target-level" "21")
                        (merge base-clock
                               {"som-level" "6"
                                "som-prior-notch" "steady"
                                "som-untried-exits" "(:seq north)"
                                "som-area" "(:seq *Grove *Warren)"})
                        (into (learned [["*Cmd-north" "north" nil]])
                              [(area "*Grove" 1 10 true)
                               (area "*Warren" 5 8 true)]))]
    (expect-rule misfiled 10)
    (expect-attempts misfiled "((:seq (:args travel movement east \"\")))")
    (expect-rule nowhere 10)
    (expect-attempts nowhere "((:seq))")
    (expect-rule located 12)
    (expect-attempts located
                     "((:args survey \"information / communication\" where \"\"))")
    (value-is (q ranked "som-optimal-area") "(*Warren)")
    (expect-rule ranked 10)
    (expect-attempts ranked "((:seq (:args travel movement north \"\")))")))

(deftest a-players-commands-stay-in-that-situation
  (let [teach (fn [state player rows]
                (reduce on state
                        (let [forms (mapv (fn [[frame name category]]
                                            (str "(in-situation " player " "
                                                 (known frame name category) ")"))
                                          rows)
                              command-seq (str "(:seq " (str/join " " (map first rows)) ")")]
                          (conj forms
                                (str "(in-situation " player " (" player
                                     " has (som-known-command (" command-seq "))))")))))
        named (reduce on loaded
                      ["(*PlayerA has (instance-of (Som-Agentic-Player)))"
                       "(*PlayerB has (instance-of (Som-Agentic-Player)))"])
        taught (-> named
                   (teach "*PlayerA" [["*Cmd-north" "north" "movement"]
                                      ["*Cmd-score" "score" nil]])
                   (teach "*PlayerB" [["*Cmd-north" "north" "combat"]
                                      ["*Cmd-east" "east" "movement"]]))
        clock (merge base-clock
                     {"som-prior-notch" "steady"
                      "som-untried-exits" "(:seq north east)"})
        both (-> taught
                 (project-from open-goal clock
                               ["(*View has (som-command-goal (explore)))"]
                               :situation "*PlayerA")
                 (project-from open-goal clock
                               ["(*View has (som-command-goal (explore)))"]
                               :situation "*PlayerB"))
        ask (fn [player expr]
              (on both (str "(in-situation " player " " expr ")")))]
    (value-is (ask "*PlayerA" "(the som-known-command of *PlayerA)")
              "((:seq *Cmd-north *Cmd-score))")
    (value-nil (ask "*PlayerB" "(the som-known-command of *PlayerA)"))
    (value-is (ask "*PlayerA" "(the som-command-for-goal of *View)")
              "((:seq *Cmd-north))")
    (value-is (ask "*PlayerB" "(the som-command-for-goal of *View)")
              "((:seq *Cmd-east))")
    (value-is (ask "*PlayerA" "(the som-attempts of (the som-licensed-directive of *View))")
              "((:seq (:args travel movement north \"\")))")
    (value-is (ask "*PlayerB" "(the som-attempts of (the som-licensed-directive of *View))")
              "((:seq (:args travel movement east \"\")))")
    (value-nil (ask "*PlayerB" "(the som-command-category of *Cmd-score)"))))

(deftest a-second-scenario-does-not-see-the-first-clock
  (let [first-scenario (project budgeted base-clock nil)
        second (on loaded "(the som-level of *Clock)")]
    (is (frame/known-frame? (:kb first-scenario) (symbol "*Clock")))
    (is (not (frame/known-frame? (:kb loaded) (symbol "*Clock"))))
    (value-nil second)))

(defn- explored-room
  [frame]
  (emit frame {"instance-of" "Som-Explored-Room"
               "som-place-name" (str "\"" (subs frame 1) "\"")}))

(defn- room-exit
  [frame direction destination open? unlock?]
  (emit frame (merge {"instance-of" "Som-Room-Exit"
                      "som-exit-direction" direction}
                     (when destination {"som-exit-to" destination})
                     (when open? {"som-requires-open" "t"})
                     (when unlock? {"som-requires-unlock" "t"}))))

(defn- route-between
  [frame from to]
  (emit frame {"instance-of" "Som-Route"
               "som-route-from" from
               "som-route-to" to}))

(defn- assert-in
  [state player forms]
  (reduce on state (map #(str "(in-situation " player " " % ")") forms)))

(defn- ask-in
  [state player expr]
  (on state (str "(in-situation " player " " expr ")")))

(deftest exits-to-a-destination-follow-the-listed-order
  (let [rooms ["*Temple" "*Closet" "*Square" "*Shop" "*Alley" "*Hall" "*Vault"
               "*Nowhere"]
        exits [(room-exit "*Blank" "north" nil false false)
               (room-exit "*North-closet" "north" "*Closet" false false)
               (room-exit "*East-square" "east" "*Square" false false)
               (room-exit "*West-temple" "west" "*Temple" false false)
               (room-exit "*North-shop" "north" "*Shop" false false)
               (room-exit "*East-alley" "east" "*Alley" true true)
               (room-exit "*South-square" "south" "*Square" false false)
               (room-exit "*East-vault" "east" "*Vault" true false)]
        links [(emit "*Temple" {"som-room-exit" "(:seq *Blank *North-closet *East-square)"})
               (emit "*Square" {"som-room-exit" "(:seq *West-temple *North-shop *East-alley)"})
               (emit "*Shop" {"som-room-exit" "(:seq *South-square)"})
               (emit "*Hall" {"som-room-exit" "(:seq *East-vault)"})
               (emit "*PlayerA" {"som-explored-room"
                                 (str "(:seq " (str/join " " rooms) ")")})
               (route-between "*To-shop" "*Temple" "*Shop")
               (route-between "*To-alley" "*Temple" "*Alley")
               (route-between "*To-here" "*Temple" "*Temple")
               (route-between "*To-none" "*Temple" "*Nowhere")
               (route-between "*To-vault" "*Hall" "*Vault")]
        named (on loaded "(*PlayerA has (instance-of (Som-Agentic-Player)))")
        mapped (assert-in named "*PlayerA"
                          (concat (map explored-room rooms) exits links))
        ask (fn [expr] (ask-in mapped "*PlayerA" expr))
        opened (ask "(the som-route-exits of *To-none)")
        joined (assert-in opened "*PlayerA"
                          [(room-exit "*East-nowhere" "east" "*Nowhere" false false)
                           "(*Temple now-has (som-room-exit ((:seq *Blank *North-closet *East-square *East-nowhere))))"
                           (route-between "*To-later" "*Temple" "*Nowhere")])
        again (fn [expr] (ask-in joined "*PlayerA" expr))]
    (value-is (ask "(the som-place-name of *Temple)") "(\"Temple\")")
    (value-is (ask "(the som-route-exits of *To-shop)")
              "((:seq *East-square *North-shop))")
    (value-is (ask "(the som-route-exits of *To-alley)")
              "((:seq *East-square *East-alley))")
    (value-is (ask "(the som-requires-open of *East-alley)") "(t)")
    (value-is (ask "(the som-requires-unlock of *East-alley)") "(t)")
    (value-is (ask "(the som-route-exits of *To-vault)") "((:seq *East-vault))")
    (value-is (ask "(the som-requires-open of *East-vault)") "(t)")
    (value-nil (ask "(the som-requires-unlock of *East-vault)"))
    (value-nil (ask "(the som-requires-open of *East-square)"))
    (value-is (ask "(the som-route-exits of *To-here)") "((:seq))")
    (value-nil opened)
    (is (empty? (:errors joined)) (pr-str (:errors joined)))
    (value-is (again "(the som-room-exit of *Temple)")
              "((:seq *Blank *North-closet *East-square *East-nowhere))")
    (value-is (again "(the som-route-exits of *To-later)") "((:seq *East-nowhere))")))

(deftest a-players-rooms-stay-in-that-situation
  (let [named (reduce on loaded
                      ["(*PlayerA has (instance-of (Som-Agentic-Player)))"
                       "(*PlayerB has (instance-of (Som-Agentic-Player)))"])
        facts [(explored-room "*Temple")
               (explored-room "*Square")
               (explored-room "*Shop")
               (room-exit "*East-square" "east" "*Square" false false)
               (room-exit "*North-shop" "north" "*Shop" false false)
               (route-between "*To-square" "*Temple" "*Square")]
        placed (-> named
                   (assert-in "*PlayerA"
                              (conj facts
                                    (emit "*Temple" {"som-room-exit" "(:seq *East-square)"})
                                    (emit "*PlayerA" {"som-explored-room" "(:seq *Temple *Square)"})))
                   (assert-in "*PlayerB"
                              (conj facts
                                    (emit "*Temple" {"som-room-exit" "(:seq *North-shop)"})
                                    (emit "*PlayerB" {"som-explored-room" "(:seq *Temple *Shop)"}))))
        ask (fn [player expr] (ask-in placed player expr))]
    (value-is (ask "*PlayerA" "(the som-route-exits of *To-square)")
              "((:seq *East-square))")
    (value-nil (ask "*PlayerB" "(the som-route-exits of *To-square)"))
    (value-is (ask "*PlayerA" "(the som-room-exit of *Temple)") "((:seq *East-square))")
    (value-is (ask "*PlayerB" "(the som-room-exit of *Temple)") "((:seq *North-shop))")
    (value-is (ask "*PlayerA" "(the som-explored-room of *PlayerA)")
              "((:seq *Temple *Square))")
    (value-nil (ask "*PlayerB" "(the som-explored-room of *PlayerA)"))
    (value-is (ask "*PlayerB" "(the som-explored-room of *PlayerB)")
              "((:seq *Temple *Shop))")
    (value-nil (ask "*PlayerA" "(the som-explored-room of *PlayerB)"))))
