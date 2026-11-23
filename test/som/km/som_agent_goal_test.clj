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
  [start goal clock extras]
  (let [clock (merge {"som-clock-kind" (get goal "som-kind-in" "level")
                      "som-clock-target" (get goal "som-target-level")}
                     clock)
        steps (concat [(emit "*Goal" goal)
                       (emit "*Clock" clock)]
                      extras
                      ["(*View has (instance-of (Som-Goal-View))
                                 (som-goal (*Goal))
                                 (som-progress (*Clock)))"])]
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

(deftest som-agent-loads-nine-components-and-leaves-the-core-files-out
  (is (empty? (:errors loaded)) (pr-str (:errors loaded)))
  (is (= [] (:lisp loaded)))
  (is (= #{"Som-Goal-View" "Som-Level-Directive" "Som-Level-Goal"
           "Som-Mobile-Reading" "Som-Progress-Projection"
           "som-goal" "som-licensed-directive" "som-progress" "som-reading"}
         (set (utils/elements (:value loaded)))))
  (value-is (on loaded "(the superclasses of Som-Level-Goal)") "(Thing)")
  (value-is (on loaded "(the inverse of som-progress)") "(som-progress-of)")
  (value-is (on loaded "(the inverse of som-goal)") "(som-goal-of)")
  (value-is (on loaded "(the inverse of som-reading)") "(som-reading-of)")
  (value-is (on loaded "(the inverse of som-licensed-directive)")
            "(som-licensed-directive-of)")
  (doseq [name ["Goal" "Event" "Entity" "Action" "Planning" "Intentional"
                "Command" "has-goal" "objective" "agent" "Agent-Role"
                "subevent" "next-event" "resulting-state"]]
    (is (not (frame/known-frame? (:kb loaded) (symbol name))) name))
  (let [created (on loaded "(a Som-Level-Goal)")
        classes (on created "(the instance-of of _Som-Level-Goal1)")]
    (is (empty? (:errors created)))
    (value-is classes "(Som-Level-Goal)")))

(deftest the-component-text-does-not-use-refused-forms
  (let [files (->> (io/file agent-dir)
                   file-seq
                   (filter #(and (.isFile %) (str/ends-with? (.getName %) ".km"))))]
    (is (= 9 (count files)))
    (doseq [file files
            :let [text (slurp file)]]
      (is (not (str/includes? text "anonymous-instancep")) (.getName file))
      (is (not (str/includes? (str/lower-case text) "lambda")) (.getName file)))
    (let [view-text (slurp (io/file agent-dir "Som-Goal-View.km"))
          directive-text (slurp (io/file agent-dir "Som-Level-Directive.km"))]
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
                          nil)
          travel (project budgeted
                          (merge behind-clock
                                 {"som-untried-exits" "(:seq north)"})
                          nil)]
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
                         nil)]
      (value-is (q state "som-pace") "(behind)")
      (expect-rule state 10)
      (expect-attempts state
                       "((:seq (:args travel movement north \"\")))")))
  (testing "steady takes the only exit"
    (let [state (project open-goal
                         (merge base-clock
                                {"som-prior-notch" "steady"
                                 "som-untried-exits" "(:seq north)"})
                         nil)]
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

(deftest a-second-scenario-does-not-see-the-first-clock
  (let [first-scenario (project budgeted base-clock nil)
        second (on loaded "(the som-level of *Clock)")]
    (is (frame/known-frame? (:kb first-scenario) (symbol "*Clock")))
    (is (not (frame/known-frame? (:kb loaded) (symbol "*Clock"))))
    (value-nil second)))
