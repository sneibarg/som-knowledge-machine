(ns som.km.explain-test
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.explain :as explain]
            [som.km.frame :as frame]
            [som.km.read :as read]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(defn- term [text]
  (:value (read/read-term text)))

(deftest user-comments-are-bracketed-symbols
  (is (explain/user-comment? (symbol "[tag]")))
  (is (explain/user-comment? (symbol "[]")))
  (is (not (explain/user-comment? (symbol "[tag"))))
  (is (not (explain/user-comment? (symbol "tag]"))))
  (is (not (explain/user-comment? (symbol "["))))
  (is (not (explain/user-comment? "[tag]")))
  (is (not (explain/user-comment? nil)))
  (is (explain/comment-tag? (explain/convert-comment (symbol "[Car1]")))))

(deftest a-source-is-a-list-headed-by-at
  (is (explain/source? (term "(@ Car parts)")))
  (is (not (explain/source? (term "(a Car)"))))
  (is (not (explain/source? (symbol "@")))))

(deftest convert-comments-stores-the-comm-form
  (is (= (term/km-list (symbol "comm") (symbol "[Car1]") (symbol "Self"))
         (explain/convert-comment (symbol "[Car1]"))))
  (is (= (term "(a (comm [Car1] Self))")
         (explain/convert-comments (term "(a [Car1])"))))
  (let [stored (explain/convert-comment (symbol "[Car1]"))]
    (is (identical? stored (explain/convert-comments stored)))))

(deftest decomment-leaves-a-pair-unless-asked-to-collapse-it
  (is (= (term "(a)") (explain/decomment (term "(a [1])"))))
  (is (= (symbol "a")
         (explain/decomment (term "(a [1])") :no-delistification? false))))

(deftest desource-drops-a-source-and-one-pair-of-parentheses
  (is (= (term "(a Wheel with (position (front)))")
         (explain/desource
          (term "(a Wheel with (position ((front (@ Car has-part Wheel position)))))"))))
  (is (= (term "(:seq)")
         (explain/desource (term "(:seq (@ p))"))))
  (is (not= :seq (explain/desource (term "(:seq (@ p))")))))

(deftest desource-decomment-follows-the-lisp-examples
  ;; The comment above desource+decomment still prints (cat (dog (man))).
  ;; That is the older remove-if walk. The function that is defined
  ;; delistifies ([4] [45] man) to man, so the result is (cat (dog man)).
  (is (= (term "(cat (dog man))")
         (explain/desource-decomment
          (term "(cat [1] (dog [3] ([4] [45] man)))"))))
  (is (= (term "(a Man with (size (((a Large)))))")
         (explain/desource-decomment
          (term "(a Man with (size (((a [2] Large)))) [1])"))))
  (is (= (term "(a Man with (size (*large)))")
         (explain/desource-decomment
          (term "(a Man with (size (([2] *large))) [1])"))))
  (is (= (term "(instance-of (Thing))")
         (explain/desource-decomment (term "(instance-of (Thing [cat]))"))))
  (is (= (symbol "*cat")
         (explain/desource-decomment (term "(*cat [1])"))))
  (is (= (term "(no-inheritance)")
         (explain/desource-decomment (term "(no-inheritance [1])"))))
  (is (= (term "(:seq)")
         (explain/desource-decomment (term "(:seq [1])")))))

(deftest retain-comments-returns-the-same-expression
  (let [expr (term "(*cat [1])")]
    (is (= expr (explain/desource-decomment expr :retain-comments? true)))))

(deftest desource-decomment-top-level-collapses-one-pair
  (is (= (symbol "*black")
         (explain/desource-decomment-top-level (term "(*black (@ Car color))"))))
  (is (= (term "(the age of Fred)")
         (explain/desource-decomment-top-level (term "(the age of Fred (@ Car))"))))
  (is (= (term "(:seq)")
         (explain/desource-decomment-top-level (term "(:seq [1])"))))
  (is (= (term "(no-inheritance)")
         (explain/desource-decomment-top-level (term "(no-inheritance [1])")))))

(deftest a-dotted-list-is-an-error-for-mapcar-and-not-for-the-tail-walk
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"dotted"
        (explain/desource (term/cons-cell (symbol "a") (symbol "b")))))
  (let [expr (term/cons-cell (symbol "a") (symbol "b"))]
    (is (= expr (explain/desource-decomment expr)))))

(defn- answer [text]
  (engine/evaluate text))

(defn- on
  "Evaluate text on the result of a previous evaluation."
  [previous text]
  (engine/evaluate text {:kb (:kb previous) :query (:query previous)}))

(defn- nth-value [value n]
  (loop [value value
         n n]
    (cond
      (or (nil? value) (not (term/cons? value))) nil
      (zero? n) (term/car value)
      :else (recur (term/cdr value) (dec n)))))

(defn- label [frame]
  (when (term/km-symbol? frame) (term/symbol-name frame)))

(deftest why-with-no-answer-says-so
  (let [why (answer "(why)")]
    (is (nil? (:value why)))
    (is (not= "not-ported" (:error why)))
    (is (str/includes? (:text why) "There are no answers to explain!"))))

(deftest an-inherited-value-explains-itself
  (let [ruled (answer "(every Cat has (color (black)))")
        cat (on ruled "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")
        why (on color "(why)")
        direct (on color "(why (:triple _Cat1 color black))")
        plain (answer "(Fred has (color (red)))")
        bare (on plain "(why (:triple Fred color red))")]
    (is (= (term "(black)") (:value color)))
    (is (empty? (:errors color)))
    (is (= (term "(t)") (:value why)))
    (is (str/includes? (:text why) "(:triple _Cat1 color black [in *Global]) because:"))
    (is (str/includes? (:text why) "RULE: (every Cat has (color (black)))"))
    (is (str/includes? (:text direct) "RULE: (every Cat has (color (black)))"))
    (is (= (term "(t)") (:value direct)))
    (is (= (term "(t)") (:value bare)))
    (is (str/includes? (:text bare) "(no explanation available)"))))

(deftest an-inverse-triple-uses-the-stored-direction
  (let [loved (answer "(Fred has (loves (Sue)))")
        told (on loved "(explanation (:triple Fred loves Sue) ((added-at Person \"by hand\")))")
        why (on told "(why (:triple Sue loves-of Fred))")]
    (is (= (term "(t)") (:value told)))
    (is (empty? (:errors told)))
    (is (= (term "(t)") (:value why)))
    (is (str/includes? (:text why) "(:triple Fred loves Sue"))
    (is (str/includes? (:text why) "(added-at Person \"by hand\")"))))

(deftest a-clone-explanation-survives-on-both-frames
  (let [opened (answer "(a-prototype Cat)")
        name (label (term/car (:value opened)))
        colored (on opened (str "(" name " has (color (black)))"))
        closed (on colored "(end-prototype)")
        cat (on closed "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")
        why (on color "(why (:triple _Cat1 color black))")
        records (some (fn [[source target]]
                        (when (utils/eql? target (symbol "_Cat1"))
                          (frame/explanations (:kb color) source)))
                      (:bindings (:kb color)))]
    (is (= (term "(black)") (:value color)))
    (is (= (term "(t)") (:value why)))
    (is (str/includes? (:text why) "cloned-from"))
    (is (str/includes? (:text why) name))
    (is (some (fn [record]
                (and (utils/eql? (symbol "color") (nth-value record 1))
                     (utils/eql? (symbol "black") (nth-value record 2))
                     (utils/eql? (symbol "cloned-from")
                                 (term/car (nth-value record 3)))))
              (utils/elements records)))
    (is (not (some #(utils/eql? (symbol "instance-of") (nth-value % 1))
                   (utils/elements records))))))

(deftest a-bad-why-argument-is-a-user-error
  (let [bad (answer "(why (Fred))")
        created (answer "(retain-expr (1 + 2))")]
    (is (nil? (:value bad)))
    (is (some #(str/includes? % "Bad argument to (why ...)!") (:errors bad)))
    (is (some #(str/starts-with? % "ERROR! ") (:errors bad)))
    (is (= "not-ported" (:error created)))
    (is (= "This form is not ported yet: (retain-expr (1 + 2))." (:message created)))))

(deftest explanations-can-be-turned-off-and-on
  (let [off (answer "(no-explanations)")
        ruled (on off "(every Cat has (color (black)))")
        cat (on ruled "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")
        quiet (on color "(why)")
        restored (on quiet "(explanations)")
        dog-rule (on restored "(every Dog has (color (white)))")
        dog (on dog-rule "(_Dog1 has (instance-of (Dog)))")
        white (on dog "(the color of _Dog1)")
        told (on white "(why)")]
    (is (= (term "(t)") (:value off)))
    (is (= (term "(black)") (:value color)))
    (is (= (term "(t)") (:value quiet)))
    (is (str/includes? (:text quiet) "(no explanation available)"))
    (is (= (term "(t)") (:value restored)))
    (is (= (term "(white)") (:value white)))
    (is (str/includes? (:text told) "RULE: (every Dog has (color (white)))"))))

(deftest a-local-situation-keeps-its-own-explanation
  (let [started (engine/session)
        sit (symbol "_Sit1")
        kb (frame/set-situation (:kb started) sit)
        colored (engine/evaluate "(_Cat1 has (color ((black (@ _Cat1 Cat color)))))"
                                 {:kb kb :query (:query started)})
        local (on colored "(why (:triple _Cat1 color black))")
        global-kb (frame/set-situation (:kb local) term/global-situation)
        global (engine/evaluate "(why (:triple _Cat1 color black))"
                                {:kb global-kb :query (:query local)})
        classed (engine/evaluate
                 "(_Dog1 has (instance-of ((Dog (@ _Dog1 Thing instance-of)))))"
                 {:kb kb :query (:query started)})
        local-class (frame/explanations (:kb classed) (symbol "_Dog1") :situation sit)
        global-class (frame/explanations (:kb classed) (symbol "_Dog1"))]
    (is (str/includes? (:text local) "RULE: (every Cat has (color (black)))"))
    (is (str/includes? (:text global) "(no explanation available)"))
    (is (not (str/includes? (str (:text global)) "(every Cat has (color (black)))")))
    (is (nil? local-class))
    (is (some? global-class))))

(deftest a-repeated-explanation-keeps-the-earlier-copy
  (let [sit (symbol "_Sit1")
        kb (frame/set-situation (:kb (engine/session)) sit)
        entry (term "(_Cat1 color black (added-at Person \"local\"))")
        other (term "(_Cat1 size small (added-at Person \"global\"))")
        kb (frame/record-explanation kb (symbol "_Cat1") entry :situation sit)
        kb (frame/record-explanation kb (symbol "_Cat1") entry
                                     :situation term/global-situation)
        kb (frame/record-explanation kb (symbol "_Cat1") other
                                     :situation term/global-situation)
        found (frame/explanation-records kb (symbol "_Cat1") nil :situation sit)
        records (utils/elements (:value found))]
    (is (= 2 (count records)))
    (is (utils/equal? entry (first records)))
    (is (utils/equal? other (second records)))))

(deftest justify-is-quiet-until-developer-mode
  (let [ruled (answer "(every Cat has (color (black)))")
        cat (on ruled "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")
        just (on color "(justify (:triple _Cat1 color black))")
        got (on color "(get-justification (:triple _Cat1 color black))")
        dev-kb (assoc-in (:kb color) [:runtime :developer-mode?] true)
        dev (engine/evaluate "(justify (:triple _Cat1 color black))"
                             {:kb dev-kb :query (:query color)})]
    (is (= (term "(t)") (:value just)))
    (is (not (str/includes? (str (:text just)) "subgoal")))
    (is (nil? (:value got)))
    (is (str/includes? (:text dev) "subgoal"))
    (is (str/includes? (:text dev) "(every Cat has (color (black)))"))))

(defn- explanation-at
  [result frame n]
  (nth-value (nth-value (frame/explanations (:kb result) frame) n) 3))

(deftest explanations-are-stored-newest-first
  (let [older (answer "(explanation (:triple Fred color red) ((added-at Cat \"older\")))")
        newer (on older "(explanation (:triple Fred color red) ((added-at Cat \"newer\")))")
        again (on newer "(explanation (:triple Fred color red) ((added-at Cat \"older\")))")
        why (on again "(why (:triple Fred color red))")
        text (:text why)
        records (utils/elements (frame/explanations (:kb again) (symbol "Fred")))]
    (is (= 2 (count records)))
    (is (utils/equal? (term "(added-at Cat \"newer\")") (explanation-at again (symbol "Fred") 0)))
    (is (utils/equal? (term "(added-at Cat \"older\")") (explanation-at again (symbol "Fred") 1)))
    (is (< (.indexOf text "newer") (.indexOf text "older")))))

(deftest modify-set-collapses-one-value-and-drops-a-remaining-set
  (let [one (answer "(explanation (:triple Fred color red) ((:set (a Cat))))")
        two (on one "(explanation (:triple Sue color blue) ((:set (a Cat) (a Dog))))")
        quiet (on two "(explanation (:triple Joe color red) ((:set red blue)))")
        atom (on quiet "(explanation (:triple Sam color green) ((:set green)))")
        path (on atom "(explanation (:triple Pat color blue) ((:set (the color of Fred))))")
        bad (on path "(explanation (:triple Ann color white) ((:set (the color of Fred) (a Dog))))")]
    (is (utils/equal? (term "(a Cat)") (explanation-at one (symbol "Fred") 0)))
    (is (nil? (frame/explanations (:kb two) (symbol "Sue"))))
    (is (some #(str/includes? % "PROGRAM ERROR!") (:errors two)))
    (is (some #(str/includes? % "not-fully-evaluated") (:errors two)))
    (is (nil? (frame/explanations (:kb quiet) (symbol "Joe"))))
    (is (empty? (:errors quiet)))
    (is (nil? (frame/explanations (:kb atom) (symbol "Sam"))))
    (is (empty? (:errors atom)))
    (is (utils/equal? (term "(the color of Fred)") (explanation-at path (symbol "Pat") 0)))
    (is (empty? (:errors path)))
    (is (= (term "(t)") (:value bad)))
    (is (nil? (frame/explanations (:kb bad) (symbol "Ann"))))
    (is (some #(str/includes? % "PROGRAM ERROR!") (:errors bad)))
    (is (some #(str/includes? % "not-fully-evaluated") (:errors bad)))))

(deftest comments-are-stored-shown-and-written-in-order
  (let [pet (answer "(comment [Pet] \"a pet\" \"owned\")")
        dog (on pet "(comment [Dog] \"d\")")
        shown (on dog "(show-comment [Pet])")
        missing (on dog "(show-comment [None])")
        bad (on dog "(comment Fred \"a\")")
        empty (on dog "(comment [x])")
        written (on dog "(write-kb)")
        text (str (:text written))]
    (is (= (term "(\"a pet\" \"owned\")") (:value pet)))
    (is (= (term "(\"a pet\" \"owned\")") (:value shown)))
    (is (nil? (:value missing)))
    (is (empty? (:errors missing)))
    (is (nil? (:value bad)))
    (is (some #(str/includes? % "square brackets") (:errors bad)))
    (is (nil? (:value empty)))
    (is (empty? (:errors empty)))
    (is (str/includes? text "COMMENTS"))
    (is (< (.indexOf text "[Pet]") (.indexOf text "[Dog]")))
    (is (str/includes? text "(comment [Pet] \"a pet\" \"owned\")"))))

(deftest why-prints-entry-and-exit-text
  (let [noted (answer "(comment [Pet] \"owned by someone\" \"a pet is owned\" (:triple Sue color blue))")
        marked (on noted "(explanation (:triple Fred color red) ((red (comm [Pet] Fred))))")
        why (on marked "(why (:triple Fred color red))")]
    (is (= (term "(t)") (:value why)))
    (is (str/includes? (:text why) "ENTRY TEXT: (\"a pet is owned\")"))
    (is (str/includes? (:text why) "EXIT TEXT: (\"owned by someone\")"))
    (is (str/includes? (:text why) "<location unknown>"))))

(deftest why-reports-several-sources-and-still-prints-the-rule
  (let [marked (answer "(explanation (:triple Fred color red) ((red (@ Fred Cat color) (@ Sue Dog color))))")
        why (on marked "(why (:triple Fred color red))")]
    (is (= (term "(t)") (:value why)))
    (is (some #(str/includes? % "More than one source path") (:errors why)))
    (is (str/includes? (:text why) "RULE:"))))

(deftest justify-leaves-names-the-class-the-triple-came-from
  (let [marked (answer "(explanation (:triple Fred color red) ((added-at Cat \"by hand\")))")
        quiet (on marked "(justify (:triple Fred color red))")
        kb (assoc-in (:kb marked) [:runtime :justify-leaves?] true)
        just (engine/evaluate "(justify (:triple Fred color red))"
                              {:kb kb :query (:query marked)})]
    (is (not (str/includes? (str (:text quiet)) "subgoal")))
    (is (not (str/includes? (str (:text quiet)) "from Cat")))
    (is (str/includes? (str (:text just)) "The color of fred = red. (from Cat)"))))

(deftest a-comment-tag-is-walked-before-the-leaf
  (let [noted (answer "(comment [Pet] \"owned by someone\" \"a pet is owned\" (:triple Sue color blue))")
        marked (on noted "(explanation (:triple Fred color red) ((added-at Cat \"note\" (comm [Pet] Fred))))")
        just (on marked "(justify (:triple Fred color red))")
        text (str (:text just))
        sub (on marked "(explanation (:triple Fred color blue) ((added-at Cat \"s\" (comm [subslot-reasoning] Fred hue))))")
        hue (on sub "(justify (:triple Fred color blue))")]
    (is (= (term "(t)") (:value just)))
    (is (str/includes? text "The color of fred = red because:"))
    (is (str/includes? text "a pet is owned"))
    (is (< (.indexOf text "a pet is owned") (.indexOf text "owned by someone")))
    (is (not (str/includes? text "subgoal")))
    (is (str/includes? (str (:text hue)) "is a subslot of"))))

(deftest a-comment-chain-stops-at-the-depth-limit
  (let [built (reduce (fn [prev n]
                        (let [tag (str "[D" n "]")
                              frame (str "F" n)
                              next (str "F" (inc n))
                              noted (on prev (str "(comment " tag
                                                  " \"exit\" \"call\" (:triple "
                                                  next " color red))"))
                              marked (on noted (str "(explanation (:triple " frame
                                                      " color red) ((added-at Thing \"n\" (comm "
                                                      tag " " frame "))))"))]
                          marked))
                      (answer "(comment [D0] \"exit\" \"call\" (:triple F1 color red))")
                      (range 1 21))
        first (on built "(explanation (:triple F0 color red) ((added-at Thing \"n\" (comm [D0] F0))))")
        just (on first "(justify (:triple F0 color red))")]
    (is (str/includes? (str (:text just))
                       "(depth limit for justification reached...no further details below this)"))))

(deftest explain-all-prints-the-rule-and-clear-drops-the-record
  (let [ruled (answer "(every Cat has (color (black)))")
        cat (on ruled "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")
        all (on color "(explain-all)")
        hidden (on color "(explain-all :include-globalp nil)")
        kept (on all "(clear-explanations)")
        still (on kept "(why (:triple _Cat1 color black))")
        sit (on still "(new-situation)")
        place (term/car (:value sit))
        local (on sit "(explanation (:triple Fred color red) ((added-at Cat \"local\")))")
        cleared (on local "(clear-explanations)")
        gone (on cleared "(clear-explanations :clear-globalp t)")]
    (is (str/includes? (:text all) "(every Cat has (color (black)))"))
    (is (not (str/includes? (:text all) "RULE:")))
    (is (not (str/includes? (str (:text hidden)) "(every Cat has")))
    (is (str/includes? (:text still) "(every Cat has (color (black)))"))
    (is (some? (frame/explanations (:kb local) (symbol "Fred") :situation place)))
    (is (nil? (frame/explanations (:kb cleared) (symbol "Fred") :situation place)))
    (is (some? (frame/explanations (:kb cleared) (symbol "_Cat1"))))
    (is (nil? (frame/explanations (:kb gone) (symbol "_Cat1"))))))

(deftest a-remove-subsumers-explanation-vanishes-on-merge
  (let [linked (answer "(Tabby has (superclasses (Cat)))")
        spec (on linked "(_Spec has (instance-of (Tabby)))")
        gen (on spec "(_Gen has (instance-of (Cat)))")
        colored (on gen "(_Gen has (color (red)))")
        classed (on colored "(explanation (:triple _Gen instance-of Cat) ((added-at Thing \"gen\")))")
        marked (on classed "(explanation (:triple _Gen color red) ((added-at Thing \"color\")))")
        before (:value (frame/get-vals (:kb marked) (symbol "Cat") (symbol "instances")
                                        :dereference? false))
        merged (frame/merge-explanations (:kb marked) (symbol "_Gen") (symbol "_Spec"))
        after (:value (frame/get-vals merged (symbol "Cat") (symbol "instances")
                                       :dereference? false))
        copied (utils/elements (frame/explanations merged (symbol "_Spec")))
        kept (utils/elements (frame/explanations merged (symbol "_Gen")))]
    (is (utils/member? (symbol "_Gen") before))
    (is (not (utils/member? (symbol "_Gen") after)))
    (is (some #(and (utils/eql? (nth-value % 1) (symbol "color"))
                    (utils/eql? (nth-value % 2) (symbol "red")))
              copied))
    (is (not (some #(and (utils/eql? (nth-value % 1) (symbol "instance-of"))
                         (utils/eql? (nth-value % 2) (symbol "Cat")))
                   copied)))
    (is (some #(and (utils/eql? (nth-value % 1) (symbol "instance-of"))
                    (utils/eql? (nth-value % 2) (symbol "Cat")))
              kept))
    (is (some #(utils/eql? % (symbol "_Gen")) (frame/objects merged)))))
