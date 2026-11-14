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

(deftest justify-prints-the-rule-and-get-justification-returns-it
  (let [ruled (answer "(every Cat has (color (black)))")
        cat (on ruled "(_Cat1 has (instance-of (Cat)))")
        color (on cat "(the color of _Cat1)")
        just (on color "(justify (:triple _Cat1 color black))")
        got (on color "(get-justification (:triple _Cat1 color black))")
        text (term/car (:value got))]
    (is (= (term "(t)") (:value just)))
    (is (str/includes? (:text just) "subgoal"))
    (is (str/includes? (:text just) "(every Cat has (color (black)))"))
    (is (term/singleton? (:value got)))
    (is (string? text))
    (is (str/includes? text "subgoal"))
    (is (str/includes? text "(every Cat has (color (black)))"))))
