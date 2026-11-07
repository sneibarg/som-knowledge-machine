(ns som.km.stack-test
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.frame :as frame]
            [som.km.read :as read]
            [som.km.stack :as stack]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(defn- term [text]
  (:value (read/read-term text)))

(defn- sym [text]
  (symbol text))

(def ^:private fred (sym "Fred"))
(def ^:private sue (sym "Sue"))

(defn- pushed
  [kb query expr & {:keys [target]}]
  (stack/push-to-goal-stack kb query expr :target target))

(deftest a-path-and-a-unification-canonicalize
  (is (= (term "(the parts of _Car23)")
         (stack/km-canonicalize (term "(_Car23 parts)"))))
  (is (= (term "(the parts)")
         (stack/km-canonicalize (term "(the parts)"))))
  (is (= (stack/km-canonicalize (term "(_X & _Engine1)"))
         (stack/km-canonicalize (term "(_Engine1 & _X)"))))
  (is (= (stack/km-canonicalize (term "(a & b)"))
         (stack/km-canonicalize (term "(b &! a)"))))
  (is (= (stack/km-canonicalize (term "(a &? b)"))
         (stack/km-canonicalize (term "(a == b)"))))
  (is (= (term "(_X &+! _Engine1)")
         (stack/km-canonicalize (term "(_X &+! _Engine1)"))))
  (is (not= (stack/km-canonicalize (term "(_X &+! _Engine1)"))
            (stack/km-canonicalize (term "(_X & _Engine1)"))))
  (is (= (term "(a set-unified-with b)")
         (stack/km-canonicalize (term "(a && b)"))))
  (is (= (term "(b set-unified-with a)")
         (stack/km-canonicalize (term "(b === a)"))))
  (is (= (stack/km-canonicalize (term "(a &&! b)"))
         (stack/km-canonicalize (term "(a === b)")))))

(deftest a-goal-records-five-elements-and-the-situation
  (let [kb (frame/set-situation (frame/knowledge-base) (sym "_Sit1"))
        stored (pushed kb frame/empty-query (term "(the parts of _Car1 [Eng1])")
                       :target (term "(the age of Fred)"))
        item (:value stored)
        query (:query stored)]
    (is (= (term "(the parts of _Car1)") (stack/stacked-canonical item)))
    (is (= (sym "_Sit1") (stack/stacked-situation item)))
    (is (= (term "(the parts of _Car1)") (stack/stacked-expr item)))
    (is (= 1 (stack/stacked-inference-number item)))
    (is (= (term "(the age of Fred)") (stack/stacked-target item)))
    (is (= (term "(the parts of _Car1)") (stack/top-level-goal query)))
    (let [unified (pushed kb query (term "(_X & _Engine1)"))]
      (is (= (sym "all situations")
             (stack/stacked-situation (:value unified))))
      (is (= (term "(the parts of _Car1)") (stack/top-level-goal (:query unified))))
      (is (= 2 (count (utils/elements (stack/goal-stack (:query unified))))))))
  (let [query (assoc frame/empty-query
                     :classification-inferences 2
                     :query-directed-inferences 3)
        stored (pushed (frame/knowledge-base) query (term "(the age of Fred)"))]
    (is (= 6 (stack/stacked-inference-number (:value stored))))))

(deftest bindings-make-two-goals-the-same-and-or-does-not-excuse-a-repeat
  (let [kb (:kb (frame/km-bind (frame/knowledge-base) (sym "_X") (sym "_Engine1")))
        once (pushed kb frame/empty-query (term "(the parts of _X)"))
        query (:query once)]
    (is (stack/looping-on? kb query (term "(the parts of _Engine1)")))
    (is (stack/looping-on? kb query (term "(the parts of _X [Eng1])")))
    (is (not (stack/looping-on? (frame/set-dereferencing kb false) query
                                (term "(the parts of _Engine1)"))))
    (let [with-or (pushed kb query (term "(or (the parts of _X) (a Dog))"))]
      (is (stack/looping-on? kb (:query with-or) (term "(the parts of _Engine1)"))))
    (let [elsewhere (frame/set-situation kb (sym "_Sit1"))]
      (is (not (stack/looping-on? elsewhere query (term "(the parts of _X)"))))
      (is (stack/looping-on? elsewhere
                             (:query (pushed elsewhere query (term "(a & b)")))
                             (term "(b & a)"))))))

(deftest set-unification-repeats-a-value-unification-only-one-way
  (let [kb (frame/knowledge-base)
        value (pushed kb frame/empty-query (term "(a & b)"))
        sets (pushed kb frame/empty-query (term "((a) && (b))"))]
    (is (not (stack/looping-on? kb frame/empty-query (term "(a & b)"))))
    (is (stack/looping-on? kb (:query value) (term "((a) && (b))")))
    (is (stack/looping-on? kb (:query value) (term "((b) &&! (a))")))
    (is (not (stack/looping-on? kb (:query sets) (term "(a & b)"))))))

(deftest full-equalities-record-the-instances-being-unified
  (let [kb (frame/knowledge-base)
        first-push (pushed kb frame/empty-query (term "(a & b)"))
        second-push (pushed kb (:query first-push) (term "(a &! c)"))
        popped (stack/pop-from-goal-stack kb (:query second-push))
        again (stack/pop-from-goal-stack kb (:query popped))]
    (is (= (term "(a b)") (:instances-being-unified (:query first-push))))
    (is (= (term "(c a b)") (:instances-being-unified (:query second-push))))
    (is (= (term "(b)") (:instances-being-unified (:query popped))))
    (is (nil? (:instances-being-unified (:query again))))
    (is (nil? (:value (stack/pop-from-goal-stack kb (:query again)))))
    (let [open (pushed kb frame/empty-query (term "(a &+ b)"))
          test-only (pushed kb frame/empty-query (term "(a &? b)"))
          nested (pushed kb frame/empty-query (term "(a & (a Car))"))]
      (is (nil? (:instances-being-unified (:query open))))
      (is (nil? (:instances-being-unified (:query test-only))))
      (is (nil? (:instances-being-unified (:query nested)))))
    (let [kept (stack/clear-goal-stack (:query second-push))]
      (is (nil? (:goal-stack (:query kept))))
      (is (= (term "(c a b)") (:instances-being-unified (:query kept)))))))

(deftest pending-equality-follows-bindings-and-looks-inside-a-set
  (let [kb (:kb (frame/km-bind (frame/knowledge-base) (sym "_X") fred))
        direct (pushed kb frame/empty-query (term "(_X &! Sue)"))
        inside (pushed kb frame/empty-query (term "(:set a (Fred & Sue))"))]
    (is (stack/pending-equality? kb (:query direct) fred sue))
    (is (stack/pending-equality? kb (:query direct) sue fred))
    (is (not (stack/pending-equality? kb (:query direct) fred fred)))
    (is (stack/pending-equality? kb (:query inside) fred sue))
    (is (not (stack/pending-equality? kb (:query (pushed kb frame/empty-query (term "(Fred &? Sue)")))
                                    fred sue)))))

(deftest a-loop-returns-the-values-found-so-far
  (let [kb (:kb (frame/put-vals (frame/knowledge-base) fred (sym "age") (term "(30)")))
        done (stack/handle-looping kb frame/empty-query (term "(the age of Fred)"))
        path (stack/handle-looping kb frame/empty-query (term "(Fred age)"))
        open (stack/handle-looping
              kb frame/empty-query (term "(Fred age)")
              :reason :depth-limit-reached)]
    (is (= (term "(30)") (:value done)))
    (is (:looping? (:query done)))
    (is (not (contains? done :message)))
    (is (= (term "(30)") (:value path)))
    (is (= (term "(30)") (:value open))))
  (let [kb (:kb (frame/put-vals (frame/knowledge-base) fred (sym "age")
                                (term "((a Dog))")))
        residual (stack/handle-looping kb frame/empty-query (term "(the age of Fred)"))
        blocked (stack/handle-looping
                 kb (:query (pushed kb frame/empty-query (term "(a Dog)")))
                 (term "(the age of Fred)"))]
    (is (nil? (:value residual)))
    (is (= "The loop's remaining expression is not evaluated yet."
           (:message residual)))
    (is (nil? (:value blocked)))
    (is (not (contains? blocked :message))))
  (let [kb (frame/knowledge-base)]
    (is (= (term "(t)")
           (:value (stack/handle-looping kb frame/empty-query (term "(a &? b)")))))
    (is (= (term "(t)")
           (:value (stack/handle-looping kb frame/empty-query (term "(a &+? b)")
                                          :reason :depth-limit-reached))))
    (is (nil? (:value (stack/handle-looping kb frame/empty-query (term "(a &? b)")
                                             :reason :other))))
    (is (= (term "(Fred)")
           (:value (stack/handle-looping kb frame/empty-query (term "(Fred & Sue)")))))
    (is (nil? (:value (stack/handle-looping kb frame/empty-query (term "(Fred &+! Sue)")))))
    (is (= (term "(a b)")
           (:value (stack/handle-looping kb frame/empty-query
                                          (term "((a b) && (c 1))")))))
    (is (nil? (:value (stack/handle-looping kb frame/empty-query (term "(a Dog)")))))))

(deftest the-goal-stack-is-shown-oldest-first-and-is-not-a-command
  (let [kb (frame/knowledge-base)
        query (:query (pushed kb frame/empty-query (term "(the parts of _Car1)")))
        text (:text (stack/show-goal-stack kb query))]
    (is (nil? (:value (stack/show-goal-stack kb query))))
    (is (= (str "--------------------\n\n"
                " CURRENT GOAL STACK IS AS FOLLOWS:\n"
                " -> (the parts of _Car1)\n"
                "\n--------------------\n")
           text)))
  (let [kb (frame/set-situation (frame/knowledge-base) (sym "_Sit1"))
        first-goal (pushed kb frame/empty-query (term "(_Car1 parts)")
                            :target (term "(the age of Fred)"))
        second-goal (pushed kb (:query first-goal) (term "(a & b)"))
        shown (stack/show-goal-stack kb (:query second-goal)
                                      :show-inference-numbers? true)
        lines (str/split-lines (:text shown))
        called (nth lines 5)]
    (is (str/starts-with? (nth lines 3) "1"))
    (is (str/includes? (nth lines 3) "-> (_Car1 parts)"))
    (is (str/includes? (nth lines 4) "[for (the age of Fred), in _Sit1]"))
    (is (str/includes? called "-> (a & b)"))
    (is (= 55 (str/index-of called "[called in |all situations|]")))
    (let [printed (engine/evaluate "(show-goal-stack)")]
      (is (:ok printed))
      (is (nil? (:value printed)))
      (is (str/includes? (:text printed) "CURRENT GOAL STACK IS AS FOLLOWS:"))
      (is (not (contains? printed :message))))))

(deftest reset-clears-both-stacks-and-keeps-the-unification-list
  (let [kb (frame/set-unstackable-instances (frame/knowledge-base)
                                            (term "(t f)"))
        goal (pushed kb frame/empty-query (term "(a & b)"))
        named (frame/create-instance-name kb (sym "Person") :query (:query goal))
        rebuilt (engine/reset kb :query (:query named))]
    (is (nil? (:goal-stack (:query rebuilt))))
    (is (nil? (:obj-stack (:query rebuilt))))
    (is (= (term "(a b)") (:instances-being-unified (:query rebuilt))))
    (is (= (term "(t f)") (frame/unstackable-instances (:kb rebuilt))))
    (let [blocked (frame/push-to-obj-stack (:kb rebuilt) (:query rebuilt) (sym "f"))
          allowed (frame/push-to-obj-stack (frame/knowledge-base)
                                           frame/empty-query (sym "f"))]
      (is (nil? (:obj-stack blocked)))
      (is (= (term "(f)") (:obj-stack allowed)))))
  (let [kb (frame/knowledge-base)
        stacked (frame/push-to-obj-stack kb frame/empty-query (sym "_X"))
        bound (:kb (frame/km-bind kb (sym "_X") fred))
        read (frame/obj-stack bound stacked)
        context (stack/new-context (:query read))
        goal (pushed bound frame/empty-query (term "(the age of Fred)"))]
    (is (= (term "(Fred)") (:value read)))
    (is (= (term "(Fred)") (:obj-stack (:query read))))
    (is (nil? (:obj-stack (:query context))))
    (is (= (term "(the age of Fred)")
           (stack/top-level-goal (:query (stack/new-context (:query goal))))))
    (is (true? (:value (stack/show-obj-stack bound stacked))))
    (is (= "   Fred\n" (:text (stack/show-obj-stack bound stacked)))))
  (let [stored (frame/put-vals (frame/knowledge-base) fred (sym "age") (term "(30)"))
        kb (:kb (frame/km-bind (:kb stored) (sym "_X") fred))
        stacked (frame/push-to-obj-stack kb (:query stored) (sym "_X"))
        gone (frame/delete-frame kb fred :query stacked)]
    (is (nil? (:obj-stack (:query gone))))))
