(ns som.km.survivor-test
  (:require [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.frame :as frame]
            [som.km.print :as print]
            [som.km.read :as read]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(defn- term-of [text]
  (:value (read/read-term text)))

(defn- answer [text]
  (engine/evaluate text))

(defn- on
  "Evaluate text on the result of a previous evaluation."
  [previous text]
  (engine/evaluate text {:kb (:kb previous) :query (:query previous)}))

(defn- items [values]
  (set (utils/elements values)))

(defn- holds? [item values]
  (contains? (items values) item))

(defn- km [value]
  (print/km-format value))

(defn- nth-value [value n]
  (loop [value value
         n n]
    (cond
      (or (nil? value) (not (term/cons? value))) nil
      (zero? n) (term/car value)
      :else (recur (term/cdr value) (dec n)))))

(deftest an-earlier-duplicate-survives-the-situation-climb
  (let [global (answer "(Fred has (color (red)))")
        sit (on global "(new-situation)")
        blue (on sit "(Fred has (color (blue)))")
        made (on blue "(a Situation with (supersituations (_Situation1)))")
        situation (term/car (:value made))
        theory (on made "(a Theory)")
        name (term/car (:value theory))
        stored (on theory (str "(in-theory " (km name) " (Fred has (color (red))))"))
        seen (on stored (str "(see-theory " (km name) ")"))
        before (frame/get-vals (:kb seen) (symbol "Fred") (symbol "color")
                               :situation situation)
        color (on seen (str "(in-situation " (km situation) " (the color of Fred))"))]
    (is (nil? (:value before)))
    (is (= (term-of "(red blue)") (:value color)))
    (is (empty? (:errors color)))))

(deftest a-depth-limit-writes-the-residue-back
  (let [sue (answer "(Sue has (age (30)))")
        fred (on sue "(Fred has (age ((the age of Sue))))")
        read (engine/evaluate "(the age of Fred)"
                              {:kb (:kb fred)
                               :query (assoc (:query fred) :km-depth-limit -1)})
        stored (frame/get-vals (:kb read) (symbol "Fred") (symbol "age"))]
    (is (= (term-of "(30)") (:value read)))
    (is (= (term-of "(30)") (:value stored)))
    (is (empty? (:errors read)))))

(deftest a-clone-cycle-explanation-is-dropped
  (let [opened (answer "(a-prototype Cat)")
        proto (term/car (:value opened))
        colored (on opened (str "(" (km proto) " has (color (black)))"))
        planted (frame/record-explanation
                 (:kb colored)
                 proto
                 (term/km-list proto (symbol "color") (symbol "black")
                               (term/km-list (symbol "cloned-from") proto proto proto)))
        closed (engine/evaluate "(end-prototype)" {:kb planted :query (:query colored)})
        cloned (on closed (str "(clone " (km proto) ")"))
        clone (term/car (:value cloned))
        records (utils/elements (frame/explanations (:kb cloned) clone))
        cycle? (fn [record]
                 (let [expl (nth-value record 3)]
                   (and (term/cons? expl)
                        (utils/eql? (symbol "cloned-from") (term/car expl))
                        (utils/eql? clone (nth-value expl 1)))))
        kept? (fn [record]
                (let [expl (nth-value record 3)
                      source (nth-value expl 1)]
                  (and (term/cons? expl)
                       (utils/eql? (symbol "cloned-from") (term/car expl))
                       (some? (:value (frame/get-vals (:kb cloned) source
                                                      (symbol "prototype-of")
                                                      :situation term/global-situation))))))]
    (is (some? clone))
    (is (empty? (:errors cloned)))
    (is (not (some cycle? records)))
    (is (some kept? records))))

(deftest a-partial-prototype-merges-one-appending-part
  (let [declared (answer "(parts has (combine-values-by-appending (t)))")
        opened (on declared "(a-prototype Cell)")
        root (term/car (:value opened))
        walled (on opened (str "(" (km root) " has (parts ((a Wall))))"))
        proto-wall (term/car (:value (frame/get-vals (:kb walled) root (symbol "parts")
                                                     :situation term/global-situation)))
        marked (on walled (str "(" (km proto-wall) " has (origin (proto)))"))
        closed (on marked "(end-prototype)")
        manual (on closed "(a Wall)")
        wall (term/car (:value manual))
        coded (on manual (str "(" (km wall)
                              " has (cloned-from (" (km proto-wall) ")) (code (mine)))"))
        cell (on coded (str "(_Cell1 has (instance-of (Cell)) (cloned-from ("
                            (km root) ")) (parts (" (km wall) ")))"))
        read (on cell "(the parts of _Cell1)")
        part (term/car (:value read))
        origin (on read (str "(the origin of " (km part) ")"))
        code (on origin (str "(the code of " (km part) ")"))]
    (is (= 1 (count (utils/elements (:value read)))))
    (is (holds? (symbol "proto") (:value origin)))
    (is (holds? (symbol "mine") (:value code)))
    (is (empty? (:errors read)))))

(deftest an-appending-slot-keeps-both-parts-without-a-partial-prototype
  (let [declared (answer "(parts has (combine-values-by-appending (t)))")
        left (on declared "(_Cell1 has (parts (_Wall1)))")
        right (on left "(_Cell2 has (parts (_Wall2)))")
        merged (on right "(_Cell1 &! _Cell2)")
        parts (on merged "(the parts of _Cell1)")]
    (is (= #{(symbol "_Wall1") (symbol "_Wall2")} (items (:value parts))))
    (is (empty? (:errors parts)))))

(deftest an-ampersand-inverse-uses-the-current-situation
  (let [ready (answer "(a Situation)")
        situation (term/car (:value ready))
        stored (frame/put-vals (:kb ready) (symbol "Fred") (symbol "loves")
                               (term-of "((Sue & _X))")
                               :situation situation
                               :query (:query ready))
        global (frame/get-vals (:kb stored) (symbol "Sue") (symbol "loves-of")
                               :situation term/global-situation)
        local (frame/get-vals (:kb global) (symbol "Sue") (symbol "loves-of")
                              :situation situation)
        outer (frame/get-vals (:kb local) (symbol "Fred") (symbol "loves")
                              :situation situation)]
    (is (:installing-inverses? (:kb ready)))
    (is (holds? (symbol "Fred") (:value global)))
    (is (nil? (:value local)))
    (is (some? (:value outer)))))

(deftest thing-is-the-fallthrough-superclass
  (let [cat (answer "(_Cat1 has (instance-of (Cat)))")
        isa (on cat "(_Cat1 isa Thing)")
        every (on cat "(every Thing)")
        broad (on cat "(the all-subclasses of Thing)")
        integer (answer "(the superclasses of Integer)")
        stored (frame/get-vals (:kb integer) (symbol "Integer") (symbol "superclasses"))
        sequence (answer "(the subclasses of Sequence)")]
    (is (= (term-of "(t)") (:value isa)))
    (is (holds? (symbol "_Cat1") (:value every)))
    (is (holds? (symbol "Cat") (:value broad)))
    (is (= (term-of "(Number)") (:value integer)))
    (is (nil? (:value stored)))
    (is (= (term-of "(Pair Triple)") (:value sequence)))
    (is (empty? (:errors isa)))))
