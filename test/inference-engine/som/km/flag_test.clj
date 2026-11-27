(ns som.km.flag-test
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.frame :as frame]
            [som.km.read :as read]
            [som.km.term :as term]
            [som.km.utils :as utils]
            [som.km.writer :as writer]))

(defn- term-of [text]
  (:value (read/read-term text)))

(defn- answer [text]
  (engine/evaluate text))

(defn- on
  "Evaluate text on the result of a previous evaluation."
  [previous text]
  (engine/evaluate text {:kb (:kb previous) :query (:query previous)}))

(defn- mentions? [pattern state]
  (some #(re-find pattern %) (:errors state)))

(defn- count-of [result key]
  (or (get-in result [:query key]) 0))

(defn- slash [path]
  (str/replace path "\\" "/"))

(defn- temp-path [suffix]
  (.getAbsolutePath (java.io.File/createTempFile "km-step20-" suffix)))

(defmacro with-temp
  [binding & body]
  `(let [~binding (temp-path ".km")]
     (try
       ~@body
       (finally
         (io/delete-file ~binding true)))))

(deftest sometimes-evaluates-its-body
  (let [ran (answer "(sometimes (1 + 2))")
        stored (answer "(Fred has (color (red (sometimes (a Cat)))))")
        color (on stored "(the color of Fred)")
        again (on color "(the color of Fred)")]
    (is (= (term-of "(3)") (:value ran)))
    (is (frame/are-some? (:kb ran) :constraints))
    (is (empty? (:errors ran)))
    (is (= (term-of "(red _Cat1)") (:value color)))
    (is (= 1 (count-of color :skolems)))
    (is (empty? (:errors color)))
    (is (= (term-of "(red _Cat1)") (:value again)))
    (is (zero? (count-of again :skolems)))))

(deftest no-inheritance-skips-inheritance-and-subslots
  (let [cat (answer "(every Cat has (color (black)))")
        bare (on cat "(_Cat1 has (instance-of (Cat)) (color ((no-inheritance))))")
        blocked (on bare "(the color of _Cat1)")
        subs (on blocked "(color has (subslots (hue)))")
        hue (on subs "(_Cat2 has (hue (red)) (color ((no-inheritance))))")
        hidden (on hue "(the color of _Cat2)")
        local (on hidden "(_Cat3 has (instance-of (Cat)) (color (red (no-inheritance))))")
        kept (on local "(the color of _Cat3)")
        open (on kept "(_Cat4 has (instance-of (Cat)))")
        inherited (on open "(the color of _Cat4)")
        own-default (on inherited "(_Cat5 has (instance-of (Cat)) (color ((no-inheritance) (:default white))))")
        skipped (on own-default "(the color of _Cat5)")]
    (is (nil? (:value blocked)))
    (is (empty? (:errors blocked)))
    (is (nil? (:value hidden)))
    (is (empty? (:errors hidden)))
    (is (= (term-of "(red)") (:value kept)))
    (is (= (term-of "(black)") (:value inherited)))
    (is (nil? (:value skipped)))
    (is (empty? (:errors skipped)))))

(deftest set-filter-keeps-the-first-pair-of-each-unit
  (let [declared (answer "(every Measurement has (value ((set-filter pair-filter))))")
        stored (on declared
                   "(_M1 has (instance-of (Measurement))
                          (value ((:pair 1 *foot) (:pair 2 *foot)
                                  (:pair 1 *yard) (:pair 2 *yard) green)))")
        value (on stored "(the value of _M1)")
        upper (answer "(every Gauge has (value ((set-filter PAIR-FILTER))))")
        gauged (on upper
                    "(_G1 has (instance-of (Gauge))
                           (value ((:pair 1 *foot) (:pair 9 *foot))))")
        gauge (on gauged "(the value of _G1)")
        unknown (answer "(Fred has (color ((set-filter no-such-filter) red blue)))")
        color (on unknown "(the color of Fred)")]
    (is (= (term-of "((:pair 1 *foot) (:pair 1 *yard) green)") (:value value)))
    (is (empty? (:errors value)))
    (is (= (term-of "((:pair 1 *foot))") (:value gauge)))
    (is (= (term-of "(red blue)") (:value color)))
    (is (mentions? #"Unrecognized set-filter" color))))

(deftest a-default-is-applied-once
  (let [stored (answer "(Fred has (color ((:default (a Color)))))")
        first-read (on stored "(the color of Fred)")
        second (on first-read "(the color of Fred)")
        made (term/car (:value first-read))
        both (answer "(Sue has (color (blue (:default red))))")
        colors (on both "(the color of Sue)")
        single (answer "(age has (cardinality (N-to-1)))")
        aged (on single "(Pete has (age (30 (:default 40))))")
        age (on aged "(the age of Pete)")
        banned (answer "(Ann has (color ((<> red) (:default red))))")
        dropped (on banned "(the color of Ann)")
        other (on dropped "(Bob has (color ((<> red) (:default blue))))")
        blue (on other "(the color of Bob)")
        rule (answer "(every Cat has (color ((:default black))))")
        cat (on rule "(_Cat1 has (instance-of (Cat)))")
        black (on cat "(the color of _Cat1)")]
    (is (and (term/km-symbol? made)
             (str/starts-with? (term/symbol-name made) "_Color")))
    (is (= 1 (count-of first-read :skolems)))
    (is (zero? (count-of second :skolems)))
    (is (utils/eql? made (term/car (:value second))))
    (is (utils/member? (symbol "blue") (:value colors)))
    (is (utils/member? (symbol "red") (:value colors)))
    (is (= 2 (count (utils/elements (:value colors)))))
    (is (= (term-of "(30)") (:value age)))
    (is (empty? (:errors age)))
    (is (nil? (:value dropped)))
    (is (= (term-of "(blue)") (:value blue)))
    (is (= (term-of "(black)") (:value black)))))

(deftest a-top-level-query-turns-inverses-back-on
  (let [off (answer "(disable-installing-inverses)")
        quiet (frame/put-vals (:kb off) (symbol "Fred") (symbol "loves") (term-of "(Sue)"))]
    (is (= (term-of "(t)") (:value off)))
    (is (not (:installing-inverses? (:kb off))))
    (is (not (frame/known-frame? (:kb quiet) (symbol "Sue"))))
    (let [loved (on off "(Fred has (loves (Sue)))")
          inverse (on loved "(the loves-of of Sue)")]
      (is (:installing-inverses? (:kb loved)))
      (is (= (term-of "(Fred)") (:value inverse))))))

(deftest a-deletion-writes-the-inverse-exclusion
  (let [sit (answer "(new-situation)")
        loved (on sit "(Fred has (loves (Sue)))")
        act (on loved "(_Move has (del-list ((:triple Fred loves Sue))))")
        done (on act "(do-and-next _Move)")
        loves (on done "(the loves of Fred)")
        inverse (frame/get-vals (:kb loves) (symbol "Sue") (symbol "loves-of"))
        cleared (answer "(Fred has (loves (Mary)))")
        removed (on cleared "(Fred also-hasnt (loves (Mary)))")
        gone (frame/get-vals (:kb removed) (symbol "Mary") (symbol "loves-of"))
        builtin (answer "(new-situation)")
        tee (on builtin "(Fred has (loves (t)))")
        drop (on tee "(_Move has (del-list ((:triple Fred loves t))))")
        after (on drop "(do-and-next _Move)")
        truth (frame/get-vals (:kb after) (symbol "t") (symbol "loves-of"))]
    (is (nil? (:value loves)))
    (is (utils/member? (term-of "(<> Fred)") (:value inverse) utils/equal?))
    (is (nil? (:value gone)))
    (is (nil? (:value truth)))))

(deftest a-load-leaves-inverses-off-when-the-save-had-them-off
  (with-temp path
    (let [base (:kb (answer "(Fred has (color (red)))"))
          quiet (frame/set-installing-inverses base false)
          text (writer/write-kb-text quiet)
          _ (spit path text :encoding "UTF-8")
          loaded (answer (str "(load-kb \"" (slash path) "\")"))]
      (is (str/includes? text "had inverse installation off"))
      (is (not (:installing-inverses? (:kb loaded))))
      (is (= (term-of "(red)")
             (:value (frame/get-vals (:kb loaded) (symbol "Fred") (symbol "color")))))))
  (with-temp path
    (let [base (:kb (answer "(Fred has (color (red)))"))
          text (writer/write-kb-text base)
          _ (spit path text :encoding "UTF-8")
          loaded (answer (str "(load-kb \"" (slash path) "\")"))]
      (is (not (str/includes? text "had inverse installation off")))
      (is (:installing-inverses? (:kb loaded))))))
