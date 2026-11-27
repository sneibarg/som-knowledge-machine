(ns som.km.frame-test
  (:require [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.frame :as frame]
            [som.km.read :as read]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(defn- term [text]
  (:value (read/read-term text)))

(defn- sym [text]
  (symbol text))

(def ^:private fred (sym "Fred"))
(def ^:private sue (sym "Sue"))
(def ^:private color (sym "color"))
(def ^:private loves (sym "loves"))

(defn- quiet
  "A knowledge base that does not install inverse frames."
  []
  (frame/set-installing-inverses (frame/knowledge-base) false))

(deftest an-empty-knowledge-base-starts-in-global
  (let [kb (frame/knowledge-base)]
    (is (= 0 (frame/gensym-counter kb)))
    (is (frame/dereferencing-on? kb))
    (is (not (frame/allow-ununify? kb)))
    (is (= term/global-situation (frame/current-situation kb)))
    (is (= [term/global-situation] (vec (frame/situations kb))))
    (is (= [] (vec (frame/theories kb))))
    (is (= [] (vec (frame/objects kb))))
    (is (nil? (:value (frame/ununify kb fred))))
    (is (= [] (vec (frame/deleted-frames kb))))))

(deftest put-and-get-keep-slot-order-and-the-frame
  (let [kb (quiet)
        stored (frame/put-vals kb fred color (term "(red blue)"))
        kb (:kb stored)
        aged (frame/put-vals kb fred (sym "age") (term "(1)"))
        slots (:value (frame/get-slotsvals (:kb aged) fred))]
    (is (= fred (:value stored)))
    (is (frame/known-frame? kb fred))
    (is (= (term "(red blue)") (:value (frame/get-vals kb fred color))))
    (is (= [fred] (vec (frame/objects kb))))
    (is (= (term "(Fred)") (:obj-stack (:query stored))))
    (is (= color (frame/slot-in (term/car slots))))
    (is (= (sym "age") (frame/slot-in (term/car (term/cdr slots)))))
    (let [again (frame/put-vals kb fred color (term "(red blue)")
                                :query (:query stored))]
      (is (= (:obj-stack (:query stored)) (:obj-stack (:query again)))))
    (let [cleared (frame/put-vals kb fred color nil)]
      (is (frame/known-frame? (:kb cleared) fred))
      (is (nil? (:value (frame/get-vals (:kb cleared) fred color)))))
    (let [absent (frame/put-vals (quiet) sue color nil)]
      (is (not (frame/known-frame? (:kb absent) sue))))))

(deftest add-val-appends-and-keeps-structurally-new-values
  (let [kb (quiet)
        once (frame/add-val kb fred color (sym "red"))
        twice (frame/add-val (:kb once) fred color (sym "blue"))
        same (frame/add-val (:kb twice) fred color (sym "red"))
        numbers (frame/add-val
                 (:kb (frame/add-val kb fred (sym "age") 1))
                 fred (sym "age") 1.0)
        dog (term "(a Dog)")
        owned (frame/add-val kb fred (sym "owns") dog)
        owned-again (frame/add-val (:kb owned) fred (sym "owns") (term "(a Dog)"))]
    (is (= (term "(red blue)") (:value (frame/get-vals (:kb twice) fred color))))
    (is (= (term "(red blue)") (:value same)))
    (is (= (term "(red blue)") (:value (frame/get-vals (:kb same) fred color))))
    (is (= (term/km-list 1 1.0) (:value (frame/get-vals (:kb numbers) fred (sym "age")))))
    (is (= (term/km-list dog) (:value (frame/get-vals (:kb owned-again) fred (sym "owns")))))
    (is (= (term/km-list dog) (:value owned-again)))))

(deftest add-val-inserts-a-subsumer-at-the-front
  (let [animal (frame/add-val (frame/knowledge-base) fred (sym "instance-of") (sym "Animal"))
        cat (frame/add-val (:kb animal) fred (sym "instance-of") (sym "Cat"))]
    (is (= (term "(Cat Animal)")
           (:value (frame/get-vals (:kb cat) fred (sym "instance-of")))))
    (is (= (term "(Fred)")
           (:value (frame/get-vals (:kb cat) (sym "Cat") (sym "instances")))))
    (is (= (term "(Fred)")
           (:value (frame/get-vals (:kb cat) (sym "Animal") (sym "instances")))))))

(deftest add-slotsvals-appends-instance-of-and-reorders-the-pairs
  (let [kb (frame/knowledge-base)
        animal (frame/add-slotsvals kb fred (term "((instance-of (Animal)))"))
        cat (frame/add-slotsvals (:kb animal) fred (term "((instance-of (Cat)))"))
        ordered (frame/add-slotsvals kb fred (term "((color (red)) (instance-of (Animal)))"))
        slots (:value (frame/get-slotsvals (:kb ordered) fred))]
    (is (= (term "(Animal Cat)")
           (:value (frame/get-vals (:kb cat) fred (sym "instance-of")))))
    (is (= (sym "instance-of") (frame/slot-in (term/car slots))))
    (is (= color (frame/slot-in (term/car (term/cdr slots)))))))

(deftest a-ground-inverse-is-installed-on-the-other-frame
  (let [stored (frame/put-vals (frame/knowledge-base) fred loves (term "(Sue)"))
        kb (:kb stored)
        replaced (frame/put-vals kb fred loves (term "(Mary)"))
        quiet-store (frame/put-vals (quiet) fred loves (term "(Sue)"))]
    (is (= (term "(Fred)") (:value (frame/get-vals kb sue (sym "loves-of")))))
    (is (= (term "(Sue Fred)") (:obj-stack (:query stored))))
    (is (= (term "(Mary)") (:value (frame/get-vals (:kb replaced) fred loves))))
    (is (= (term "(Fred)") (:value (frame/get-vals (:kb replaced) sue (sym "loves-of")))))
    (is (= (term "(Fred)")
           (:value (frame/get-vals (:kb replaced) (sym "Mary") (sym "loves-of")))))
    (is (not (frame/known-frame? (:kb quiet-store) sue)))))

(deftest an-args-value-installs-its-first-argument
  (let [stored (frame/put-vals (frame/knowledge-base) fred loves (term "((:args Sue lots))"))]
    (is (= (term "((:args Fred lots))")
           (:value (frame/get-vals (:kb stored) sue (sym "loves-of")))))))

(deftest member-facets-and-blocked-slots-do-not-install-inverses
  (let [kb (frame/knowledge-base)
        member (frame/put-vals kb fred loves (term "(Sue)")
                               :facet (sym "member-properties"))
        open (frame/put-vals kb (sym "Box1") (sym "open") (term "(t)"))
        scope (frame/put-vals kb fred (sym "prototype-scope") (term "(Cat)"))
        secret-kb (:kb (frame/put-vals kb (sym "secret") (sym "ignore-inverses") (term "(t)")))
        secret (frame/put-vals secret-kb fred (sym "secret") (term "(Sue)"))]
    (is (not (frame/known-frame? (:kb member) sue)))
    (is (not (frame/known-frame? (:kb open) (sym "t"))))
    (is (not (frame/known-frame? (:kb scope) (sym "Cat"))))
    (is (not (frame/known-frame? (:kb secret) sue)))))

(deftest cardinality-comes-from-the-built-in-list-or-the-stored-value
  (let [kb (frame/knowledge-base)]
    (is (frame/single-valued-slot? kb (sym "cardinality")))
    (is (= (sym "N-to-1") (frame/cardinality-of kb (sym "cardinality"))))
    (is (= (sym "N-to-N") (frame/cardinality-of kb loves)))
    (is (not (frame/single-valued-slot? kb loves))))
  (let [kb (:kb (frame/put-vals (frame/knowledge-base) (sym "wife") (sym "cardinality")
                                (term "(N-to-1)")))
        once (frame/add-val kb fred (sym "wife") sue)
        twice (frame/add-val (:kb once) fred (sym "wife") (sym "Mary"))]
    (is (frame/single-valued-slot? kb (sym "wife")))
    (is (= (term "((Sue & Mary))")
           (:value (frame/get-vals (:kb twice) fred (sym "wife"))))))
  (let [kb (:kb (frame/put-vals (frame/knowledge-base) (sym "wife-of") (sym "cardinality")
                                (term "(1-to-N)")))]
    (is (= (sym "N-to-1") (frame/cardinality-of kb (sym "wife")))))
  (let [kb (:kb (frame/put-vals (frame/knowledge-base) loves (sym "cardinality")
                                (term "(Many)")))]
    (is (= (sym "N-to-N") (frame/cardinality-of kb loves))))
  (let [kb (:kb (frame/put-vals (frame/knowledge-base) loves (sym "cardinality")
                                (term "(N-to-1 Many)")))]
    (is (= (sym "N-to-1") (frame/cardinality-of kb loves))))
  (let [kb (:kb (frame/put-vals (frame/knowledge-base) loves (sym "cardinality")
                                (term "(Many 1-to-1)")))]
    (is (= (sym "N-to-N") (frame/cardinality-of kb loves)))))

(deftest a-situation-stores-its-own-facet-and-reuses-the-name
  (let [sit (sym "_Sit1")
        kb (frame/set-situation (frame/knowledge-base) sit)
        stored (frame/put-vals kb fred color (term "(red)"))
        kb (:kb stored)
        named (frame/curr-situation-facet kb (sym "own-properties") sit)
        again (frame/curr-situation-facet (:kb named) (sym "own-properties") sit)]
    (is (nil? (:value (frame/get-vals kb fred color :situation term/global-situation))))
    (is (= (term "(red)") (:value (frame/get-vals kb fred color))))
    (is (identical? (:value named) (:value again)))
    (is (= "own-properties_Sit1" (term/symbol-name (:value named))))
    (is (= [term/global-situation sit] (vec (frame/situations kb)))))
  (let [kb (frame/set-situation (frame/knowledge-base) (sym "T1") :theory? true)]
    (is (= [(sym "T1")] (vec (frame/theories kb))))
    (is (= (sym "T1") (frame/current-situation kb)))
    (is (= [term/global-situation] (vec (frame/situations kb))))))

(deftest bindings-are-followed-and-a-cycle-is-an-error
  (let [kb (frame/knowledge-base)
        x (sym "_X")
        y (sym "_Y")
        bound (frame/km-bind kb x fred)]
    (is (= fred (:value bound)))
    (is (not (frame/known-frame? (:kb bound) x)))
    (is (= fred (frame/dereference (:kb bound) x)))
    (is (= fred (frame/dereference
                 (:kb (frame/km-bind (:kb (frame/km-bind kb x y)) y fred))
                 x)))
    (is (= (term "(the age of Fred)")
           (frame/dereference (:kb bound) (term "(the age of _X)"))))
    (let [expr (term "(the age of _X)")]
      (is (identical? expr
                      (frame/dereference (frame/set-dereferencing (:kb bound) false)
                                         expr)))))
  (let [kb (:kb (frame/put-vals (quiet) fred color (term "(red)")))
        bound (frame/km-bind kb fred sue)
        off (frame/set-dereferencing (:kb bound) false)]
    (is (nil? (:value (frame/km-bind kb fred fred))))
    (is (frame/known-frame? off fred))
    (is (nil? (:value (frame/get-vals off fred color))))
    (is (= sue (frame/dereference (:kb bound) fred)))
    (is (= (term "(blue)")
           (:value (frame/get-vals
                    (:kb (frame/put-vals (:kb bound) sue color (term "(blue)")))
                    fred color)))))
  (let [kb (:kb (frame/put-vals (quiet) fred color (term "(red)")))
        bound (frame/km-bind kb fred nil)]
    (is (nil? (:value bound)))
    (is (frame/known-frame? (:kb bound) fred))
    (is (nil? (:value (frame/get-vals (:kb bound) fred color))))
    (is (= fred (frame/dereference (:kb bound) fred))))
  (let [off (frame/set-dereferencing (frame/knowledge-base) false)
        kb (:kb (frame/km-bind (:kb (frame/km-bind off fred sue)) sue fred))
        on (frame/set-dereferencing kb true)]
    (is (thrown? clojure.lang.ExceptionInfo (frame/dereference on fred)))))

(deftest sources-are-stripped-only-when-the-value-is-fully-evaluated
  (let [kb (quiet)
        black (frame/put-vals kb fred color (term/km-list (term "(*black (@ Car color))")))
        age (term "(the age of Fred (@ Car))")
        kept (frame/put-vals kb fred (sym "age") (term/km-list age))
        data (frame/put-vals kb fred (sym "age") (term/km-list (term "(the age of Fred)")))
        scope (term "(the-class Cat [1])")
        prototype (frame/put-vals kb fred (sym "prototype-scope") (term/km-list scope))]
    (is (= (term "(*black)") (:value (frame/get-vals (:kb black) fred color))))
    (is (= (term/km-list age) (:value (frame/get-vals (:kb kept) fred (sym "age")))))
    (is (= (term/km-list (term "(the age of Fred)"))
           (:value (frame/get-vals (:kb data) fred (sym "age")))))
    (is (= (term/km-list scope)
           (:value (frame/get-vals (:kb prototype) fred (sym "prototype-scope")))))))

(deftest classes-slots-and-instances-read-the-store
  (let [kb (frame/knowledge-base)]
    (is (frame/class? kb (sym "Thing")))
    (is (not (frame/class? kb (sym "thing"))))
    (is (not (frame/known-frame? kb (sym "Thing"))))
    (is (frame/slot? kb (sym "cardinality")))
    (is (not (frame/slot? kb loves)))
    (is (not (frame/simple-slot? kb loves)))
    (is (frame/anonymous-instance? kb (sym "_Car1")))
    (is (frame/an-instance? kb (sym "_Car1")))
    (is (frame/orphan? kb (sym "_Car1")))
    (is (frame/orphan? kb (sym "NeverStored")))
    (is (not (frame/orphan? kb (sym "Thing"))))
    (is (frame/an-instance? kb 3))
    (is (frame/an-instance? kb "cat"))
    (is (frame/an-instance? kb (term "(the-class Cat)")))
    (is (frame/an-instance? kb (term "(:seq 1)")))
    (is (frame/an-instance? kb identity))
    (is (not (frame/anonymous-instance? kb fred)))
    (is (frame/named-instance? kb fred))
    (is (not (frame/named-instance? kb (sym "_Car1")))))
  (let [kb (:kb (frame/put-vals (frame/knowledge-base) (sym "Dog") (sym "superclasses")
                                (term "(Animal)")))]
    (is (frame/class? kb (sym "Dog"))))
  (let [kb (:kb (frame/put-vals (frame/knowledge-base) loves (sym "instance-of")
                                (term "(Slot)")
                                :situation term/global-situation))]
    (is (frame/slot? kb loves))
    (is (frame/simple-slot? kb loves))))

(deftest add-slotsvals-merges-values-and-keeps-an-existential
  (let [kb (quiet)
        once (frame/add-slotsvals kb fred (term "((color (red)))"))
        twice (frame/add-slotsvals (:kb once) fred (term "((color (red)))"))
        constrained (frame/add-slotsvals (:kb twice) fred (term "((color ((<> 23))))"))
        dog (frame/add-slotsvals kb fred (term "((owns (_Dog1)))"))
        both (frame/add-slotsvals (:kb dog) fred (term "((owns ((a Dog))))"))
        eq (frame/add-slotsvals kb fred (term "((== (a)))"))
        eqs (frame/add-slotsvals (:kb eq) fred (term "((== (b)))"))]
    (is (= (term "(red)") (:value (frame/get-vals (:kb twice) fred color))))
    (is (= (term "(red (<> 23))")
           (:value (frame/get-vals (:kb constrained) fred color))))
    (is (= (term "(((_Dog1) && ((a Dog))))")
           (:value (frame/get-vals (:kb both) fred (sym "owns")))))
    (is (= (term "(a b)") (:value (frame/get-vals (:kb eqs) fred (sym "==")))))))

(deftest self-is-replaced-on-an-own-facet-and-domain-uses-the-original-pair
  (let [own (frame/add-slotsvals (quiet) fred (term "((likes ('(Self))))"))
        member (frame/add-slotsvals (quiet) fred (term "((likes ('(Self))))")
                                    :facet (sym "member-properties"))
        declared (frame/add-slotsvals (frame/knowledge-base) loves
                                      (term "((domain (Self)))"))]
    (is (= (term "('(Fred))")
           (:value (frame/get-vals (:kb own) fred (sym "likes")))))
    (is (= (term "('(Self))")
           (:value (frame/get-vals (:kb member) fred (sym "likes")
                                   :facet (sym "member-properties")))))
    (is (= (term "(loves)")
           (:value (frame/get-vals (:kb declared) loves (sym "domain")))))
    (is (= (term "(Self)")
           (:value (frame/get-vals (:kb declared) (sym "loves-of") (sym "range")
                                   :situation term/global-situation))))))

(deftest domain-and-range-are-copied-onto-the-inverse
  (let [stored (frame/add-slotsvals (frame/knowledge-base) loves
                                    (term "((domain (Person)) (range (Person)))"))
        kb (:kb stored)]
    (is (= (term "(Person)")
           (:value (frame/get-vals kb (sym "loves-of") (sym "range")
                                   :situation term/global-situation))))
    (is (= (term "(Person)")
           (:value (frame/get-vals kb (sym "loves-of") (sym "domain")
                                   :situation term/global-situation))))
    (is (= (term "(loves loves-of)")
           (:value (frame/get-vals kb (sym "Person") (sym "domain-of")))))
    (is (= (term "(loves loves-of)")
           (:value (frame/get-vals kb (sym "Person") (sym "range-of")))))))

(deftest overwriting-removes-the-old-inverse
  (let [stored (frame/add-slotsvals (frame/knowledge-base) fred (term "((loves (Sue)))"))
        replaced (frame/add-slotsvals (:kb stored) fred (term "((loves (Mary)))")
                                      :combine-values-by (sym "overwriting"))]
    (is (= (term "(Mary)") (:value (frame/get-vals (:kb replaced) fred loves))))
    (is (nil? (:value (frame/get-vals (:kb replaced) sue (sym "loves-of")))))
    (is (= (term "(Fred)")
           (:value (frame/get-vals (:kb replaced) (sym "Mary") (sym "loves-of"))))))
  (let [kb (:kb (frame/put-vals (frame/knowledge-base) (sym "wife-of") (sym "cardinality")
                                (term "(N-to-1)")))
        y (sym "Y")
        z (sym "Z")
        x (sym "X")
        wife (sym "wife")
        kb (:kb (frame/put-vals kb z wife (term "(Y)")))
        replaced (frame/add-slotsvals kb x (term "((wife (Y)))")
                                      :combine-values-by (sym "overwriting"))]
    (is (= (term "(Y)") (:value (frame/get-vals (:kb replaced) x wife))))
    (is (= (term "(X)") (:value (frame/get-vals (:kb replaced) y (sym "wife-of")))))
    (is (nil? (:value (frame/get-vals (:kb replaced) z wife))))))

(deftest a-double-ampersand-value-grows-on-its-last-value-list
  (let [values (term "((red) && (blue))")
        kb (:kb (frame/put-vals (quiet) fred color values))
        present (frame/add-val kb fred color (term "(blue)"))
        added (frame/add-val kb fred color (sym "green"))]
    (is (= (term "((blue))") (:value present)))
    (is (= values (:value (frame/get-vals (:kb present) fred color))))
    (is (= (term "((red) && (blue) green)")
           (:value (frame/get-vals (:kb added) fred color))))))

(deftest create-instance-name-counts-and-skips-a-known-name
  (let [kb (frame/knowledge-base)
        one (frame/create-instance-name kb (sym "Person"))
        two (frame/create-instance-name (:kb one) (sym "Person"))]
    (is (= (sym "_Person1") (:value one)))
    (is (= (sym "_Person2") (:value two)))
    (is (= 2 (frame/gensym-counter (:kb two))))
    (is (not (frame/known-frame? (:kb two) (sym "_Person1")))))
  (let [kb (:kb (frame/put-vals (quiet) (sym "_Person1") color (term "(red)")))
        made (frame/create-instance-name kb (sym "Person"))]
    (is (= (sym "_Person2") (:value made)))
    (is (= 2 (frame/gensym-counter (:kb made))))))

(deftest delete-removes-the-value-and-the-inverse
  (let [kb (:kb (frame/put-vals (frame/knowledge-base) fred color (term "(red)")))
        missing (frame/delete-val kb fred color (sym "blue"))
        stored (frame/put-vals (frame/knowledge-base) fred loves (term "(Sue)"))
        gone (frame/delete-val (:kb stored) fred loves sue)]
    (is (nil? (:value missing)))
    (is (:message missing))
    (is (= (term "(red)") (:value (frame/get-vals (:kb missing) fred color))))
    (is (true? (:value gone)))
    (is (nil? (:value (frame/get-vals (:kb gone) fred loves))))
    (is (nil? (:value (frame/get-vals (:kb gone) sue (sym "loves-of")))))
    (is (frame/known-frame? (:kb gone) sue)))
  (let [kb (:kb (frame/add-val (quiet) fred (sym "age") 1))
        kb (:kb (frame/add-val kb fred (sym "age") 1.0))
        missed (frame/delete-val kb fred (sym "age") 1.0)
        gone (frame/delete-val kb fred (sym "age") 1)]
    (is (nil? (:value missed)))
    (is (= (term/km-list 1 1.0) (:value (frame/get-vals (:kb missed) fred (sym "age")))))
    (is (nil? (:value (frame/get-vals (:kb gone) fred (sym "age"))))))
  (is (thrown? clojure.lang.ExceptionInfo
               (frame/delete-frame (frame/knowledge-base) (sym "Missing"))))
  (let [stored (frame/put-vals (frame/knowledge-base) fred loves (term "(Sue)"))
        gone (frame/delete-frame (:kb stored) fred :query (:query stored))
        kb (:kb gone)]
    (is (true? (:value gone)))
    (is (not (frame/known-frame? kb fred)))
    (is (= [fred] (vec (frame/deleted-frames kb))))
    (is (nil? (:value (frame/get-vals kb sue (sym "loves-of")))))
    (is (not (utils/member? fred (:obj-stack (:query gone))))))
  (let [sit (sym "Sit1")
        kb (frame/set-situation (frame/knowledge-base) sit)
        kb (:kb (frame/put-vals kb sit color (term "(red)")))
        gone (:kb (frame/delete-frame kb sit))]
    (is (= [term/global-situation sit] (vec (frame/situations gone))))
    (is (not (frame/known-frame? gone sit)))))

(deftest the-active-stack-records-the-last-value-at-the-front
  (let [kb (-> (frame/knowledge-base)
               (frame/set-installing-inverses false)
               (frame/set-active-obj-stack true))
        stored (frame/put-vals kb fred color (term "(red blue)"))
        again (frame/put-vals (:kb stored) fred color (term "(red blue)")
                              :query (:query stored))]
    (is (= (term "(blue red Fred)") (:obj-stack (:query stored))))
    (is (= (:obj-stack (:query stored)) (:obj-stack (:query again))))
    (is (not (frame/known-frame? (:kb stored) (sym "red")))))
  (let [once (frame/put-vals (quiet) fred color (term "(red blue)"))
        again (frame/put-vals (frame/set-active-obj-stack (:kb once) true)
                              fred color (term "(red blue)")
                              :query (:query once))]
    (is (= (term "(Fred)") (:obj-stack (:query once))))
    (is (= (term "(blue red Fred)") (:obj-stack (:query again))))
    (is (= (term "(red blue)") (:value (frame/get-vals (:kb again) fred color))))))

(deftest several-frames-contribute-one-value-list
  (let [kb (:kb (frame/put-vals (quiet) fred color (term "(red blue)")))
        kb (:kb (frame/put-vals kb sue color (term "(blue green)")))
        got (frame/gets-vals kb (term "(Fred Sue)") color)]
    (is (= (term "(red blue green)") (:value got))))
  (let [stored (frame/put-vals (quiet) fred color (term "(red blue)"))
        several (frame/get-unique-val (:kb stored) fred color)
        none (frame/get-unique-val (quiet) fred color)]
    (is (= (sym "red") (:value several)))
    (is (:message several))
    (is (nil? (:value none)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (frame/get-unique-val (quiet) fred color :fail-mode :error)))))

(deftest a-bad-name-is-an-error-and-evaluate-stores-a-slot
  (let [kb (frame/knowledge-base)]
    (is (thrown? clojure.lang.ExceptionInfo (frame/get-vals kb fred 1)))
    (is (thrown? clojure.lang.ExceptionInfo (frame/put-vals kb 1 color (term "(red)"))))
    (is (thrown? clojure.lang.ExceptionInfo (frame/known-frame? kb 1)))
    (is (thrown? clojure.lang.ExceptionInfo (frame/put-vals kb :set color (term "(red)"))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (frame/curr-situation-facet kb (sym "no-such-facet") term/global-situation))))
  (let [result (engine/evaluate "(Fred has (color (red)))")]
    (is (:ok result))
    (is (= (term "(Fred)") (:value result)))
    (is (= (term "(red)") (:value (frame/get-vals (:kb result) fred color))))
    (is (= "interpreter" (:evaluator (engine/status)))))
  (let [result (engine/evaluate "(reset-kb)")]
    (is (:ok result))
    (is (= (term "(t)") (:value result)))
    (is (frame/known-frame? (:kb result) (sym "Thing")))))

(defn- started
  []
  (:kb (engine/reset (frame/knowledge-base))))

(deftest a-fresh-base-has-flags-and-no-vocabulary-frames
  (let [kb (frame/knowledge-base)]
    (is (= (sym "*Fluent") (frame/default-fluent-status kb)))
    (is (not (frame/instance-of-is-fluent? kb)))
    (is (not (frame/are-some? kb :definitions)))
    (is (not (frame/are-some? kb :prototypes)))
    (is (not (frame/are-some? kb :constraints)))
    (is (not (frame/are-some? kb :subslots)))
    (is (not (frame/are-some? kb :defaults)))
    (is (frame/classification-enabled? kb))
    (is (not (frame/known-frame? kb (sym "Thing"))))
    (is (= 0 (:max-padding-instances (frame/runtime kb))))
    (is (nil? (:curr-prototype (frame/runtime kb))))))

(deftest reset-rebuilds-the-vocabulary-and-clears-user-frames
  (let [sit (sym "_Sit1")
        kb (-> (frame/knowledge-base)
               (frame/set-dereferencing false)
               (frame/set-installing-inverses false)
               (frame/set-situation sit)
               (frame/set-situation (sym "T1") :theory? true)
               (frame/set-default-fluent-status (sym "*Non-Fluent"))
               (frame/set-instance-of-is-fluent true)
               (frame/set-are-some :constraints true)
               (frame/set-classification false))
        kb (:kb (frame/put-vals kb fred color (term "(red)")))
        kb (:kb (frame/km-bind kb (sym "_X") sue))
        named (frame/create-instance-name kb (sym "Person"))
        gone (frame/delete-frame (:kb named) fred :query (:query named))
        rebuilt (engine/reset (:kb gone) :query (:query gone))]
    (is (true? (:value rebuilt)))
    (is (nil? (:obj-stack (:query rebuilt))))
    (is (nil? (:goal-stack (:query rebuilt))))
    (is (= 0 (frame/gensym-counter (:kb rebuilt))))
    (is (= term/global-situation (frame/current-situation (:kb rebuilt))))
    (is (= [term/global-situation] (vec (frame/situations (:kb rebuilt)))))
    (is (= [] (vec (frame/theories (:kb rebuilt)))))
    (is (not (frame/dereferencing-on? (:kb rebuilt))))
    (is (not (:installing-inverses? (:kb rebuilt))))
    (is (= (sym "*Fluent") (frame/default-fluent-status (:kb rebuilt))))
    (is (not (frame/instance-of-is-fluent? (:kb rebuilt))))
    (is (not (frame/are-some? (:kb rebuilt) :constraints)))
    (is (frame/classification-enabled? (:kb rebuilt)))
    (is (true? (:prototype-classification-enabled? (frame/runtime (:kb rebuilt)))))
    (is (not (frame/known-frame? (:kb rebuilt) fred)))
    (is (nil? (frame/get-binding (:kb rebuilt) (sym "_X"))))
    (is (= [fred] (vec (frame/deleted-frames (:kb rebuilt)))))
    (is (frame/known-frame? (:kb rebuilt) (sym "Thing")))
    (is (nil? (:value (frame/get-vals (:kb rebuilt) (sym "Thing") (sym "subclasses"))))))
  (let [quiet (engine/reset (frame/set-installing-inverses (frame/knowledge-base) false))
        stored (frame/put-vals (:kb quiet) fred loves (term "(Sue)"))]
    (is (not (frame/known-frame? (:kb stored) sue)))))

(deftest the-built-in-classes-are-frames-and-their-taxonomy-slots-stay-empty
  (let [kb (started)
        subclasses (fn [class-name] (:value (frame/get-vals kb (sym class-name) (sym "subclasses"))))
        superclasses (fn [class-name] (:value (frame/get-vals kb (sym class-name) (sym "superclasses"))))
        instance-of (fn [frame] (:value (frame/get-vals kb frame (sym "instance-of"))))]
    (is (= 131 (count (frame/objects kb))))
    (is (= (sym "Integer") (first (frame/objects kb))))
    (is (nil? (subclasses "Thing")))
    (is (nil? (superclasses "Thing")))
    (is (nil? (superclasses "Integer")))
    (is (nil? (superclasses "Number")))
    (is (nil? (subclasses "Number")))
    (is (nil? (subclasses "Sequence")))
    (is (nil? (superclasses "Aggregate")))
    (is (nil? (superclasses "Bag")))
    (is (nil? (superclasses "Pair")))
    (is (nil? (superclasses "Aggregation-Slot")))
    (is (nil? (superclasses "Set-Aggregation-Slot")))
    (is (= (term "(Slot)") (instance-of (sym "domain"))))
    (is (= (term "(Slot)") (instance-of (sym "cardinality"))))
    (is (= (term "(Slot)") (instance-of (sym "inverse"))))
    (is (= (term "(Slot)") (instance-of (sym "inverse2"))))
    (is (= (term "(Slot)") (instance-of (sym "inverse3"))))
    (is (= (term "(Bag-Aggregation-Slot)") (instance-of (sym "min"))))
    (is (= (term "(min max sum average difference product quotient)")
           (:value (frame/get-vals kb (sym "Bag-Aggregation-Slot") (sym "instances")))))
    (is (= (term "(first second third fourth fifth last unification set-unification append number)")
           (:value (frame/get-vals kb (sym "Set-Aggregation-Slot") (sym "instances")))))
    (is (= (sym "cardinality")
           (term/car (:value (frame/get-vals kb (sym "Slot") (sym "instances"))))))
    (is (utils/member? (sym ">")
                       (:value (frame/get-vals kb (sym "Slot") (sym "instances")))))
    (is (utils/member? (sym "domain")
                       (:value (frame/get-vals kb (sym "Slot") (sym "instances")))))
    (is (frame/simple-slot? kb (sym "domain")))
    (is (not (frame/simple-slot? kb (sym "first"))))
    (is (not (frame/simple-slot? kb (sym "min"))))
    (is (= (term "(Boolean)") (instance-of (sym "t"))))
    (is (= (term "(Boolean)") (instance-of (sym "f"))))
    (is (= (term "(t f)")
           (:value (frame/get-vals kb (sym "Boolean") (sym "instances")))))
    (is (= (term "(Fluent-Status)") (instance-of (sym "*Fluent"))))
    (is (= (term "(*Fluent *Non-Fluent *Inertial-Fluent)")
           (:value (frame/get-vals kb (sym "Fluent-Status") (sym "instances")))))
    (is (= (term "(Situation)") (instance-of term/global-situation)))
    (is (frame/known-frame? kb (sym "1-to-N")))
    (is (nil? (instance-of (sym "1-to-N"))))
    (is (frame/known-frame? kb (sym "T")))
    (is (nil? (instance-of (sym "T"))))
    (is (frame/an-instance? kb (sym "t")))
    (is (not (frame/an-instance? kb (sym "T"))))
    (is (frame/known-frame? kb (term "/==")))
    (is (= (term "(Slot)") (instance-of (term "/=="))))
    (is (frame/known-frame? kb (sym "append")))
    (is (= (term "(Set-Aggregation-Slot)") (instance-of (sym "append"))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (frame/put-vals kb (sym "append") (sym "domain") (term "(Thing)"))))))

(deftest fluent-status-sends-non-fluents-to-the-global-situation
  (let [sit (sym "_Sit1")
        kb (frame/set-situation (started) sit)
        local (frame/put-vals kb fred color (term "(red)"))
        global (frame/put-vals kb fred (sym "superclasses") (term "(Person)"))
        declared (frame/put-vals (frame/knowledge-base) (sym "age") (sym "fluent-status")
                                 (term "(*Non-Fluent)"))
        aged (frame/put-vals (frame/set-situation (:kb declared) sit)
                             fred (sym "age") (term "(30)"))]
    (is (frame/fluent? kb color))
    (is (not (frame/fluent? kb (sym "superclasses"))))
    (is (= (sym "*Non-Fluent") (frame/fluent-status kb (sym "cardinality"))))
    (is (= (sym "*Inertial-Fluent") (frame/fluent-status kb (sym "nowexists"))))
    (is (= (sym "*Fluent") (frame/fluent-status kb (sym "add-list"))))
    (is (nil? (:value (frame/get-vals (:kb local) fred color :situation term/global-situation))))
    (is (= (term "(red)") (:value (frame/get-vals (:kb local) fred color))))
    (is (= (term "(Person)")
           (:value (frame/get-vals (:kb global) fred (sym "superclasses")
                                   :situation term/global-situation))))
    (is (nil? (:value (frame/get-vals (:kb global) fred (sym "superclasses")
                                      :situation sit))))
    (is (= (term "(30)")
           (:value (frame/get-vals (:kb aged) fred (sym "age")
                                   :situation term/global-situation))))
    (is (nil? (:value (frame/get-vals (:kb aged) fred (sym "age") :situation sit)))))
  (let [sit (sym "_Sit1")
        kb (-> (started)
               (frame/set-default-fluent-status (sym "*Non-Fluent"))
               (frame/set-situation sit))
        stored (frame/put-vals kb fred color (term "(red)"))]
    (is (not (frame/fluent? kb color)))
    (is (= (term "(red)")
           (:value (frame/get-vals (:kb stored) fred color :situation term/global-situation)))))
  (let [kb (frame/set-instance-of-is-fluent (started) true)]
    (is (= (sym "*Inertial-Fluent") (frame/fluent-status kb (sym "instance-of"))))
    (is (frame/inertial-fluent? kb (sym "instance-of"))))
  (let [sit (sym "_Sit1")
        kb (-> (started)
               (frame/set-instance-of-is-fluent true)
               (frame/set-situation sit))
        exact (frame/add-slotsvals kb (sym "_Sit2") (term "((instance-of (Situation)))"))
        other (frame/add-slotsvals kb fred (term "((instance-of (Dog)))"))
        put (frame/put-vals kb (sym "_Sit2") (sym "instance-of") (term "(Situation)"))
        child (frame/put-vals (frame/knowledge-base) (sym "MySit") (sym "superclasses")
                              (term "(Situation)"))
        nested (frame/add-slotsvals (frame/set-situation
                                     (frame/set-instance-of-is-fluent (:kb child) true)
                                     sit)
                                    (sym "_Sit2")
                                    (term "((instance-of (MySit)))"))]
    (is (= (term "(Situation)")
           (:value (frame/get-vals (:kb exact) (sym "_Sit2") (sym "instance-of")
                                   :situation term/global-situation))))
    (is (nil? (:value (frame/get-vals (:kb exact) (sym "_Sit2") (sym "instance-of")
                                      :situation sit))))
    (is (= (term "(Dog)")
           (:value (frame/get-vals (:kb other) fred (sym "instance-of") :situation sit))))
    (is (= (term "(Situation)")
           (:value (frame/get-vals (:kb put) (sym "_Sit2") (sym "instance-of") :situation sit))))
    (is (nil? (:value (frame/get-vals (:kb put) (sym "_Sit2") (sym "instance-of")
                                      :situation term/global-situation))))
    (is (= (term "(MySit)")
           (:value (frame/get-vals (:kb nested) (sym "_Sit2") (sym "instance-of")
                                   :situation sit)))))
  (is (thrown? clojure.lang.ExceptionInfo
               (frame/set-default-fluent-status (frame/knowledge-base) (sym "Sometimes"))))
  (is (thrown? clojure.lang.ExceptionInfo
               (frame/are-some? (frame/knowledge-base) :nope)))
  (let [kb (:kb (frame/put-vals (frame/knowledge-base) (sym "age") (sym "fluent-status")
                                (term "(*Non-Fluent)")))
        kb (:kb (frame/put-vals kb (sym "age-of") (sym "fluent-status")
                                (term "(*Fluent)")))]
    (is (thrown? clojure.lang.ExceptionInfo (frame/fluent-status kb (sym "age"))))))
