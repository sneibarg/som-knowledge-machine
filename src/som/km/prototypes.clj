(ns som.km.prototypes
  "Prototypes, from prototypes.lisp and the first slot-value source.

  (a-prototype Class) builds a root named with _Proto, records
  prototype-of and prototype-scope, and adds the root to its own
  prototype-participants. While that prototype is being built, (a Class)
  creates another participant. (end-prototype) leaves the mode.
  A later slot read clones the participant graph onto an ordinary
  instance and unifies the clone with &!. A slotted prototype-scope is
  tested when the instance is not already one of the prototype's
  classes. The caller classifies a new instance.

  (a Class) outside prototype mode creates an ordinary instance.
  This namespace does not require the interpreter or the slot reader.
  Both are passed in when a clone has to evaluate something."
  (:require [som.km.classify :as classify]
            [som.km.errors :as errors]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.print :as print]
            [som.km.stack :as stack]
            [som.km.taxonomy :as taxonomy]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(def slots-not-to-clone-for
  "Slots a read does not clone a prototype to fill.

  instance-of is still copied onto the clone. It is not given a
  cloned-from explanation, and reading it does not start a clone."
  (set (map symbol ["prototype-participant-of" "prototype-participants"
                    "prototypes" "prototype-of" "instance-of" "cloned-from"
                    "has-clones" "clone-built-from" "has-built-clones"])))

(def ^:private unclonable-slots
  (set (map symbol ["prototype-participant-of" "prototype-participants"
                    "prototype-of" "prototypes" "prototype-scope"
                    "locked-instance-of" "has-clones" "has-built-clones"])))

(def ^:private nonparticipant-slots
  (set (map symbol ["cloned-from" "clone-built-from"
                    "has-clones" "has-built-clones"])))

(def ^:private proto-prefix "_Proto")

(defn clones-for?
  "True when a read of slot may clone a prototype."
  [slot]
  (not (contains? slots-not-to-clone-for slot)))

(defn- refused?
  [state]
  (= "not-ported" (:error state)))

(defn- adopt
  "Take the knowledge base and the notes a store call recorded.

  An empty error vector is a real value. It replaces the previous notes."
  [state stored]
  (cond-> (assoc state
                 :kb (:kb stored)
                 :query (or (:query stored) (:query state)))
    (contains? stored :errors) (assoc :errors (vec (:errors stored)))
    (contains? stored :warnings) (assoc :warnings (vec (:warnings stored)))
    (contains? stored :error-structures)
    (assoc :error-structures (vec (:error-structures stored)))
    (contains? stored :error)
    (assoc :error (:error stored) :message (:message stored) :value nil)))

(defn- user-error
  [state template & args]
  (-> (apply errors/report-error state :user-error template args)
      (assoc :value nil)))

(defn- flag
  [kb key not-found]
  (get (:runtime kb) key not-found))

(defn- nth-value
  [value n]
  (loop [value value
         n n]
    (cond
      (or (nil? value) (not (term/cons? value))) nil
      (zero? n) (term/car value)
      :else (recur (term/cdr value) (dec n)))))

(defn- prototype?
  [kb frame]
  (and (kb/kb-object? frame)
       (some? (:value (frame/get-vals kb frame (symbol "prototype-of")
                                      :situation term/global-situation
                                      :dereference? false)))))

(defn- in-list?
  "True when item is in a vector or a Knowledge Machine list."
  [item values]
  (cond
    (nil? values) false
    (vector? values) (some #(utils/eql? item %) values)
    :else (utils/member? item values)))

(defn- local-situation?
  "True in a situation that is not *Global and not a theory."
  [kb]
  (let [situation (frame/current-situation kb)]
    (and (not (utils/eql? situation term/global-situation))
         (not (in-list? situation (frame/theories kb))))))

(defn- local-theory?
  "True when the current situation is one of the entered theories.

  No theory is entered until situations land. The store still does not
  treat a situation as a theory by itself."
  [kb]
  (let [situation (frame/current-situation kb)]
    (and (not (utils/eql? situation term/global-situation))
         (in-list? situation (frame/theories kb)))))

(defn- prototype-expr
  [class slotsvals]
  (term/build-list [(symbol "a-prototype") class (symbol "with")] slotsvals))

(defn reject-prototype-entry
  "The user error that blocks prototype mode, or nil when entry may proceed.

  A local situation, a theory, and a prototype that is already open are
  the three blocks. The Lisp misspells the stored definition. The
  message here keeps the expression that was evaluated."
  [state class slotsvals]
  (let [kb (:kb state)]
    (cond
      (local-situation? kb)
      (user-error state "Can't enter prototype mode when in a Situation!")
      (local-theory? kb)
      (user-error state "Can't enter prototype mode when in a Theory!")
      (some? (frame/curr-prototype kb))
      (user-error state
                  "%s%nAttempt to enter prototype mode while already in prototype mode (not allowed)!%nPerhaps you are missing an (end-prototype)?"
                  (print/km-format (prototype-expr class slotsvals)))
      :else nil)))

(defn- extra-classes
  [slotsvals]
  (loop [pairs slotsvals
         acc []]
    (cond
      (or (nil? pairs) (not (term/cons? pairs))) acc
      :else
      (let [pair (term/car pairs)]
        (if (and (term/cons? pair)
                 (utils/eql? (symbol "instance-of") (term/car pair))
                 (utils/lisp-list? (nth-value pair 1)))
          (recur (term/cdr pairs) (into acc (utils/elements (nth-value pair 1))))
          (recur (term/cdr pairs) acc))))))

(defn- without-slot
  [slotsvals slot]
  (loop [pairs slotsvals
         acc []]
    (cond
      (nil? pairs) (term/build-list acc nil)
      (not (term/cons? pairs)) pairs
      (and (term/cons? (term/car pairs))
           (utils/eql? slot (term/car (term/car pairs))))
      (recur (term/cdr pairs) acc)
      :else (recur (term/cdr pairs) (conj acc (term/car pairs))))))

(defn- with-class
  "Put parent on instance-of and keep the other pairs."
  [slotsvals parent]
  (let [classes (into [parent] (extra-classes slotsvals))
        unique (loop [pending classes
                      acc []]
                 (if (empty? pending)
                   acc
                   (recur (next pending)
                          (if (some #(utils/eql? (first pending) %) acc)
                            acc
                            (conj acc (first pending))))))]
    (term/cons-cell
     (term/km-list (symbol "instance-of") (term/build-list unique nil))
     (without-slot slotsvals (symbol "instance-of")))))

(defn- class-of-description
  [expr]
  (when (and (kb/the-class? expr) (term/cons? (term/cdr expr)))
    (term/car (term/cdr expr))))

(defn create-instance
  "Create one anonymous instance of class and return it as :value.

  prefix defaults to _Proto while a prototype is being built, and to _
  otherwise. bind-self? replaces Self. The root is created before
  prototype mode is on, so this does not add that root as a participant.
  A participant created while mode is on is linked to the current
  prototype. The caller classifies. The assertions slot is not run."
  [state class slotsvals & {:keys [prefix bind-self?] :or {bind-self? true}}]
  (let [described (class-of-description class)
        parent (or described class)
        extra (when (and described (term/cons? (term/cdr (term/cdr class))))
                (let [after (term/cdr (term/cdr class))]
                  (if (utils/eql? (symbol "with") (term/car after))
                    (term/cdr after)
                    nil)))
        slotsvals (if extra (term/build-list (utils/elements slotsvals) extra) slotsvals)
        prefix (or prefix
                   (if (some? (frame/curr-prototype (:kb state))) proto-prefix "_"))]
    (cond
      (not (kb/kb-object? parent))
      (user-error state
                  "Class name must be a symbol or class description! (was %s)"
                  (print/km-format class))
      :else
      (let [named (frame/create-instance-name (:kb state) parent
                                              :prefix prefix
                                              :query (:query state))
            named (update named :query #(update % :skolems (fnil inc 0)))
            instance (:value named)
            stored (frame/add-slotsvals (:kb named) instance (with-class slotsvals parent)
                                        :bind-self? bind-self?
                                        :query (:query named)
                                        :errors (:errors state)
                                        :warnings (:warnings state)
                                        :error-structures (:error-structures state))]
        (if (refused? stored)
          stored
          (let [linked (if-let [root (frame/curr-prototype (:kb stored))]
                         (frame/add-val (:kb stored) instance
                                        (symbol "prototype-participant-of") root
                                        :situation term/global-situation
                                        :query (:query stored))
                         stored)
                kb (frame/un-done (:kb linked) instance)]
            (assoc (adopt state linked)
                   :kb kb
                   :query (:query linked)
                   :value instance)))))))

(defn- scope-pair
  [class slotsvals]
  (if (nil? slotsvals)
    (term/km-list (symbol "prototype-scope") (term/km-list class))
    (term/km-list (symbol "prototype-scope")
                  (term/km-list
                   (term/build-list [(symbol "the-class") class (symbol "with")]
                                    slotsvals)))))

(defn- prototype-slots
  [class slotsvals]
  (term/build-list [(term/km-list (symbol "prototype-of") (term/km-list class))
                    (scope-pair class slotsvals)]
                   slotsvals))

(defn- definition-expr
  "The expression stored on the prototype. The Lisp writes a-prototoype when there are no slots."
  [class slotsvals]
  (if (nil? slotsvals)
    (term/km-list (symbol "a-prototype") class)
    (term/build-list [(symbol "a-prototype") class (symbol "with")] slotsvals)))

(defn enter-prototype
  "Create the prototype root and enter prototype mode.

  The caller has already checked the situation and the slot pairs.
  The root is named with _Proto. Self inside the scope is left as Self.
  The root is added to its own prototype-participants after it exists,
  because prototype mode is still off during the create."
  [state class slotsvals]
  (let [cleared (stack/new-context (:query state))
        state (assoc state :query (:query cleared))
        created (create-instance state class (prototype-slots class slotsvals)
                                 :prefix proto-prefix
                                 :bind-self? false)]
    (cond
      (refused? created) created
      (nil? (:value created)) created
      :else
      (let [root (:value created)
            linked (frame/add-val (:kb created) root
                                  (symbol "prototype-participants") root
                                  :situation term/global-situation
                                  :query (:query created))
            kb (-> (:kb linked)
                   (frame/set-are-some :prototypes true)
                   (frame/set-curr-prototype root)
                   (frame/add-definition root (definition-expr class slotsvals)))]
        (assoc (adopt state linked)
               :kb kb
               :query (:query linked)
               :value (term/km-list root))))))

(defn end-prototype
  "Leave prototype mode, return to *Global, and clear the object stack.

  The answer is (t). Leaving a mode that is already off does the same."
  [state]
  (let [kb (-> (:kb state)
               (frame/set-curr-prototype nil)
               (frame/set-situation term/global-situation))
        cleared (stack/new-context (:query state))]
    (assoc state
           :kb kb
           :query (:query cleared)
           :value (term/km-list (symbol "t")))))

(defn- says?
  "True when prototype has a value for slot or one of its subslots."
  [state prototype slot]
  (let [situation (frame/target-situation (:kb state)
                                          (frame/current-situation (:kb state))
                                          prototype slot)
        subs (taxonomy/all-subslots (:kb state) slot)
        state (adopt state subs)]
    (loop [rest (term/cons-cell slot (:value subs))
           state state]
      (cond
        (or (nil? rest) (not (term/cons? rest))) [state false]
        :else
        (let [found (frame/get-vals (:kb state) prototype (term/car rest)
                                    :situation situation
                                    :dereference? false
                                    :query (:query state))]
          (if (some? (:value found))
            [(adopt state found) true]
            (recur (term/cdr rest) (adopt state found))))))))

(defn- closure
  "The transitive values of slot, without the starting frame."
  [kb frame slot]
  (let [direct (frame/get-vals kb frame slot
                               :situation term/global-situation
                               :dereference? false)]
    (loop [agenda (vec (utils/elements (:value direct)))
           kb (:kb direct)
           seen #{}
           acc []]
      (if (empty? agenda)
        {:kb kb :value acc}
        (let [item (first agenda)]
          (if (or (not (kb/kb-object? item)) (contains? seen item))
            (recur (rest agenda) kb seen acc)
            (let [found (frame/get-vals kb item slot
                                        :situation term/global-situation
                                        :dereference? false)]
              (recur (into (vec (rest agenda)) (utils/elements (:value found)))
                     (:kb found)
                     (conj seen item)
                     (conj acc item)))))))))

(defn- matches-protoclass?
  "True when the prototype applies to instance.

  A stored member succeeds before the description is tested. While
  that instance is already being classified, the description is not
  tested again."
  [state instance prototype km-int]
  (classify/prototype-fits? state instance prototype km-int))

(defn- suitable?
  [state instance slot prototype km-int]
  (cond
    (or (utils/eql? instance prototype)
        (not (prototype? (:kb state) prototype))
        (utils/eql? prototype (frame/curr-prototype (:kb state))))
    [state false]
    :else
    (let [[state speaks?] (if (some? slot)
                            (says? state prototype slot)
                            [state true])]
      (if-not speaks?
        [state false]
        (let [closed (closure (:kb state) instance (symbol "clone-built-from"))
              state (assoc state :kb (:kb closed))]
          (if (some #(utils/eql? prototype %) (:value closed))
            [state false]
            (matches-protoclass? state instance prototype km-int)))))))

(defn- applicable
  "Prototypes worth cloning, in class order and then storage order.

  Thing is visited first. A class's prototypes stay in the order they
  were stored. The knowledge base from each suitability test is kept."
  [state instance slot km-int]
  (let [classes (taxonomy/all-classes (:kb state) instance)
        state (adopt state classes)]
    (loop [rest (:value classes)
           state state
           acc []]
      (if (or (nil? rest) (not (term/cons? rest)))
        [state acc]
        (let [[state acc]
              (loop [protos (frame/defined-prototypes (:kb state)
                                                      (term/car rest))
                     state state
                     acc acc]
                (if (or (nil? protos) (not (term/cons? protos)))
                  [state acc]
                  (let [[state fits?] (suitable? state instance slot
                                                       (term/car protos) km-int)]
                    (recur (term/cdr protos)
                           state
                           (if fits? (conj acc (term/car protos)) acc)))))]
          (recur (term/cdr rest) state acc))))))

(defn- eager?
  [kb]
  (get (:runtime kb) :eagerly-unify-prototypes? true))

(defn- recording?
  [kb]
  (or (flag kb :record-explanations? true)
      (flag kb :record-explanations-for-clones? true)))

(defn- translate
  [mapping value]
  (cond
    (term/cons? value)
    (let [head (translate mapping (term/car value))
          tail (translate mapping (term/cdr value))]
      (if (and (identical? head (term/car value))
               (identical? tail (term/cdr value)))
        value
        (term/cons-cell head tail)))
    :else
    (loop [mapping mapping]
      (cond
        (empty? mapping) value
        (utils/eql? (ffirst mapping) value) (second (first mapping))
        :else (recur (rest mapping))))))

(defn- mapped?
  [mapping value]
  (some #(utils/eql? value (first %)) mapping))

(defn- outside-values
  [slot values mapping]
  (loop [values values
         acc []]
    (cond
      (nil? values)
      (when (seq acc)
        (frame/make-slotvals slot (term/build-list acc nil)))
      (not (term/cons? values)) nil
      (mapped? mapping (term/car values)) (recur (term/cdr values) acc)
      :else (recur (term/cdr values) (conj acc (term/car values))))))

(defn- clonable-slots
  [slotsvals mapping]
  (loop [pairs slotsvals
         acc []]
    (cond
      (nil? pairs) (when (seq acc) (term/build-list acc nil))
      (not (term/cons? pairs)) nil
      :else
      (let [pair (term/car pairs)
            slot (frame/slot-in pair)
            kept (cond
                   (contains? unclonable-slots slot) nil
                   (contains? nonparticipant-slots slot)
                   (outside-values slot (frame/vals-in pair) mapping)
                   :else pair)]
        (recur (term/cdr pairs) (if (some? kept) (conj acc kept) acc))))))

(defn- pair-name
  [mapping prototype]
  (some (fn [[from to]] (when (utils/eql? from prototype) to)) mapping))

(defn- name-participants
  [kb participants query]
  (loop [rest participants
         kb kb
         mapping []]
    (cond
      (or (nil? rest) (not (term/cons? rest)))
      {:kb kb :mapping mapping}
      (frame/anonymous-instance? kb (term/car rest))
      (let [classes (taxonomy/immediate-classes kb (term/car rest))
            parent (or (term/car (:value classes)) (symbol "Thing"))
            named (frame/create-instance-name (:kb classes) parent
                                              :prefix "_"
                                              :query query)]
        (recur (term/cdr rest)
               (:kb named)
               (conj mapping [(term/car rest) (:value named)])))
      :else
      (recur (term/cdr rest)
             kb
             (conj mapping [(term/car rest) (term/car rest)])))))

(defn- build-one
  "The copied slots for one anonymous participant.

  :kb is the knowledge base after the read. :clone and :slots are
  present only when that participant is slot-copied. A named
  participant maps to itself and contributes no slots."
  [kb prototype mapping]
  (if-not (frame/anonymous-instance? kb prototype)
    {:kb kb}
    (let [found (frame/get-slotsvals kb prototype
                                     :situation term/global-situation
                                     :dereference? false)
          kept (clonable-slots (:value found) mapping)
          clone (pair-name mapping prototype)]
      (if (and (some? kept) (some? clone))
        {:kb (:kb found)
         :clone clone
         :slots (translate mapping kept)}
        {:kb (:kb found)}))))

(defn- record-fresh
  [kb clone slotsvals prototype clone-root participant]
  (if-not (recording? kb)
    kb
    (loop [pairs slotsvals
           kb kb]
      (cond
        (or (nil? pairs) (not (term/cons? pairs))) kb
        :else
        (let [pair (term/car pairs)
              slot (frame/slot-in pair)]
          (if (or (contains? #{(symbol "cloned-from") (symbol "clone-built-from")
                              (symbol "instance-of")}
                             slot))
            (recur (term/cdr pairs) kb)
            (recur (term/cdr pairs)
                   (loop [vals (frame/vals-in pair)
                          kb kb]
                     (if (or (nil? vals) (not (term/cons? vals)))
                       kb
                       (recur (term/cdr vals)
                              (frame/record-explanation
                               kb clone
                               (term/km-list
                                clone slot (term/car vals)
                                (term/km-list (symbol "cloned-from")
                                              prototype clone-root participant)))))))))))))

(defn- copied-instance-of?
  [kb record]
  (let [instance (term/car record)
        slot (nth-value record 1)
        value (nth-value record 2)
        explanation (nth-value record 3)]
    (and (utils/eql? slot (symbol "instance-of"))
         (or (and (term/cons? explanation)
                  (utils/eql? (term/car explanation) (symbol "cloned-from")))
             (and (term/cons? explanation)
                  (utils/eql? (term/car explanation) (symbol "a")))
             (not (utils/member?
                   value
                   (:value (frame/get-vals kb instance (symbol "instance-of")
                                           :situation term/global-situation
                                           :dereference? false))))))))

(defn- clone-cycle?
  "A cloned-from explanation whose second element is not a prototype.

  During a load the clone may not be marked a prototype yet (HLO-1859).
  The Lisp comment says the check is suppressed while loading. The code
  does not look at a load flag, so this check runs during a load too."
  [kb explanation]
  (and (term/cons? explanation)
       (utils/eql? (term/car explanation) (symbol "cloned-from"))
       (not (prototype? kb (nth-value explanation 1)))))

(defn- copy-explanations
  [kb mapping]
  (reduce (fn [kb [participant clone]]
            (reduce (fn [kb record]
                      (if (copied-instance-of? kb record)
                        kb
                        (let [translated (translate mapping record)]
                          (if (clone-cycle? kb (nth-value translated 3))
                            kb
                            (frame/record-explanation kb clone translated)))))
                    kb
                    (utils/elements (frame/explanations kb participant))))
          kb
          mapping))

(defn- link-cloned-from
  [state mapping]
  (if-not (flag (:kb state) :add-cloned-from-links? true)
    state
    (reduce (fn [state [participant clone]]
              (let [linked (frame/add-val (:kb state) clone (symbol "cloned-from")
                                          participant
                                          :situation term/global-situation
                                          :query (:query state))]
                (adopt state linked)))
            state
            mapping)))

(defn- install-clones
  "Store each copied slot list. Classification stays off for the write.

  The two flags return to the values they had, including when a write
  is refused or aborts. Nothing in the write reads those flags."
  [state clones mapping prototype clone-root]
  (let [class? (frame/classification-enabled? (:kb state))
        proto-class? (flag (:kb state) :prototype-classification-enabled? true)
        restore (fn [kb]
                  (-> kb
                      (assoc-in [:runtime :classification-enabled?] class?)
                      (assoc-in [:runtime :prototype-classification-enabled?] proto-class?)))
        state (update state :kb
                      #(-> %
                           (assoc-in [:runtime :classification-enabled?] false)
                           (assoc-in [:runtime :prototype-classification-enabled?] false)))
        finish (fn [done] (update done :kb restore))]
    (try
      (finish
       (loop [clones clones
              state state]
         (cond
           (refused? state) state
           (empty? clones) state
           :else
           (let [{:keys [clone slots]} (first clones)
                 participant (some (fn [[from to]] (when (utils/eql? to clone) from)) mapping)
                 stored (frame/add-slotsvals (:kb state) clone slots
                                             :query (:query state)
                                             :errors (:errors state)
                                             :warnings (:warnings state)
                                             :error-structures (:error-structures state))]
             (if (refused? stored)
               (adopt state stored)
               (let [kb (record-fresh (:kb stored) clone slots
                                      prototype clone-root participant)
                     linked (if-let [root (frame/curr-prototype kb)]
                              (frame/add-val kb clone
                                             (symbol "prototype-participant-of") root
                                             :situation term/global-situation
                                             :query (:query stored))
                              stored)]
                 (recur (rest clones)
                        (assoc (adopt state linked)
                               :kb (if (identical? linked stored) kb (:kb linked))
                               :query (:query linked)))))))))
      (catch clojure.lang.ExceptionInfo thrown
        (if (errors/abort-exception? thrown)
          (let [data (ex-data thrown)]
            (throw (ex-info (.getMessage thrown)
                            (assoc data :state (finish (:state data)))
                            thrown)))
          (throw thrown))))))

(defn clone
  "Copy prototype's participant graph and return the clone of the root.

  Dereferencing is off while the graph is copied. Unclonable slots are
  left behind. instance-of is copied and is not explained. Named
  participants map to themselves and are not slot-copied. cloned-from
  links every participant to its clone. clone-built-from links the
  clone root to the prototype. The unify-with-clone-of goal is not
  pushed. The clone is not reclassified."
  [state prototype0]
  (let [was (frame/dereferencing-on? (:kb state))
        prototype (frame/dereference (:kb state) prototype0)
        state (assoc state :kb (frame/set-dereferencing (:kb state) false))
        restore (fn [done]
                  (assoc done :kb (frame/set-dereferencing (:kb done) was)))]
    (try
      (restore
       (cond
         (not (prototype? (:kb state) prototype))
         (user-error state "Attempt to clone a non-prototype %s!"
                     (print/km-format prototype))
         (and (flag (:kb state) :situations-mode? false)
              (utils/eql? (frame/current-situation (:kb state)) term/global-situation))
         (user-error state
                     "Attempt to clone a prototype %s in the global situation while using Situations -- not allowed!%nOnly do cloning in local situations when using KM Situations."
                     (print/km-format prototype))
         :else
         (let [participants (frame/get-vals (:kb state) prototype
                                            (symbol "prototype-participants")
                                            :situation term/global-situation
                                            :dereference? false
                                            :query (:query state))]
           (if (nil? (:value participants))
             (user-error (adopt state participants)
                         "(clone %s): No prototype-participants declared for this prototype!"
                         (print/km-format prototype))
             (let [named (name-participants (:kb participants) (:value participants)
                                            (:query participants))
                   mapping (:mapping named)
                   built (reduce (fn [acc participant]
                                   (conj acc (build-one (:kb (last acc))
                                                        participant mapping)))
                                 [{:kb (:kb named)}]
                                 (utils/elements (:value participants)))
                   copies (vec (filter :clone built))
                   clone-root (pair-name mapping prototype)
                   installed (install-clones
                              (assoc (adopt state participants)
                                     :kb (:kb (last built)))
                              copies mapping prototype clone-root)]
               (if (or (refused? installed) (nil? clone-root))
                 installed
                 (let [explained (if (and (recording? (:kb installed))
                                          (flag (:kb installed)
                                                :propagate-explanations? true))
                                   (let [on (frame/set-dereferencing
                                             (:kb installed)
                                             (flag (:kb installed)
                                                   :dereference-explanations-during-cloning?
                                                   true))
                                         copied (copy-explanations on mapping)]
                                     (frame/set-dereferencing copied false))
                                   (frame/set-dereferencing (:kb installed) false))
                       linked (link-cloned-from (assoc installed :kb explained) mapping)
                       rooted (frame/add-val (:kb linked) clone-root
                                             (symbol "clone-built-from") prototype
                                             :situation term/global-situation
                                             :query (:query linked))]
                   (assoc (adopt linked rooted) :value clone-root))))))))
      (catch clojure.lang.ExceptionInfo thrown
        (if (errors/abort-exception? thrown)
          (let [data (ex-data thrown)]
            (throw (ex-info (.getMessage thrown)
                            (assoc data :state (restore (:state data)))
                            thrown)))
          (throw thrown))))))

(defn- restore-partial
  [state previous]
  (assoc-in state [:query :partially-included-prototype] previous))

(defn- unify-one
  [state instance prototype km-int]
  (let [cloned (km-int state (term/km-list (symbol "clone") prototype) :fail-mode :error)]
    (cond
      (refused? cloned) cloned
      (not (term/singleton? (:value cloned))) cloned
      :else
      (let [clone-name (term/car (:value cloned))
            operator (if (eager? (:kb cloned)) (symbol "&!") (symbol "&"))
            closed (closure (:kb cloned) instance (symbol "cloned-from"))
            previous (get (:query cloned) :partially-included-prototype)
            partial? (some #(utils/eql? prototype %) (:value closed))
            marked (assoc cloned
                          :kb (:kb closed)
                          :query (assoc (or (:query cloned) {})
                                        :partially-included-prototype
                                        (if partial? prototype previous)))]
        (try
          (restore-partial
           (km-int marked
                   (term/km-list instance operator clone-name)
                   :fail-mode :error)
           previous)
          (catch clojure.lang.ExceptionInfo thrown
            (if (errors/abort-exception? thrown)
              (let [data (ex-data thrown)]
                (throw (ex-info (.getMessage thrown)
                                (assoc data :state (restore-partial (:state data) previous))
                                thrown)))
              (throw thrown))))))))

(defn- unify-all
  [state instance0 slot km-int]
  (let [instance (frame/dereference (:kb state) instance0)
        [state prototypes] (applicable state instance slot km-int)]
    (loop [prototypes prototypes
           state state]
      (cond
        (refused? state) state
        (empty? prototypes) state
        :else
        (let [prototype (first prototypes)
              instance (frame/dereference (:kb state) instance0)
              closed (closure (:kb state) instance (symbol "clone-built-from"))
              state (assoc state :kb (:kb closed))]
          (if (some #(utils/eql? prototype %) (:value closed))
            (recur (rest prototypes) state)
            (let [next (unify-one state instance prototype km-int)]
              (if (refused? next)
                next
                (recur (rest prototypes) next)))))))))

(defn unify-in-prototypes
  "Clone every suitable prototype onto instance.

  use-prototypes is the recursive flag for the duration, which starts
  false, so a nested slot read does not clone again. The previous flag
  is restored on the returned knowledge base and on an abort. The
  unify-with-clone-of goal is not pushed. A prototype already reached
  through clone-built-from is not unified again. A prototype reached
  through cloned-from, and not through clone-built-from, is unified
  again. For that pass the query records partially-included-prototype
  for the duration of the unify, then the previous value is restored.
  A user appending slot can then join values that share a cloned-from
  source. The binding is not stored on the knowledge base."
  [state instance slot km-int]
  (let [previous (get (:runtime (:kb state)) :use-prototypes? true)
        recursive (boolean (flag (:kb state) :recursive-prototypes? false))
        state (assoc-in state [:kb :runtime :use-prototypes?] recursive)
        restore (fn [current]
                  (assoc-in current [:kb :runtime :use-prototypes?] previous))]
    (try
      (restore (unify-all state instance slot km-int))
      (catch clojure.lang.ExceptionInfo thrown
        (if (errors/abort-exception? thrown)
          (let [data (ex-data thrown)]
            (throw (ex-info (.getMessage thrown)
                            (assoc data :state (restore (:state data)))
                            thrown)))
          (throw thrown))))))

(defn- path-value?
  [value]
  (and (not (kb/fully-evaluated? value))
       (not (kb/constraint-expr? value))))

(defn- needs-path?
  [values]
  (loop [values values]
    (cond
      (nil? values) false
      (not (term/cons? values)) false
      (path-value? (term/car values)) true
      :else (recur (term/cdr values)))))

(defn- simple-eval
  [state instance km-int]
  (let [found (frame/get-slotsvals (:kb state) instance
                                   :dereference? false
                                   :query (:query state))
        state (adopt state found)]
    (loop [pairs (:value found)
           state state]
      (cond
        (refused? state) state
        (or (nil? pairs) (not (term/cons? pairs))) state
        :else
        (let [pair (term/car pairs)]
          (if (needs-path? (frame/vals-in pair))
            (let [next (km-int state
                               (term/km-list (symbol "the") (frame/slot-in pair)
                                             (symbol "of") instance))]
              (if (refused? next)
                next
                (recur (term/cdr pairs) next)))
            (recur (term/cdr pairs) state)))))))

(defn- newcomers
  [before after]
  (loop [after after
         acc []]
    (cond
      (nil? after) (term/build-list acc nil)
      (not (term/cons? after)) (term/build-list acc nil)
      (utils/member? (term/car after) before) (recur (term/cdr after) acc)
      :else (recur (term/cdr after) (conj acc (term/car after))))))

(defn- expand
  [state instances depth km-int]
  (cond
    (or (nil? instances) (refused? state)) state
    (>= depth 100)
    (user-error state
                "eval-instances in frame-io.lisp!%nRecursion is causing an infinite graph to be generated! Giving up...")
    :else
    (let [before (frame/obj-stack (:kb state) (:query state))
          state (adopt state before)
          state (loop [rest instances
                       state state]
                  (cond
                    (refused? state) state
                    (or (nil? rest) (not (term/cons? rest))) state
                    :else (let [next (simple-eval state (term/car rest) km-int)]
                            (if (refused? next)
                              next
                              (recur (term/cdr rest) next)))))]
      (if (refused? state)
        state
        (let [after (frame/obj-stack (:kb state) (:query state))
              state (adopt state after)]
          (expand state (newcomers (:value before) (:value after)) (inc depth) km-int))))))

(defn evaluate-paths
  "Evaluate slot values that are still expressions, then the new participants.

  In prototype mode a nested slot read does not clone. Outside it, a
  prototype can be unified in. <> constraints are left as they are, and
  the clones are not reclassified. The command that calls this answers (t)."
  [state km-int]
  (let [stacked (frame/obj-stack (:kb state) (:query state))
        state (adopt state stacked)
        expanded (expand state (:value stacked) 0 km-int)]
    (if (or (refused? expanded) (not (frame/use-prototypes? (:kb expanded))))
      expanded
      (loop [rest (:value stacked)
             state expanded]
        (cond
          (refused? state) state
          (or (nil? rest) (not (term/cons? rest))) state
          :else
          (let [next (unify-in-prototypes state (term/car rest) nil km-int)]
            (if (refused? next)
              next
              (recur (term/cdr rest) next))))))))
