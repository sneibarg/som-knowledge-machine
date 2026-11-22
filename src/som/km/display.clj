(ns som.km.display
  "showme, showme-all, and evaluate-all.

  showme prints write-frame. showme-all prints the rules stored on the
  frame and on its classes, in one situation at a time. evaluate-all
  reads every Slot. The interpreter is passed in as km-int, so this
  namespace does not require it. Printed text is appended to :text.
  A file capture keeps the frame text on :captured and still sends the
  empty-frames sentence to :text."
  (:require [som.km.errors :as errors]
            [som.km.explain :as explain]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.print :as print]
            [som.km.taxonomy :as taxonomy]
            [som.km.term :as term]
            [som.km.utils :as utils]
            [som.km.writer :as writer]))

(def ^:private own-properties (symbol "own-properties"))
(def ^:private own-definition (symbol "own-definition"))
(def ^:private member-properties (symbol "member-properties"))
(def ^:private member-definition (symbol "member-definition"))
(def ^:private amp (symbol "&"))
(def ^:private amp-amp (symbol "&&"))

(defn- emit
  [state text capture?]
  (if capture?
    (update state :captured #(str % text))
    (update state :text #(str % text))))

(defn- names
  "Situation or theory names. A vector is already a name list."
  [value]
  (cond
    (nil? value) []
    (vector? value) value
    :else (vec (utils/elements value))))

(defn- km-text
  "km-format of one control. The controls passed here are fixed strings."
  [control args]
  (:text (print/km-format-control control args)))

(defn- literal
  "expr2string, written as characters. A tilde in the value stays a tilde."
  [kb expr]
  (writer/objwrite kb expr false))

(defn- nodebugger
  [state template & args]
  (apply errors/report-error state :nodebugger-error template args))

(defn- binding-note
  "The bound-name comment, when the expression and its one frame differ.

  neq is name equality. Two reads of one symbol are the same frame."
  [state expr frames newlines capture?]
  (let [frame (when (term/cons? frames) (term/car frames))]
    (if (and (term/singleton? frames)
             (not (utils/eql? expr frame))
             (kb/kb-object? expr)
             (kb/is-km-term? frame))
      (emit state
            (km-text (str ";;; (~a is bound to ~a)" newlines) [expr frame])
            capture?)
      state)))

(defn- each-frame
  "Walk frames. f receives the state and one frame and returns a state."
  [state frames f]
  (loop [pending frames
         current state]
    (cond
      (or (nil? pending) (not (term/cons? pending))) current
      :else
      (let [next (f current (term/car pending))]
        (if (= "not-ported" (:error next))
          next
          (recur (term/cdr pending) next))))))

(defn- show-one
  [state frame situations theories capture?]
  (if-not (kb/is-km-term? frame)
    (nodebugger state
                "Doing (showme-frame %s) - the frame name `%s' should be a KB term!"
                (print/km-format frame)
                (print/km-format frame))
    (emit state
          (writer/write-frame (:kb state) frame
                              :situations situations
                              :theories theories)
          capture?)))

(defn showme
  "Print the frames expr evaluates to and return those frames.

  The nested evaluation uses :fail. No frames prints the sentence to
  :text and answers nil. One frame is write-frame. Several frames print
  a divider after each one, including the last. capture? keeps the frame
  text on :captured. The empty-frames sentence still goes to :text."
  [state expr km-int & {:keys [situations theories capture?]}]
  (let [found (km-int state expr :fail-mode :fail)]
    (if (= "not-ported" (:error found))
      found
      (let [frames (:value found)
            situations (or situations (frame/situations (:kb found)))
            theories (or theories (frame/theories (:kb found)))
            noted (binding-note found expr frames "~%~%" capture?)]
        (cond
          (nil? frames)
          (update noted :text
                  #(str % (km-text ";;; (No frames to show: ~a evaluates to NIL)~%"
                                   [expr])))

          (term/singleton? frames)
          (show-one noted (term/car frames) situations theories capture?)

          :else
          (each-frame noted frames
                      (fn [current frame]
                        (let [printed (show-one current frame situations theories capture?)]
                          (emit printed ";;; ----------\n\n" capture?)))))))))

(defn- rule-sets-in
  "The rule sets of one class, one slot, and one situation.

  A single-valued slot splits & and keeps the earlier duplicate. A
  multivalued slot splits &&. These are the member facets only."
  [kb class slot situation]
  (let [props (frame/get-vals kb class slot
                              :facet member-properties
                              :situation situation)
        defs (frame/get-vals (:kb props) class slot
                             :facet member-definition
                             :situation situation)
        kb (:kb defs)]
    (if (frame/single-valued-slot? kb slot)
      (let [flat (utils/append-lists
                  (term/km-list (kb/un-andify (:value props))
                                (kb/un-andify (:value defs))))
            unique (utils/remove-duplicates flat
                                            :test utils/equal?
                                            :from-end? true)]
        {:kb kb
         :value (when unique
                  (term/build-list
                   (mapv #(term/km-list %) (utils/elements unique))
                   nil))})
      {:kb kb
       :value (utils/remove-items
               nil
               (utils/append-lists
                (term/km-list (kb/&&-exprs-to-valsets (:value props))
                              (kb/&&-exprs-to-valsets (:value defs)))))})))

(defn- inherited-pairs
  "Rule sets and the class they came from, for these classes and situations."
  [kb slot classes situations]
  (loop [classes classes
         kb kb
         acc []]
    (if (or (nil? classes) (not (term/cons? classes)))
      {:kb kb :value (term/build-list acc nil)}
      (let [class (term/car classes)
            gathered (loop [situations situations
                            kb kb
                            sets nil]
                       (if (or (nil? situations) (not (term/cons? situations)))
                         {:kb kb :value (utils/remove-items nil sets)}
                         (let [one (rule-sets-in kb class slot (term/car situations))]
                           (recur (term/cdr situations)
                                  (:kb one)
                                  (utils/append-lists
                                   (term/km-list sets (:value one)))))))
            unique (utils/remove-duplicates (:value gathered) :test utils/equal?)]
        (recur (term/cdr classes)
               (:kb gathered)
               (if (nil? unique)
                 acc
                 (conj acc (term/km-list unique class))))))))

(defn- inherited-rule-sets
  "The rule sets, without the classes. The earlier equal copy is kept."
  [kb slot classes situations]
  (let [pairs (inherited-pairs kb slot classes situations)
        lists (loop [pending (:value pairs)
                     acc nil]
                (if (or (nil? pending) (not (term/cons? pending)))
                  acc
                  (recur (term/cdr pending)
                         (utils/append-lists
                          (term/km-list acc (term/car (term/car pending)))))))]
    {:kb (:kb pairs)
     :value (utils/remove-duplicates lists :test utils/equal? :from-end? true)}))

(defn- used-slots
  "Slot names whose value list is not empty."
  [kb frame facet situation]
  (if-not (kb/kb-object? frame)
    {:kb kb :value nil}
    (let [found (frame/get-slotsvals kb frame :facet facet :situation situation)]
      {:kb (:kb found)
       :value (loop [pairs (:value found)
                     acc []]
                (cond
                  (or (nil? pairs) (not (term/cons? pairs)))
                  (term/build-list acc nil)
                  (some? (frame/vals-in (term/car pairs)))
                  (recur (term/cdr pairs) (conj acc (frame/slot-in (term/car pairs))))
                  :else (recur (term/cdr pairs) acc)))})))

(defn- join-slots
  [kb frames facets situation]
  (loop [frames frames
         kb kb
         acc nil]
    (if (or (nil? frames) (not (term/cons? frames)))
      {:kb kb
       :value (utils/remove-duplicates acc)}
      (let [frame (term/car frames)
            read (loop [facets facets
                        kb kb
                        slots nil]
                   (if (empty? facets)
                     {:kb kb :value slots}
                     (let [found (used-slots kb frame (first facets) situation)]
                       (recur (rest facets)
                              (:kb found)
                              (utils/append-lists
                               (term/km-list slots (:value found)))))))]
        (recur (term/cdr frames)
               (:kb read)
               (utils/append-lists (term/km-list acc (:value read))))))))

(defn- by-name
  "string< on the symbol name. Upper case comes before lower case."
  [slots]
  (sort-by #(if (term/km-symbol? %) (term/symbol-name %) "")
           (remove nil? (utils/elements slots))))

(defn- spaces
  [n]
  (apply str (repeat n \space)))

(defn- slot-exprs
  "The several-rule-set printer. One rule set closes the line.

  The first line is indented inside a double parenthesis. Later lines
  line the joiner up under the value. A null rule list is a program error."
  [kb slot rules joiner first?]
  (if (nil? rules)
    {:text ""
     :error "Null all-rule-sets in print-slot-exprs (stack.lisp!)"}
    (let [prefix (if first?
                   (km-text (if (utils/eql? joiner amp)
                              "~%  (~a ((  "
                              "~%  (~a ((   ")
                            [slot])
                   (str (spaces (+ 6 (count (term/symbol-name slot))))
                        (km-text "~a " [joiner])))
          body (literal kb
                        (if (frame/single-valued-slot? kb slot)
                          (kb/vals-to-&-expr (term/car rules))
                          (term/car rules)))
          rest (term/cdr rules)]
      (if (term/singleton? rules)
        {:text (str prefix body "))")}
        (let [more (slot-exprs kb slot rest joiner false)]
          {:text (str prefix body "\n" (:text more))
           :error (:error more)})))))

(defn- print-rules
  [state slot rules]
  (let [kb (:kb state)
        joiner (if (frame/single-valued-slot? kb slot) amp amp-amp)]
    (if (term/singleton? rules)
      (emit state
            (str (km-text "~%  (~a " [slot])
                 (literal kb (term/car rules))
                 ")")
            false)
      (let [printed (slot-exprs kb slot rules joiner true)
            noted (if (:error printed)
                    (errors/report-error state :program-error "%s" (:error printed))
                    state)]
        (emit noted (:text printed) false)))))

(defn- own-section
  [state instance situation]
  (let [classes (taxonomy/all-classes (:kb state) instance)
        own (join-slots (:kb classes) (term/km-list instance)
                        [own-properties own-definition] situation)
        inherited (join-slots (:kb own) (:value classes)
                              [member-properties member-definition] situation)
        slots (utils/remove-duplicates
               (utils/append-lists
                (term/km-list (:value own) (:value inherited))))
        state (assoc state :kb (:kb inherited))]
    (if (nil? slots)
      state
      (let [global? (utils/eql? situation term/global-situation)
            opened (emit state
                         (if global?
                           (km-text "(~a has" [instance])
                           (km-text "(in-situation ~a~% (~a has"
                                    [situation instance]))
                         false)
            filled (reduce
                    (fn [current slot]
                      (let [inherited (inherited-rule-sets
                                       (:kb current) slot (:value classes)
                                       (term/km-list situation))
                            own-props (frame/get-vals (:kb inherited) instance slot
                                                      :facet own-properties
                                                      :situation situation)
                            own-defs (frame/get-vals (:kb own-props) instance slot
                                                     :facet own-definition
                                                     :situation situation)
                            own-sets (utils/remove-items
                                      nil
                                      (term/km-list (:value own-props)
                                                    (:value own-defs)))
                            combined (utils/remove-duplicates
                                      (utils/append-lists
                                       (term/km-list own-sets (:value inherited)))
                                      :test utils/equal?
                                      :from-end? true)
                            rules (explain/desource
                                   (frame/bind-self combined instance))
                            current (assoc current :kb (:kb own-defs))]
                        (print-rules current slot rules)))
                    opened
                    (by-name slots))]
        (emit filled (km-text (if global? ")~%~%" "))~%~%") []) false)))))

(defn- member-section
  [state class situation]
  (let [supers (taxonomy/all-superclasses (:kb state) class)
        classes (term/cons-cell class (:value supers))
        found (join-slots (:kb supers) classes
                          [member-properties member-definition] situation)
        slots (:value found)
        state (assoc state :kb (:kb found))]
    (if (nil? slots)
      state
      (let [global? (utils/eql? situation term/global-situation)
            opened (emit state
                         (if global?
                           (km-text "(every ~a has" [class])
                           (km-text "(in-situation ~a~% (every ~a has"
                                    [situation class]))
                         false)
            filled (reduce
                    (fn [current slot]
                      (let [rules (inherited-rule-sets
                                   (:kb current) slot classes
                                   (term/km-list situation))
                            current (assoc current
                                           :kb (:kb rules))]
                        (print-rules current slot
                                     (explain/desource (:value rules)))))
                    opened
                    (by-name slots))]
        (emit filled (km-text (if global? ")~%~%" "))~%~%") []) false)))))

(defn- show-all-one
  [state instance situations]
  (if-not (kb/is-km-term? instance)
    (nodebugger state
                "Doing (showme-all-frame %s) - the instance name `%s' should be a KB term!"
                (print/km-format instance)
                (print/km-format instance))
    (if-not (kb/kb-object? instance)
      state
      (reduce (fn [current situation]
                (-> current
                    (own-section instance situation)
                    (member-section instance situation)))
              state
              (names situations)))))

(defn showme-all
  "Print every stored rule of the frames expr evaluates to.

  The nested evaluation uses :fail-mode :error. Slot names are sorted
  with string< on the symbol name. The answer is the frames."
  [state expr km-int & {:keys [situations]}]
  (let [found (km-int state expr :fail-mode :error)]
    (if (= "not-ported" (:error found))
      found
      (let [frames (:value found)
            situations (or situations (frame/situations (:kb found)))
            noted (binding-note found expr frames "~%" false)]
        (cond
          (term/singleton? frames)
          (show-all-one noted (term/car frames) situations)
          :else
          (each-frame noted frames
                      (fn [current frame]
                        (-> (show-all-one current frame situations)
                            (emit ";;; ----------\n\n" false)))))))))

(defn- evaluate-one-situation
  [state instance situation km-int km-unique-int]
  (let [opened (emit state
                     (if (utils/eql? situation term/global-situation)
                       (km-text "(~a has~%" [instance])
                       (km-text "(in-situation ~a~% (~a has~%"
                                [situation instance]))
                     false)
        slots (taxonomy/all-instances (:kb opened) (symbol "Slot"))
        current (assoc opened :kb (:kb slots))
        filled (reduce
                (fn [current slot]
                  (if (= "not-ported" (:error current))
                    current
                    (let [domain (km-unique-int
                                  current
                                  (term/km-list (symbol "the") (symbol "domain")
                                                (symbol "of") slot))]
                      (if (= "not-ported" (:error domain))
                        domain
                        (let [named (or (:value domain) (symbol "Thing"))
                              classed (taxonomy/isa? (:kb domain) instance named)]
                          (if-not (:value classed)
                            (assoc domain :kb (:kb classed))
                            (let [vals (km-int (assoc domain :kb (:kb classed))
                                               (term/km-list (symbol "the") slot
                                                             (symbol "of") instance))]
                              (if (= "not-ported" (:error vals))
                                vals
                                (emit vals
                                      (if (nil? (:value vals))
                                        (km-text "  (~a ())~%" [slot])
                                        (km-text "  (~a ~a)~%"
                                                 [slot (:value vals)]))
                                      false)))))))))
                current
                (by-name (:value slots)))]
    (if (= "not-ported" (:error filled))
      filled
      (emit filled
            (km-text (if (utils/eql? situation term/global-situation)
                       ")~%~%"
                       "))~%~%")
                     [])
            false))))

(defn- evaluate-one
  [state instance situations km-int km-unique-int]
  (if-not (kb/is-km-term? instance)
    (nodebugger state
                "Doing (evaluate-all-frame %s) - the instance name `%s' should be a KB term!"
                (print/km-format instance)
                (print/km-format instance))
    (reduce (fn [current situation]
              (if (= "not-ported" (:error current))
                current
                (evaluate-one-situation current instance situation
                                        km-int km-unique-int)))
            state
            (names situations))))

(defn evaluate-all
  "Read every Slot of the frames expr evaluates to and print the values.

  The nested evaluation uses :fail-mode :error. A slot whose domain is
  empty is read as Thing. A slot the frame is not an instance of is
  skipped after that domain read. Empty values are printed. The answer
  is the frames. km-unique-int reads the domain."
  [state expr km-int km-unique-int & {:keys [situations]}]
  (let [found (km-int state expr :fail-mode :error)]
    (if (= "not-ported" (:error found))
      found
      (let [frames (:value found)
            situations (or situations (frame/situations (:kb found)))
            noted (binding-note found expr frames "~%~%" false)
            printed (cond
                      (term/singleton? frames)
                      (evaluate-one noted (term/car frames) situations
                                    km-int km-unique-int)
                      :else
                      (each-frame noted frames
                                  (fn [current frame]
                                    (let [done (evaluate-one current frame situations
                                                             km-int km-unique-int)]
                                      (if (= "not-ported" (:error done))
                                        done
                                        (emit done ";;; ----------\n\n" false))))))]
        (if (= "not-ported" (:error printed))
          printed
          (assoc printed :value frames))))))
