(ns som.km.writer
  "Print a frame, or a whole knowledge base, as Knowledge Machine text.

  write-frame emits (frame has (slot (values))). A situation or a theory
  wraps that form. write-kb walks frames in the order they were first
  stored, with slots, theories, situations, and prototypes grouped so a
  later load can read the wrappers. Two writes of one value match. The
  header does not include a clock. HTML names go through htextify, which
  returns nothing."
  (:require [clojure.string :as str]
            [som.km.explain :as explain]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.print :as print]
            [som.km.taxonomy :as taxonomy]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(def html-action
  "The default HTML action. The stub does not read it."
  "frame")

(def html-window
  "The default HTML window. The stub does not read it."
  "")

(def ^:private prototype-slots-not-saved
  #{(symbol "has-clones") (symbol "has-built-clones")})

(defn htextify
  "The HTML name wrapper. This is the stub: it returns nothing.

  write-frame calls it only when htmlify is set. The name is then
  omitted."
  [expr text & {:keys [action window]}]
  (let [_ [expr text action window]]
    nil))

(defn- pad
  [n]
  (apply str (repeat n \space)))

(defn- km-name
  [value]
  (print/km-format value))

(defn objwrite
  "The characters km-format would use for one expression.

  A known frame is passed through htextify when htmlify is set. The
  stub returns nothing, so that name is omitted. Nil is written as ()."
  [kb expr htmlify?]
  (cond
    (and htmlify?
         (kb/kb-object? expr)
         (frame/known-frame? kb expr))
    (or (htextify expr (km-name expr) :action html-action :window html-window) "")

    (nil? expr) "()"

    (and (term/cons? expr)
         (term/km-symbol? (term/car expr))
         (utils/eql? (term/car expr) (symbol "quote"))
         (term/singleton? (term/cdr expr)))
    (str "'" (objwrite kb (term/car (term/cdr expr)) htmlify?))

    (term/cons? expr)
    (let [parts (loop [cell expr
                       first? true
                       acc ""]
                  (cond
                    (nil? cell) acc
                    (not (term/cons? cell)) (str acc " . " (objwrite kb cell htmlify?))
                    :else
                    (recur (term/cdr cell)
                           false
                           (str acc
                                (if first? "" " ")
                                (objwrite kb (term/car cell) htmlify?)))))]
      (str "(" parts ")"))

    :else (km-name expr)))

(defn- write-vals
  [kb vals tab htmlify?]
  (if (nil? vals)
    "()"
    (str "("
         (objwrite kb (term/car vals) htmlify?)
         (loop [rest (term/cdr vals)
                acc ""]
           (if-not (term/cons? rest)
             (str acc ")")
             (recur (term/cdr rest)
                    (str acc "\n" (pad tab) (objwrite kb (term/car rest) htmlify?))))))))

(defn- write-slotvals
  [kb slotvals tab htmlify? save-prototype?]
  (cond
    (nil? slotvals) " ()"

    (utils/eql? (frame/slot-in slotvals) (symbol "assertions")) ""

    (and save-prototype?
         (contains? prototype-slots-not-saved (frame/slot-in slotvals)))
    ""

    :else
    (let [slot (frame/slot-in slotvals)
          values (kb/remove-dup-instances (frame/vals-in slotvals))]
      (str "\n" (pad tab) "("
           (objwrite kb slot htmlify?)
           " "
           (write-vals kb values (+ tab 3 (count (km-name slot))) htmlify?)
           ")"))))

(defn- slot-shown?
  [slotvals slots-to-show]
  (or (nil? slots-to-show)
      (utils/member? (frame/slot-in slotvals) slots-to-show)))

(defn- write-slots
  [kb slotsvals tab htmlify? slots-to-show save-prototype?]
  (loop [slots slotsvals
         acc ""]
    (cond
      (nil? slots) acc
      (not (term/cons? slots)) acc
      :else
      (let [pair (term/car slots)]
        (recur (term/cdr slots)
               (if (slot-shown? pair slots-to-show)
                 (str acc (write-slotvals kb pair tab htmlify? save-prototype?))
                 acc))))))

(defn- assertions-only?
  [slots]
  (and (term/singleton? slots)
       (utils/eql? (frame/slot-in (term/car slots)) (symbol "assertions"))))

(defn- facet-slots
  [kb frame facet situation]
  (let [found (frame/get-slotsvals kb frame
                                   :facet facet
                                   :situation situation
                                   :dereference? true)]
    (explain/desource-for-printing (:value found))))

(defn- write-wrapped
  [kb frame situation slotsvals quantifier joiner
   & {:keys [htmlify? theory? slots-to-show save-prototype? tab]
      :or {tab 0}}]
  (let [global? (utils/eql? situation term/global-situation)
        show? (or (nil? slots-to-show)
                  (loop [slots slotsvals]
                    (cond
                      (nil? slots) false
                      (not (term/cons? slots)) false
                      (slot-shown? (term/car slots) slots-to-show) true
                      :else (recur (term/cdr slots)))))]
    (if-not show?
      ""
      (let [tab2 (if global? tab (+ tab 2))
            body (str (if (zero? tab2) "" (pad tab2))
                      (if quantifier (str "(" (km-name quantifier) " ") "(")
                      (objwrite kb frame htmlify?)
                      " " (km-name joiner) " "
                      (write-slots kb slotsvals (+ tab2 2) htmlify?
                                   slots-to-show save-prototype?)
                      ")")]
        (str (if global?
               ""
               (str (if theory? "(in-theory " "(in-situation ")
                    (objwrite kb situation htmlify?)
                    "\n"))
             body
             (if global? "" ")")
             "\n\n")))))

(defn- write-in-situation
  [kb frame situation & {:keys [htmlify? theory? slots-to-show save-prototype?]}]
  (let [own-defn (facet-slots kb frame (symbol "own-definition") situation)
        own-props (facet-slots kb frame (symbol "own-properties") situation)
        member-defn (facet-slots kb frame (symbol "member-definition") situation)
        member-props (facet-slots kb frame (symbol "member-properties") situation)
        opts {:htmlify? htmlify?
              :theory? theory?
              :slots-to-show slots-to-show
              :save-prototype? save-prototype?}]
    (str (if (nil? own-defn)
           ""
           (write-wrapped kb frame situation own-defn nil (symbol "has-definition") opts))
         (if (or (nil? own-props) (assertions-only? own-props))
           ""
           (write-wrapped kb frame situation own-props nil (symbol "has") opts))
         (if (nil? member-defn)
           ""
           (write-wrapped kb frame situation member-defn (symbol "every")
                          (symbol "has-definition") opts))
         (if (or (nil? member-props) (assertions-only? member-props))
           ""
           (write-wrapped kb frame situation member-props (symbol "every")
                          (symbol "has") opts)))))

(defn- prototype-comment
  [kb frame htmlify?]
  (let [prototypes (:value (frame/get-vals kb frame (symbol "prototypes")
                                           :situation term/global-situation
                                           :dereference? true))]
    (if (nil? prototypes)
      ""
      (str "#|\n"
           (loop [prototypes prototypes
                  acc ""]
             (if-not (term/cons? prototypes)
               acc
               (let [prototype (term/car prototypes)
                     lines (loop [exprs (utils/elements (frame/definition kb prototype))
                                  acc (str "\n;;; Prototype " (km-name prototype)
                                           " defined by:\n")]
                             (if (empty? exprs)
                               acc
                               (recur (rest exprs)
                                      (str acc (objwrite kb (first exprs) htmlify?) "\n"))))]
                 (recur (term/cdr prototypes) (str acc lines)))))
           "|#\n\n"))))

(defn- situation-assertions
  [kb frame htmlify?]
  (let [under (taxonomy/isa? kb frame (symbol "Situation"))]
    (if-not (:value under)
      ""
      (let [props (facet-slots kb frame (symbol "member-properties") term/global-situation)
            pair (loop [slots props]
                   (cond
                     (nil? slots) nil
                     (not (term/cons? slots)) nil
                     (utils/eql? (frame/slot-in (term/car slots)) (symbol "assertions"))
                     (term/car slots)
                     :else (recur (term/cdr slots))))]
        (if (nil? pair)
          ""
          (loop [assertions (frame/vals-in pair)
                 acc ""]
            (if-not (term/cons? assertions)
              acc
              (let [assertion (term/car assertions)]
                (recur (term/cdr assertions)
                       (str acc
                            (if (utils/quote? assertion)
                              (str "(in-every-situation "
                                   (objwrite kb frame htmlify?)
                                   "\n  "
                                   (objwrite kb (term/car (term/cdr assertion)) htmlify?)
                                   ")\n\n")
                              "")
                            ))))))))))

(defn- names-of
  [value]
  (cond
    (nil? value) []
    (vector? value) value
    :else (vec (utils/elements value))))

(defn write-frame
  "The text of one frame.

  situations and theories limit which wrappers are written. nulls-okay?
  writes (frame has) when the frame has no stored slots. slots-to-show
  keeps only those slots. A bound name is a comment. A built-in name
  with no slots is a comment. HTML output calls htextify."
  [kb frame & {:keys [situations theories htmlify? nulls-okay? slots-to-show save-prototype?]}]
  (let [situations (names-of (or situations (frame/situations kb)))
        theories (names-of (or theories (frame/theories kb)))]
    (cond
      (and (kb/kb-object? frame) (some? (frame/get-binding kb frame)))
      (str ";;; (" (km-name frame) " is bound to "
           (km-name (frame/dereference kb frame)) ")\n\n")

      (contains? kb/reserved-keywords frame)
      (str ";;; (" (km-name frame)
           " is a reserved name, so this save leaves the vocabulary value)\n\n")

      (not (kb/kb-object? frame))
      (str ";;; (" (km-name frame) " is not a knowledge-base object)\n\n")

      :else
      (let [global (if (some #(utils/eql? % term/global-situation) situations)
                     (write-in-situation kb frame term/global-situation
                                         :htmlify? htmlify?
                                         :slots-to-show slots-to-show
                                         :save-prototype? save-prototype?)
                     "")
            prototypes (if (nil? slots-to-show) (prototype-comment kb frame htmlify?) "")
            theory-text (apply str
                               (map (fn [theory]
                                      (write-in-situation kb frame theory
                                                          :htmlify? htmlify?
                                                          :theory? true
                                                          :slots-to-show slots-to-show
                                                          :save-prototype? save-prototype?))
                                    theories))
            situation-text (apply str
                                  (map (fn [situation]
                                         (if (utils/eql? situation term/global-situation)
                                           ""
                                           (write-in-situation kb frame situation
                                                               :htmlify? htmlify?
                                                               :slots-to-show slots-to-show
                                                               :save-prototype? save-prototype?)))
                                       situations))
            assertions (situation-assertions kb frame htmlify?)
            text (str global prototypes assertions theory-text situation-text)]
        (cond
          (not (str/blank? text)) text

          (frame/built-in-concept-type frame)
          (str ";;; (Concept " (km-name frame) " is a built-in "
               (frame/built-in-concept-type frame) ")\n\n")

          nulls-okay?
          (str "(" (km-name frame) " has)\n\n")

          (and (nil? slots-to-show) (empty? theories))
          (str ";;; (Concept " (km-name frame) " is not declared in the situations "
               (km-name (term/build-list situations nil)) ")\n\n")

          (nil? slots-to-show)
          (str ";;; (Concept " (km-name frame)
               " is not declared in the situations "
               (km-name (term/build-list situations nil))
               " nor the theories "
               (km-name (term/build-list theories nil)) ")\n\n")

          :else "")))))

(defn- class-names
  [kb class]
  (let [below (taxonomy/all-subclasses kb class)]
    (into #{class} (utils/elements (:value below)))))

(defn- prototype?
  [kb frame]
  (and (kb/kb-object? frame)
       (some? (:value (frame/get-vals kb frame (symbol "prototype-of")
                                      :situation term/global-situation
                                      :dereference? false)))))

(defn- isa-name?
  [kb frame class-name]
  (boolean (:value (taxonomy/isa? kb frame class-name))))

(defn- group-frames
  "Slot, theory, and situation frames first, then prototypes, then the rest.

  Each group keeps the order the frames were first stored. Comment tags
  are returned separately. The Lisp sorts each group by symbol name."
  [kb]
  (let [order (vec (:frame-order kb))
        slots (class-names kb (symbol "Slot"))
        theories (class-names kb (symbol "Theory"))
        situations (class-names kb (symbol "Situation"))
        groups {:comment []
                :slot []
                :theory-class []
                :theory []
                :situation-class []
                :situation []
                :prototype []
                :rest []}]
    (reduce (fn [groups frame]
              (cond
                (explain/user-comment? frame) (update groups :comment conj frame)
                (contains? slots frame) (update groups :slot conj frame)
                (contains? theories frame) (update groups :theory-class conj frame)
                (isa-name? kb frame (symbol "Theory")) (update groups :theory conj frame)
                (contains? situations frame) (update groups :situation-class conj frame)
                (isa-name? kb frame (symbol "Situation")) (update groups :situation conj frame)
                (prototype? kb frame) (update groups :prototype conj frame)
                :else (update groups :rest conj frame)))
            groups
            order)))

(defn- quoted
  [value]
  (str "'" (if (nil? value) "nil" (print/km-format value))))

(defn- flag
  [on?]
  (quoted (if on? (symbol "t") nil)))

(defn- setq-line
  [name value]
  (str "(SETQ " name " " value ")\n"))

(defn- behavior-lines
  [kb]
  (let [runtime (:runtime kb)]
    (str "
;;; ----------------------------------------
;;;	KM'S INTERNAL BEHAVIOR PARAMETER VALUES
;;; ----------------------------------------

"
         (setq-line "*MAX-PADDING-INSTANCES*" (quoted (or (:max-padding-instances runtime) 0)))
         (setq-line "*INSTANCE-OF-IS-FLUENT*" (flag (:instance-of-is-fluent? runtime)))
         (setq-line "*RECURSIVE-PROTOTYPES*" (flag (:recursive-prototypes? runtime)))
         (setq-line "*EAGERLY-UNIFY-PROTOTYPES*" (flag (:eagerly-unify-prototypes? runtime)))
         (setq-line "*RECORD-EXPLANATIONS*" (flag (:record-explanations? runtime)))
         (setq-line "*RECORD-EXPLANATIONS-FOR-CLONES*" (flag (:record-explanations-for-clones? runtime)))
         (setq-line "*DEFAULT-FLUENT-STATUS*" (quoted (:default-fluent-status runtime)))
         (setq-line "*CLASSIFICATION-ENABLED*" (flag (:classification-enabled? runtime)))
         (setq-line "*PROTOTYPE-CLASSIFICATION-ENABLED*" (flag (:prototype-classification-enabled? runtime)))
         (setq-line "*USE-PROTOTYPES*" (flag (get runtime :use-prototypes? true)))
         (setq-line "*ACTIVE-OBJ-STACK*" (flag (:active-obj-stack? kb)))
         (setq-line "*SLOT-CHECKING-ENABLED*" (flag (:slot-checking-enabled? runtime)))
         (setq-line "*LOGGING*" (flag (:logging? runtime)))
         "\n")))

(defn- state-lines
  [kb]
  (let [runtime (:runtime kb)]
    (str "
;;; ----------------------------------------
;;;	KM'S INTERNAL STATE PARAMETER VALUES
;;; ----------------------------------------

"
         (setq-line "*KM-GENSYM-COUNTER*" (quoted (or (:counter kb) 0)))
         (setq-line "*VISIBLE-THEORIES*" (quoted (:visible-theories runtime)))
         (setq-line "*CURR-PROTOTYPE*" (quoted (:curr-prototype runtime)))
         (setq-line "*CURR-SITUATION*" (quoted (:situation kb)))
         (setq-line "*CLASSES-USING-ASSERTIONS-SLOT*" (quoted (:classes-using-assertions runtime)))
         (setq-line "*ARE-SOME-DEFINITIONS*" (flag (:are-some-definitions? runtime)))
         (setq-line "*ARE-SOME-PROTOTYPE-DEFINITIONS*" (flag (:are-some-prototype-definitions? runtime)))
         (setq-line "*ARE-SOME-PROTOTYPES*" (flag (:are-some-prototypes? runtime)))
         (setq-line "*ARE-SOME-SUBSLOTS*" (flag (:are-some-subslots? runtime)))
         (setq-line "*ARE-SOME-CONSTRAINTS*" (flag (:are-some-constraints? runtime)))
         (setq-line "*ARE-SOME-TAGS*" (flag (:are-some-tags? runtime)))
         (setq-line "*ARE-SOME-DEFAULTS*" (flag (:are-some-defaults? runtime)))
         (setq-line "*AM-IN-SITUATIONS-MODE*" (flag (:situations-mode? runtime)))
         "\n")))

(defn- fourth
  [value]
  (term/car (term/cdr (term/cdr (term/cdr value)))))

(defn- explanation-lines
  [kb frame situations theories]
  (let [places (into [term/global-situation]
                     (remove #(utils/eql? % term/global-situation)
                             (concat situations theories)))]
    (apply str
           (map (fn [situation]
                  (loop [records (utils/elements
                                  (frame/explanations kb frame :situation situation))
                         acc ""]
                    (if (empty? records)
                      acc
                      (let [record (first records)
                            expl (fourth record)]
                        (recur (rest records)
                               (if (nil? expl)
                                 acc
                                 (str acc
                                      "(explanation (:triple "
                                      (km-name (term/car record)) " "
                                      (km-name (term/car (term/cdr record))) " "
                                      (km-name (term/car (term/cdr (term/cdr record))))
                                      ")\n  ("
                                      (km-name expl)
                                      "))\n")))))))
                places))))

(defn write-kb-text
  "The text save-kb writes for this knowledge base.

  reset-kb? includes (reset-kb) and the temporary disable commands.
  include-explanations? includes the explanation section. situations,
  when supplied, limits the situation wrappers. Two calls on one value
  return the same text."
  [kb & {:keys [reset-kb? include-explanations? situations objects]
         :or {reset-kb? true include-explanations? true}}]
  (let [groups (group-frames kb)
        chosen (if (nil? objects)
                 (concat (:slot groups) (:theory-class groups) (:theory groups)
                         (:situation-class groups) (:situation groups)
                         (:prototype groups) (:rest groups))
                 (names-of objects))
        situation-names (if (nil? situations)
                         (names-of (frame/situations kb))
                         (names-of situations))
        theory-names (names-of (frame/theories kb))
        unbound (remove #(some? (frame/get-binding kb %)) chosen)
        body (apply str
                    (map (fn [frame]
                           (if (some? (frame/get-binding kb frame))
                             (write-frame kb frame :situations situation-names
                                          :theories theory-names)
                             (str (write-frame kb frame
                                               :situations situation-names
                                               :theories theory-names
                                               :nulls-okay? true)
                                  ";;; ----------\n\n")))
                         chosen))
        taxonomy (apply str
                        (map (fn [frame]
                               (if (some? (frame/get-binding kb frame))
                                 ""
                                 (write-frame kb frame
                                              :situations situation-names
                                              :theories theory-names
                                              :slots-to-show (term/km-list (symbol "superclasses"))
                                              :nulls-okay? false)))
                             chosen))
        explanations (if-not include-explanations?
                       ""
                       (str "\n;;; ---------- EXPLANATIONS ----------\n\n"
                            (apply str
                                   (map #(explanation-lines kb % situation-names theory-names)
                                        unbound))))]
    (str "\n;;; Current state of the KB (KM 2.5.45)\n"
         (if-not reset-kb?
           ""
           (str "\n(reset-kb)\n"
                "\n(disable-slot-checking)       ; (Temporarily disable while rebuilding KB state)\n"
                "                              ; (Will be restored to original value by final SETQ statements)\n"
                "\n(disable-classification)      ; (Temporarily disable while rebuilding KB state)\n"
                "                              ; (Will be restored to original value by final SETQ statements)\n"
                "\n(disable-installing-inverses) ; (Temporarily disable while rebuilding KB state)\n"
                "                              ; (Will be switched back on by (enable-installing-inverses) at the end)\n"))
         "\n;;; ---------- TAXONOMY ----------\n\n"
         taxonomy
         "\n;;; ---------- CONTENTS ----------\n\n"
         body
         explanations
         "\n;;; ----------------------------------------\n"
         "\n(enable-installing-inverses)  ; (Re-enable it after restoring KB state)\n"
         (behavior-lines kb)
         (state-lines kb)
         ";;; --- end (" (count unbound) " frames written) ---\n\n")))
