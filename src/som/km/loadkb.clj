(ns som.km.loadkb
  "Load and save a knowledge base, and undo a logged change.

  load-kb reads a file as UTF-8, or as ISO-8859-1 when the bytes are not
  UTF-8, and evaluates each expression. save-kb writes the text from
  som.km.writer. fastsave-kb and fastload-kb stay refused.

  Logging is off until start-logging. A checkpoint remembers the
  knowledge base value. undo restores that value. keeping-kb evaluates
  an expression and then restores the value from before it. The creation
  log records frames added while it is on, and undo-creations deletes
  the anonymous ones."
  (:refer-clojure :exclude [load-file])
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [som.km.classify :as classify]
            [som.km.errors :as errors]
            [som.km.frame :as frame]
            [som.km.kbutils :as kb]
            [som.km.minimatch :as match]
            [som.km.print :as print]
            [som.km.prototypes :as prototypes]
            [som.km.read :as read]
            [som.km.situations :as situations]
            [som.km.stack :as stack]
            [som.km.stats :as stats]
            [som.km.term :as term]
            [som.km.utils :as utils]
            [som.km.writer :as writer])
  (:import [java.nio ByteBuffer]
           [java.nio.charset Charset CodingErrorAction]))

(def ^:private keeping-id (symbol "%keeping-kb-cpid%"))

(defn- add-text
  [state text]
  (if (str/blank? (str text))
    state
    (assoc state :text (str (:text state) text))))

(defn- one
  [state value]
  (assoc state :value (term/km-list value)))

(defn- none
  [state]
  (assoc state :value nil))

(defn logging?
  "True when an undo log is being kept.

  *logging* and *internal-logging* both count. Both start off."
  [kb]
  (boolean (or (get-in kb [:runtime :logging?])
               (get-in kb [:runtime :internal-logging?]))))

(defn logging-creations?
  "True when new frames are recorded for undo-creations."
  [kb]
  (boolean (get-in kb [:runtime :logging-creations?])))

(defn skip-checkpoint?
  "True for showme, undo, and why.

  The prompt does not checkpoint these. A later command still can."
  [expr]
  (and (term/cons? expr)
       (contains? #{(symbol "showme") (symbol "undo") (symbol "why")}
                  (term/car expr))))

(defn set-checkpoint
  "Remember the knowledge base under id when logging is on.

  The id is t when the caller does not pass one. Nothing is recorded
  while logging is off. The returned value is the same frames with the
  checkpoint on the history."
  ([kb]
   (set-checkpoint kb (symbol "t")))
  ([kb id]
   (if-not (logging? kb)
     kb
     (assoc kb :history (into [{:checkpoint id :snapshot kb}]
                              (or (:history kb) []))))))

(defn undo
  "Restore the knowledge base recorded at a checkpoint.

  A nil id uses the newest checkpoint. :id is that checkpoint's id.
  :exhausted? is true when the history has no matching checkpoint.
  The restored value is the one remembered at the checkpoint, including
  its earlier history."
  [kb id]
  (loop [kb kb]
    (let [history (or (:history kb) [])]
      (if (empty? history)
        {:kb (assoc kb :history []) :id nil :exhausted? true}
        (let [entry (first history)]
          (if (and (contains? entry :checkpoint)
                   (or (nil? id) (utils/equal? id (:checkpoint entry))))
            {:kb (:snapshot entry) :id (:checkpoint entry) :exhausted? false}
            (recur (:snapshot entry))))))))

(defn- noted
  [state text value]
  (-> (add-text state text) (one value)))

(defn start-logging
  "Turn the undo log on. The text says whether it was already on."
  [state]
  (if (get-in state [:kb :runtime :logging?])
    (noted state "(Logging of KM commands is already switched on)\n" (symbol "t"))
    (noted (assoc-in state [:kb :runtime :logging?] true)
           "(Started logging KM commands)\n"
           (symbol "t"))))

(defn stop-logging
  "Turn the undo log off and drop the history."
  [state]
  (if-not (get-in state [:kb :runtime :logging?])
    (noted state "(Logging of KM commands is already switched off)\n" (symbol "t"))
    (let [kb (:kb state)]
      (noted (assoc state :kb (-> kb
                                   (assoc :history [])
                                   (assoc-in [:runtime :logging?] false)))
             "(Stopping logging of KM commands)\n"
             (symbol "t")))))

(defn start-creations-logging
  "Record frames added after this call. The text says whether it was already on."
  [state]
  (if (logging-creations? (:kb state))
    (noted state "(Logging of concept creations is already switched on)\n" (symbol "t"))
    (noted (assoc-in state [:kb :runtime :logging-creations?] true)
           "(Started logging of concept creations)\n"
           (symbol "t"))))

(defn stop-creations-logging
  "Stop the creation log and drop it."
  [state]
  (if-not (logging-creations? (:kb state))
    (noted state "(Logging of concept creations is already switched off)\n" (symbol "t"))
    (noted (assoc state :kb (assoc (:kb state) :creations []
                                   :runtime (assoc (:runtime (:kb state))
                                                   :logging-creations? false)))
           "(Stopping logging of concept creations)\n"
           (symbol "t"))))

(defn set-creations-checkpoint
  "Mark the creation log.

  Logging starts if it was off. multiple? keeps earlier checkpoints.
  Otherwise the log is cleared first. The gensym counter is recorded
  with the mark so undo-creations can put it back."
  [state id & {:keys [multiple?]}]
  (let [state (if (logging-creations? (:kb state))
                state
                (-> (add-text state "WARNING! Trying to set-creations-checkpoint, but you should first call (start-creations-logging)!\n")
                    (add-text "WARNING! I'll start creation's logging now for you.\n")
                    start-creations-logging))
        kb (:kb state)
        older (if multiple? (or (:creations kb) []) [])
        creations (into [id {:counter (or (:counter kb) 0)}] older)]
    (noted (assoc state :kb (assoc kb :creations creations))
           "Creations checkpoint is set\n"
           (symbol "t"))))

(defn- chain-after
  [kb frame]
  (loop [frame frame
         acc []]
    (if-let [bound (frame/get-binding kb frame)]
      (recur bound (conj acc bound))
      acc)))

(defn undo-creations
  "Delete anonymous frames created since the checkpoint.

  A named frame is left in place. A frame unified with an older frame
  is left in place. The gensym counter returns to the recorded value.
  Logging must be off, and creation logging must be on."
  [state id & {:keys [remove-checkpoint?]}]
  (cond
    (not (logging-creations? (:kb state)))
    (add-text (none state)
              "Unable to undo concept creations - concept creations not switched on! Do (start-creations-logging) first.\n")

    (logging? (:kb state))
    (add-text (none state)
              "You're not allowed to undo concept creations while logging is on! Do (stop-logging) first.\n")

    :else
    (let [kb (:kb state)
          creations (or (:creations kb) [])
          at (first (keep-indexed (fn [index item]
                                    (when (utils/equal? item id) index))
                                  creations))
          state (add-text state "Undo creations: starting\n")]
      (if (nil? at)
        (add-text (none state)
                  (str "Unable to undo concept creations - can't find checkpoint "
                       (print/km-format id)
                       " to undo back to.\nDo (set-creations-checkpoint) to create a checkpoint.\n"))
        (let [started (System/nanoTime)
              doomed (vec (remove #(and (map? %) (contains? % :counter))
                                  (subvec creations 0 at)))
              walked (reduce (fn [{:keys [doomed state]} frame]
                               (if (some #(utils/eql? frame %) doomed)
                                 {:doomed doomed :state state}
                                 (let [linked (filterv #(some (fn [item] (utils/eql? item %)) doomed)
                                                       (chain-after kb frame))]
                                   (if (empty? linked)
                                     {:doomed doomed :state state}
                                     {:doomed (vec (remove #(some (fn [keep] (utils/eql? keep %)) linked)
                                                           doomed))
                                      :state (reduce (fn [state item]
                                                       (add-text state
                                                                 (str "   " (print/km-format item)
                                                                      " created since checkpoint, but won't delete it (pre-checkpoint instance is unified with it)\n")))
                                                     state
                                                     linked)}))))
                             {:doomed doomed :state state}
                             (:frame-order kb))
              spared (:doomed walked)
              deleted (reduce (fn [state frame]
                                (cond
                                  (not (frame/anonymous-instance? (:kb state) frame)) state
                                  (not (frame/known-frame? (:kb state) frame)) state
                                  (some? (frame/get-binding (:kb state) frame)) state
                                  :else
                                  (let [removed (frame/delete-frame (:kb state) frame
                                                                    :query (:query state))]
                                    (assoc state :kb (:kb removed) :query (:query removed)))))
                              (:state walked)
                              spared)
              deleted (reduce (fn [state frame]
                                (if (and (frame/known-frame? (:kb state) frame)
                                         (some? (frame/get-binding (:kb state) frame)))
                                  (let [removed (frame/delete-frame (:kb state) frame
                                                                    :delete-inverses? false
                                                                    :dereference? false
                                                                    :query (:query state))]
                                    (assoc state :kb (:kb removed) :query (:query removed)))
                                  state))
                              deleted
                              spared)
              mark (get creations (inc at))
              counter (when (and (map? mark) (integer? (:counter mark)))
                        (:counter mark))
              deleted (if (some? counter)
                       deleted
                       (add-text deleted
                                 "ERROR! Failed to find number to reset *km-gensym-counter* to (Leaving it unchanged)\n"))
              older (subvec creations (if (some? counter) (+ at 2) (inc at)))
              kept (cond
                     (nil? counter) older
                     remove-checkpoint? older
                     :else (into [id mark] older))
              kb (cond-> (assoc (:kb deleted) :creations kept)
                   (some? counter) (assoc :counter counter))
              query (:query (stack/clear-obj-stack (:query deleted)))
              seconds (/ (- (System/nanoTime) started) 1000000000.0)]
          (-> (assoc deleted :kb kb :query query)
              (add-text (format "Undo creations: %d concepts deleted in %.2f sec%n"
                                at seconds))
              (one (symbol "t"))))))))

(defn keeping-kb
  "Evaluate exprs and then restore the knowledge base.

  Logging is on for the body. The value of the last expression is kept.
  The frames return to the checkpoint taken before the first expression.
  The caller's logging flag is put back."
  [state exprs km-int]
  (let [saved-logging (get-in state [:kb :runtime :logging?])
        marked (-> state
                   (assoc-in [:kb :runtime :logging?] true)
                   (assoc :kb (set-checkpoint
                               (assoc-in (:kb state) [:runtime :logging?] true)
                               keeping-id)))
        ran (reduce (fn [state expr]
                      (if (or (:error state) (:stopped? state))
                        state
                        (km-int state expr :fail-mode (or (:fail-mode state) :fail))))
                    marked
                    (utils/elements exprs))
        restored (undo (:kb ran) keeping-id)
        kb (assoc-in (:kb restored) [:runtime :logging?] (boolean saved-logging))]
    (assoc ran :kb kb)))

(defn store-kb
  "Remember this knowledge base on the value itself.

  A later restore-kb returns to it. Two callers do not share one stored
  copy. The Lisp keeps a single process-wide copy."
  [state]
  (let [kb (:kb state)
        snapshot (dissoc kb :stored-kb)]
    (one (assoc state :kb (assoc kb :stored-kb snapshot)) (symbol "t"))))

(defn restore-kb
  "Return to the knowledge base remembered by store-kb.

  The remembered copy stays, so a second restore returns to the same
  value. The text names a missing copy."
  [state]
  (if-let [snapshot (:stored-kb (:kb state))]
    (one (assoc state :kb (assoc snapshot :stored-kb snapshot)) (symbol "t"))
    (add-text (none state) "No stored KB state to restore!\n")))

(defn- read-file-text
  "The characters in path.

  UTF-8 is used when the bytes are valid UTF-8. Otherwise the bytes are
  read as ISO-8859-1. Nil means the file is not there."
  [path]
  (let [file (io/file path)]
    (when (.isFile file)
      (let [bytes (java.nio.file.Files/readAllBytes (.toPath file))
            decoder (-> (Charset/forName "UTF-8")
                        .newDecoder
                        (.onMalformedInput CodingErrorAction/REPORT)
                        (.onUnmappableCharacter CodingErrorAction/REPORT))]
        (try
          (str (.decode decoder (ByteBuffer/wrap bytes)))
          (catch java.nio.charset.CharacterCodingException _
            (String. bytes (Charset/forName "ISO-8859-1"))))))))

(defn- unwrap
  [value]
  (if (and (utils/quote? value) (term/singleton? (term/cdr value)))
    (term/car (term/cdr value))
    value))

(defn- lisp-nil?
  [value]
  (or (nil? value)
      (and (term/km-symbol? value)
           (= "nil" (str/lower-case (term/symbol-name value))))))

(defn- stored-value
  "A quoted file value, with the symbol nil stored as the empty value."
  [value]
  (let [value (unwrap value)]
    (if (lisp-nil? value) nil value)))

(defn- t-symbol?
  [value]
  (and (term/km-symbol? value)
       (= "t" (str/lower-case (term/symbol-name value)))))

(defn- falsey?
  [value]
  (or (lisp-nil? value)
      (and (term/km-symbol? value)
           (= "f" (str/lower-case (term/symbol-name value))))))

(defn- truth?
  [value]
  (not (falsey? (unwrap value))))

(defn- keyword-name
  [value]
  (cond
    (keyword? value) (str/lower-case (name value))
    (term/km-symbol? value) (str/lower-case (term/symbol-name value))
    :else nil))

(defn- keyword-map
  [tail]
  (loop [tail tail
         acc {}]
    (cond
      (nil? tail) acc
      (not (term/cons? tail)) acc
      :else
      (let [key (keyword-name (term/car tail))
            rest (term/cdr tail)]
        (cond
          (and key (term/cons? rest))
          (recur (term/cdr rest) (assoc acc key (term/car rest)))
          key (assoc acc key nil)
          :else (recur rest acc))))))

(defn- head-is?
  [expr name]
  (and (term/cons? expr)
       (term/km-symbol? (term/car expr))
       (= name (str/lower-case (term/symbol-name (term/car expr))))))

(defn- valid-triple?
  [triple]
  (and (term/cons? triple)
       (term/km-symbol? (term/car triple))
       (term/cons? (term/cdr triple))
       (utils/eql? (term/car (term/cdr triple)) (symbol "->"))
       (term/cons? (term/cdr (term/cdr triple)))
       (nil? (term/cdr (term/cdr (term/cdr triple))))))

(defn- triples-to-alist
  [state triples]
  (let [triples (unwrap triples)]
    (if-not (and (utils/lisp-list? triples)
                 (every? valid-triple? (utils/elements triples)))
      {:state (errors/report-error
               state :nodebugger-error
               ":with-morphism: renaming table should be a list of triples of the form%n ((OldS1 -> NewS1) (OldS2 -> NewS2) ...)")
       :alist nil}
      {:state state
       :alist (mapv (fn [triple]
                      [(term/car triple) (term/car (term/cdr (term/cdr triple)))])
                    (utils/elements triples))})))

(defn- rename-symbols
  [expr alist]
  (cond
    (empty? alist) expr
    (term/km-symbol? expr)
    (or (some (fn [[old new]]
                (when (utils/eql? old expr) new))
              alist)
        expr)

    (term/cons? expr)
    (let [head (rename-symbols (term/car expr) alist)
          tail (rename-symbols (term/cdr expr) alist)]
      (if (and (identical? head (term/car expr))
               (identical? tail (term/cdr expr)))
        expr
        (term/cons-cell head tail)))

    :else expr))

(defn- needs-expand?
  [values]
  (loop [values values]
    (cond
      (nil? values) false
      (not (term/cons? values)) false
      (and (not (kb/fully-evaluated? (term/car values)))
           (not (kb/constraint-expr? (term/car values))))
      true
      :else (recur (term/cdr values)))))

(defn- refused?
  [state]
  (= "not-ported" (:error state)))

(defn- classify-loaded
  "Unify prototypes and classify one eval-instances batch.

  Prototype mode leaves use-prototypes off, so that batch stays a slot
  re-read. A number is not classified. Constraints are not checked here."
  [state instances km-int]
  (if (or (refused? state)
          (not (frame/use-prototypes? (:kb state))))
    state
    (reduce (fn [state instance]
              (if (or (refused? state) (not (kb/kb-object? instance)))
                state
                (let [unified (prototypes/unify-in-prototypes state instance nil km-int)]
                  (if (refused? unified)
                    unified
                    (classify/classify unified instance km-int)))))
            state
            (utils/elements instances))))

(defn- expand-instances
  [state instances km-int rounds]
  (cond
    (nil? instances) state
    (>= rounds 100)
    (errors/report-error state :user-error
                         "eval-instances in frame-io.lisp!%nRecursion is causing an infinite graph to be generated! Giving up...")

    :else
    (let [before (:value (frame/obj-stack (:kb state) (:query state)))
          expanded (reduce (fn [state instance]
                             (if-not (kb/kb-object? instance)
                               state
                               (let [slots (:value (frame/get-slotsvals (:kb state) instance))]
                                 (loop [slots slots
                                        state state]
                                   (cond
                                     (or (nil? slots) (not (term/cons? slots))) state
                                     (needs-expand? (frame/vals-in (term/car slots)))
                                     (let [read (km-int state
                                                        (term/km-list (symbol "the")
                                                                      (frame/slot-in (term/car slots))
                                                                      (symbol "of")
                                                                      instance)
                                                        :fail-mode :fail)]
                                       (recur (term/cdr slots) read))
                                     :else (recur (term/cdr slots) state))))))
                           state
                           (utils/elements instances))
          classed (classify-loaded expanded instances km-int)
          after (:value (frame/obj-stack (:kb classed) (:query classed)))
          fresh (loop [items after
                       acc []]
                  (cond
                    (nil? items) acc
                    (not (term/cons? items)) acc
                    (utils/member? (term/car items) before) (recur (term/cdr items) acc)
                    :else (recur (term/cdr items) (conj acc (term/car items)))))]
      (if (or (refused? classed) (empty? fresh))
        classed
        (expand-instances classed (term/build-list fresh nil) km-int (inc rounds))))))

(defn- pattern-kept?
  [expr patterns]
  (or (nil? patterns)
      (boolean (some #(match/minimatch expr %) (utils/elements patterns)))))

(defn- continue?
  [state]
  (not (contains? #{:abort :abort-silently}
                  (get-in state [:query :on-error] :continue))))

(defn- apply-setq
  [state variable value]
  (let [name (str/upper-case (term/symbol-name variable))
        value (stored-value value)
        kb (:kb state)]
    (case name
      "*LOGGING*" state
      "*MAX-PADDING-INSTANCES*"
      (assoc state :kb (assoc-in kb [:runtime :max-padding-instances] (or value 0)))
      "*INSTANCE-OF-IS-FLUENT*"
      (assoc state :kb (frame/set-instance-of-is-fluent kb (truth? value)))
      "*RECURSIVE-PROTOTYPES*"
      (assoc state :kb (assoc-in kb [:runtime :recursive-prototypes?] (truth? value)))
      "*EAGERLY-UNIFY-PROTOTYPES*"
      (assoc state :kb (assoc-in kb [:runtime :eagerly-unify-prototypes?] (truth? value)))
      "*RECORD-EXPLANATIONS*"
      (assoc state :kb (frame/set-record-explanations kb (truth? value)))
      "*RECORD-EXPLANATIONS-FOR-CLONES*"
      (assoc state :kb (assoc-in kb [:runtime :record-explanations-for-clones?] (truth? value)))
      "*DEFAULT-FLUENT-STATUS*"
      (assoc state :kb (frame/set-default-fluent-status kb value))
      "*CLASSIFICATION-ENABLED*"
      (assoc state :kb (assoc-in kb [:runtime :classification-enabled?] (truth? value)))
      "*PROTOTYPE-CLASSIFICATION-ENABLED*"
      (assoc state :kb (assoc-in kb [:runtime :prototype-classification-enabled?] (truth? value)))
      "*USE-PROTOTYPES*"
      (assoc state :kb (assoc-in kb [:runtime :use-prototypes?] (truth? value)))
      "*ACTIVE-OBJ-STACK*"
      (assoc state :kb (assoc kb :active-obj-stack? (truth? value)))
      "*SLOT-CHECKING-ENABLED*"
      (assoc state :kb (assoc-in kb [:runtime :slot-checking-enabled?] (truth? value)))
      "*KM-GENSYM-COUNTER*"
      (assoc state :kb (assoc kb :counter (long (or value 0))))
      "*VISIBLE-THEORIES*"
      (assoc state :kb (frame/set-visible-theories kb value))
      "*CURR-PROTOTYPE*"
      (assoc state :kb (frame/set-curr-prototype kb value))
      "*CURR-SITUATION*"
      (if (kb/kb-object? value)
        (assoc state :kb (frame/set-situation kb value
                                              :theory? (frame/theory-situation? kb value)))
        state)
      "*CLASSES-USING-ASSERTIONS-SLOT*"
      (assoc state :kb (assoc-in kb [:runtime :classes-using-assertions] value))
      "*ARE-SOME-DEFINITIONS*"
      (assoc state :kb (frame/set-are-some kb :definitions (truth? value)))
      "*ARE-SOME-PROTOTYPE-DEFINITIONS*"
      (assoc state :kb (frame/set-are-some kb :prototype-definitions (truth? value)))
      "*ARE-SOME-PROTOTYPES*"
      (assoc state :kb (frame/set-are-some kb :prototypes (truth? value)))
      "*ARE-SOME-SUBSLOTS*"
      (assoc state :kb (frame/set-are-some kb :subslots (truth? value)))
      "*ARE-SOME-CONSTRAINTS*"
      (assoc state :kb (frame/set-are-some kb :constraints (truth? value)))
      "*ARE-SOME-TAGS*"
      (assoc state :kb (frame/set-are-some kb :tags (truth? value)))
      "*ARE-SOME-DEFAULTS*"
      (assoc state :kb (frame/set-are-some kb :defaults (truth? value)))
      "*AM-IN-SITUATIONS-MODE*"
      (assoc state :kb (assoc-in kb [:runtime :situations-mode?] (truth? value)))
      "*VERBOSE-NUMBER-TO-TEXT*"
      (assoc state :kb (assoc-in kb [:runtime :verbose-number-to-text?] (truth? value)))
      "*OUTPUT-PRECISION*"
      (if (number? value)
        (assoc state :kb (assoc-in kb [:runtime :output-precision] value))
        (errors/report-error state :user-error
                             "Lisp setq is refused: (SETQ %s %s)."
                             (print/km-format variable)
                             (print/km-format value)))
      "*DEFAULT-KM-BEHAVIOR-FOR-EXPAND-TEXT*"
      (assoc state :kb (assoc-in kb [:runtime :default-km-behavior-for-expand-text?]
                                 (truth? value)))
      "*JUSTIFY-LEAVES*"
      (assoc state :kb (assoc-in kb [:runtime :justify-leaves?] (truth? value)))
      "*DEVELOPER-MODE*"
      (assoc state :kb (assoc-in kb [:runtime :developer-mode?] (truth? value)))
      "*RESET-STATISTICS-ENABLED*"
      (assoc state :kb (assoc-in kb [:runtime :reset-statistics-enabled?] (truth? value)))
      "*INFERENCE-REPORT-FREQUENCY*"
      (cond
        (nil? value)
        (assoc state :kb (assoc-in kb [:runtime :inference-report-frequency] nil))
        (number? value)
        (assoc state :kb (assoc-in kb [:runtime :inference-report-frequency] value))
        :else
        (errors/report-error state :user-error
                             "Lisp setq is refused: (SETQ %s %s)."
                             (print/km-format variable)
                             (print/km-format value)))
      "*SHOW-COMMENTS*"
      (assoc state :kb (assoc-in kb [:runtime :show-comments?] (truth? value)))
      "*TRACE*"
      (assoc state :kb (assoc-in kb [:runtime :trace?] (truth? value)))
      "*INTERACTIVE-TRACE*"
      (assoc state :kb (assoc-in kb [:runtime :interactive-trace?] (truth? value)))
      "*TRACE-CLASSIFY*"
      (assoc state :kb (assoc-in kb [:runtime :trace-classify?] (truth? value)))
      "*TRACE-UNIFY*"
      (assoc state :kb (assoc-in kb [:runtime :trace-unify?] (truth? value)))
      "*TRACE-SUBSUMES*"
      (assoc state :kb (assoc-in kb [:runtime :trace-subsumes?] (truth? value)))
      "*TRACE-CONSTRAINTS*"
      (assoc state :kb (assoc-in kb [:runtime :trace-constraints?] (truth? value)))
      "*TRACE-OTHER-SITUATIONS*"
      (assoc state :kb (assoc-in kb [:runtime :trace-other-situations?] (truth? value)))
      "*TRACE-TO-FILE?*"
      (assoc state :kb (assoc-in kb [:runtime :trace-to-file?] (truth? value)))
      "*TRACE-FILE*"
      (cond
        (nil? value)
        (assoc state :kb (assoc-in kb [:runtime :trace-file] "%trace.km"))
        (string? value)
        (assoc state :kb (assoc-in kb [:runtime :trace-file] value))
        :else
        (errors/report-error state :user-error
                             "Lisp setq is refused: (SETQ %s %s)."
                             (print/km-format variable)
                             (print/km-format value)))
      (errors/report-error state :user-error
                           "Lisp setq is refused: (SETQ %s %s)."
                           (print/km-format variable)
                           (print/km-format value)))))

(defn- load-one
  [state expr km-int alist options]
  (let [expr (rename-symbols expr alist)]
    (cond
      (nil? expr) {:state state :done? true :alist alist}

      (head-is? expr "symbol-renaming-table")
      (let [converted (triples-to-alist
                       (add-text state "(Symbol renaming table encountered and will be conformed to)\n")
                       (term/car (term/cdr expr)))]
        {:state (:state converted) :done? false :alist (or (:alist converted) alist)})

      (not (pattern-kept? expr (:patterns options)))
      {:state state :done? false :alist alist}

      (head-is? expr "setq")
      (let [variable (term/car (term/cdr expr))
            value (term/car (term/cdr (term/cdr expr)))]
        (if-not (term/km-symbol? variable)
          {:state (errors/report-error state :user-error
                                       "Lisp setq is refused: %s."
                                       (print/km-format expr))
           :done? (not (continue? state))
           :alist alist}
          (let [applied (apply-setq state variable value)]
            {:state applied
             :done? (and (not (continue? applied))
                         (> (count (:errors applied)) (count (:errors state))))
             :alist alist})))

      :else
      (let [state (if (:verbose options)
                    (-> state
                        (add-text (situations/prompt-text (:kb state)))
                        (add-text " ")
                        (add-text (print/km-format expr))
                        (add-text "\n"))
                    state)
            result (km-int (assoc state :query (assoc (:query state) :instances-being-unified nil))
                           expr
                           :fail-mode (or (:top-level-fail-mode (:query state)) :fail))]
        (cond
          (= "not-ported" (:error result))
          {:state (add-text result (str "Loading of " (:file options) " aborted!\n"))
           :done? true
           :alist alist}

          (and (seq (:errors result))
               (> (count (:errors result)) (count (:errors state)))
               (not (continue? result)))
          {:state (add-text result (str "Loading of " (:file options) " aborted!\n"))
           :done? true
           :alist alist}

          :else
          (let [result (if (or (:eval-instances options)
                               (frame/curr-prototype (:kb result)))
                         (expand-instances result (:value result) km-int 0)
                         result)
                result (if (:verbose options)
                         (add-text result (str (print/km-format (:value result)) "\n"))
                         result)]
            {:state result :done? false :alist alist}))))))

(defn- load-text
  [state text km-int options]
  (let [logging (get-in state [:kb :runtime :logging?])
        creations (get-in state [:kb :runtime :logging-creations?])
        kb (-> (:kb state)
               (assoc-in [:runtime :logging?] false)
               (assoc-in [:runtime :logging-creations?] false)
               (frame/set-situation term/global-situation))
        state (assoc state :kb kb)
        alist (or (:alist options) (:renaming kb))]
    (loop [index 0
           state state
           alist alist]
      (let [read (read/read-next text index)]
        (cond
          (= "empty" (:error read))
          (let [kb (-> (:kb state)
                       frame/reset-done
                       (assoc :renaming (if (:clear-renaming? options) nil alist))
                       (assoc-in [:runtime :logging?] (boolean logging))
                       (assoc-in [:runtime :logging-creations?] (boolean creations)))]
            (let [finished (cond-> (one (assoc state :kb kb) (symbol "t"))
                             (not (:silent options))
                             (add-text (str (:file options) " loaded!\n")))]
              (if (:print-statistics options)
                (add-text finished (stats/report (:kb finished) (:query finished)))
                finished)))

          (not (:ok read))
          (add-text (none (errors/report-error state :user-error "%s" (:message read)))
                    (str "Loading of " (:file options) " aborted!\n"))

          :else
          (let [step (try
                       (load-one state (:value read) km-int alist options)
                       (catch clojure.lang.ExceptionInfo thrown
                         (if (errors/abort-exception? thrown)
                           {:state (add-text (:state (ex-data thrown))
                                             (str "Loading of " (:file options) " aborted!\n"))
                            :done? true
                            :alist alist}
                           (throw thrown))))]
            (if (:done? step)
              (let [kb (-> (:kb (:state step))
                           (assoc-in [:runtime :logging?] (boolean logging))
                           (assoc-in [:runtime :logging-creations?] (boolean creations)))]
                (none (assoc (:state step) :kb kb)))
              (recur (:end read) (:state step) (:alist step)))))))))

(defn- file-missing
  [state file]
  (none (errors/report-error state :user-error "No such file %s!" file)))

(defn load-file
  "Evaluate the expressions in file.

  with-morphism renames symbols before each expression is evaluated.
  A missing file records an error and answers nil. The loaded text
  includes (reset-kb) when it was written by save-kb."
  [state file km-int & {:keys [verbose with-morphism eval-instances load-patterns
                               print-statistics silent]}]
  (let [state (if (truth? silent)
                state
                (add-text state (str "Loading " file "...\n")))]
    (if-let [text (read-file-text file)]
    (let [converted (if (nil? with-morphism)
                      {:state state :alist (:renaming (:kb state))}
                      (triples-to-alist state with-morphism))
          options {:verbose (truth? verbose)
                   :eval-instances (truth? eval-instances)
                   :patterns (unwrap load-patterns)
                   :print-statistics (truth? print-statistics)
                   :silent (truth? silent)
                   :file (str file)
                   :alist (:alist converted)
                   :clear-renaming? (some? with-morphism)}]
      (load-text (:state converted) text km-int options))
      (file-missing state file))))

(defn reload-file
  "Reset the knowledge base, then load file.

  The query's object stack and goal stack are cleared by the reset.
  Inference counters on the query stay, and the file's (reset-kb) runs
  again when the saved text includes it."
  [state file km-int options]
  (let [rebuilt (frame/reset (:kb state) :query (:query state))]
    (load-file (assoc state :kb (:kb rebuilt) :query (:query rebuilt))
               file km-int options)))

(defn save-file
  "Write the knowledge base to file as UTF-8 KM text.

  The text is the same on a second save of the same value. reset-kb?
  includes the reset and the disable commands. Explanations are included
  unless include-explanations? is false."
  [state file & {:keys [reset-kb? include-explanations?]
                 :or {reset-kb? true include-explanations? true}}]
  (try
    (let [text (writer/write-kb-text (:kb state)
                                     :reset-kb? reset-kb?
                                     :include-explanations? include-explanations?)]
      (spit file text :encoding "UTF-8")
      (noted state (str file " saved!\n") (symbol "t")))
    (catch java.io.IOException thrown
      (none (errors/report-error state :user-error "No such file %s!"
                                 (or (.getMessage thrown) file))))))

(defn write-command-text
  "The text write-kb would send to the terminal.

  A stream argument other than t is an error. The answer is (t)."
  [state & {:keys [reset-kb? include-explanations? situations]
            :or {reset-kb? true include-explanations? true}}]
  (let [text (writer/write-kb-text (:kb state)
                                   :reset-kb? reset-kb?
                                   :include-explanations? include-explanations?
                                   :situations situations)]
    (noted state text (symbol "t"))))

(defn- option-flag
  [value default]
  (if (nil? value) default (truth? value)))

(defn load-command
  "Run a (load-kb ...) or (reload-kb ...) form."
  [state expr km-int reload?]
  (let [file (term/car (term/cdr expr))
        options (keyword-map (term/cdr (term/cdr expr)))
        file (unwrap file)]
    (if-not (string? file)
      (none (errors/report-error state :user-error "No such file %s!"
                                 (print/km-format file)))
      (let [args {:verbose (get options "verbose")
                  :with-morphism (get options "with-morphism")
                  :eval-instances (get options "eval-instances")
                  :load-patterns (get options "load-patterns")
                  :print-statistics (get options "print-statistics")
                  :silent (get options "silentp")}]
        (if reload?
          (reload-file state file km-int args)
          (load-file state file km-int args))))))

(defn save-command
  "Run a (save-kb file) form."
  [state expr]
  (let [file (unwrap (term/car (term/cdr expr)))
        options (keyword-map (term/cdr (term/cdr expr)))]
    (if-not (string? file)
      (none (errors/report-error state :user-error "No such file %s!"
                                 (print/km-format file)))
      (save-file state file
                 :reset-kb? (option-flag (get options "reset-kb") true)
                 :include-explanations? (option-flag (get options "include-explanationsp") true)))))

(defn write-command
  "Run a (write-kb) form. The text is returned on :text."
  [state expr]
  (let [options (keyword-map (term/cdr expr))
        stream (get options "stream")]
    (if (and (some? stream)
             (not (falsey? (unwrap stream)))
             (not (t-symbol? (unwrap stream))))
      (none (errors/report-error state :user-error
                                 "write-kb given a non-stream as an argument!%n(Use (save-kb \"myfile\") to save KB to the file called \"myfile\")"))
      (write-command-text state
                          :reset-kb? (option-flag (get options "reset-kb") true)
                          :include-explanations? (option-flag (get options "include-explanationsp") true)
                          :situations (unwrap (get options "situations"))))))

(defn logging-command
  "Run one logging, creation, store, or disable command.

  Nil means this name is not one of those commands."
  [state expr name]
  (let [arg (unwrap (term/car (term/cdr expr)))]
    (case name
      "start-logging" (start-logging state)
      "stop-logging" (stop-logging state)
      "set-checkpoint"
      (let [id (or arg (symbol "t"))
            kb (set-checkpoint (:kb state) id)]
        (if (logging? kb)
          (one (assoc state :kb kb) (symbol "t"))
          (none state)))
      "start-creations-logging" (start-creations-logging state)
      "stop-creations-logging" (stop-creations-logging state)
      "set-creations-checkpoint"
      (set-creations-checkpoint state (or arg (symbol "checkpoint")))
      "undo-creations"
      (undo-creations state (or arg (symbol "checkpoint")))
      "store-kb" (store-kb state)
      "restore-kb" (restore-kb state)
      "disable-slot-checking"
      (one (assoc-in state [:kb :runtime :slot-checking-enabled?] false) (symbol "t"))
      "enable-slot-checking"
      (one (assoc-in state [:kb :runtime :slot-checking-enabled?] true) (symbol "t"))
      "disable-classification"
      (one (assoc state :kb (frame/set-classification (:kb state) false)) (symbol "t"))
      "enable-classification"
      (one (assoc state :kb (frame/set-classification (:kb state) true)) (symbol "t"))
      "disable-installing-inverses"
      (one (assoc state :kb (frame/set-installing-inverses (:kb state) false)) (symbol "t"))
      "enable-installing-inverses"
      (one (assoc state :kb (frame/set-installing-inverses (:kb state) true)) (symbol "t"))
      nil)))

(defn checkpoint-command
  "Run (checkpoint) or (checkpoint id). The answer is (t).

  A nil id records an error. The checkpoint is stored only while logging
  is on. The answer is (t) either way."
  [state id]
  (cond
    (lisp-nil? id)
    (none (errors/report-error state :user-error
                               "(checkpoint %s): Argument to checkpoint can't be NIL!"
                               (print/km-format id)))

    :else
    (one (assoc state :kb (set-checkpoint (:kb state) id)) (symbol "t"))))

(defn undo-command
  "Run (undo) or (undo id).

  At depth 0 the text is the prompt's Undone line, or the line that
  says there is nothing left. A nested call answers (t) or nil and does
  not add that line."
  [state id]
  (let [found (undo (:kb state) id)
        top? (zero? (or (get-in state [:query :depth]) 0))]
    (cond
      (:exhausted? found)
      (if top?
        (add-text (none (assoc state :kb (:kb found))) "Nothing more to undo!\n\n")
        (none (assoc state :kb (:kb found))))

      top?
      (noted (assoc state :kb (:kb found))
             (str "Undone " (print/km-format (:id found)) "...\n\n")
             (symbol "t"))

      :else
      (one (assoc state :kb (:kb found)) (symbol "t")))))
