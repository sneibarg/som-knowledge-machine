(ns som.km.trace
  "Trace lines for one Knowledge Machine query.

  The same interpreter calls record a line. This is not a second
  evaluator. The line is appended to :text, and also to the named file
  when trace-to-file is on. The interactive menu is not read. Evaluation
  continues. Nothing here returns redo or fail.

  Trace depth is its own counter. The depth ceiling stays on :depth.
  A name lookup suspends the flag itself and does not call this
  namespace."
  (:require [clojure.string :as str]
            [som.km.errors :as errors]
            [som.km.explain :as explain]
            [som.km.minimatch :as match]
            [som.km.print :as print]
            [som.km.term :as term]
            [som.km.utils :as utils])
  (:import [java.io FileOutputStream]))

(defn- pad-to
  "Pad to a column. Past that column, one space is written.

  This is ~T with a column increment of 1."
  [^StringBuilder sb column]
  (let [text (str sb)
        break (str/last-index-of text \newline)
        column-now (if (nil? break) (count text) (- (count text) break 1))
        target (if (< column-now column) column (inc column-now))]
    (dotimes [_ (- target column-now)]
      (.append sb \space))))

(defn format-km
  "Interpret ~a, ~%, and ~NT in one Knowledge Machine format string.

  ~a is km-format of the next argument. ~% is a newline. ~NT pads to
  column N. Any other character after a tilde is written as itself,
  including the tilde."
  [template args]
  (let [sb (StringBuilder.)
        n (count template)]
    (loop [i 0
           args (seq args)]
      (if (>= i n)
        (str sb)
        (let [ch (nth template i)]
          (if (and (= \~ ch) (< (inc i) n))
            (let [directive (nth template (inc i))]
              (cond
                (= directive \a)
                (do (.append sb (print/km-format (first args)))
                    (recur (+ i 2) (next args)))

                (= directive \%)
                (do (.append sb \newline)
                    (recur (+ i 2) args))

                (Character/isDigit ^char directive)
                (let [end (loop [j (inc i)]
                            (if (and (< j n) (Character/isDigit ^char (nth template j)))
                              (recur (inc j))
                              j))
                      marker (when (< end n) (nth template end))]
                  (if (= marker \T)
                    (do (pad-to sb (Long/parseLong (subs template (inc i) end)))
                        (recur (inc end) args))
                    (do (.append sb \~)
                        (recur (inc i) args))))

                :else
                (do (.append sb \~)
                    (recur (inc i) args))))
            (do (.append sb ch)
                (recur (inc i) args))))))))

(defn- truncate
  "The first maxlen characters, then \"...\", once the text is longer.

  A shorter text is kept. The comparison is strict, so a text of exactly
  maxlen is kept."
  [text maxlen]
  (if (< (count text) maxlen)
    text
    (str (subs text 0 maxlen) "...")))

(defn- indent
  "The depth digits and the spaces that follow them.

  The pad is one more than the depth, minus the number of digits. A
  comment has one more space. A negative pad is written as nothing."
  [depth comment?]
  (let [digits (str depth)
        pad (max 0 (- (inc depth) (count digits)))]
    (str digits (apply str (repeat pad \space)) (when comment? " "))))

(defn- append-file
  "Append line to path. A failure is recorded and the query continues."
  [state path line]
  (try
    (let [out (FileOutputStream. (str path) true)]
      (try
        (.write out (.getBytes ^String line "UTF-8"))
        state
        (finally
          (.close out))))
    (catch Exception thrown
      (errors/report-error state :user-error
                           "Could not write the trace file %s: %s"
                           (str path)
                           (.getMessage thrown)))))

(defn- emit
  "Append one trace line to :text, and to the trace file when that is on.

  Exit and fail truncate the formatted message to 80 characters before
  the indent is added. The line ends with a newline. The menu that would
  read a key is not called."
  [state mode template args]
  (let [depth (or (:trace-depth (:query state)) 0)
        formatted (format-km template (map explain/desource-for-printing args))
        body (if (#{:exit :fail} mode) (truncate formatted 80) formatted)
        line (str (indent depth (= mode :comment)) body "\n")
        state (update state :text #(str % line))]
    (if (get-in state [:kb :runtime :trace-to-file?] false)
      (append-file state (or (get-in state [:kb :runtime :trace-file]) "%trace.km") line)
      state)))

(defn reset-trace
  "Turn both trace flags on when either one is on, and clear the finer switches.

  The trace depth is left as it is. The trace file, the spypoints, and
  comment display stay. A later top-level query calls this, so a trace
  that was left on comes back on."
  [kb]
  (let [on? (or (get-in kb [:runtime :trace?] false)
                (get-in kb [:runtime :interactive-trace?] false))
        kb (if on?
             (-> kb
                 (assoc-in [:runtime :trace?] true)
                 (assoc-in [:runtime :interactive-trace?] true))
             kb)]
    (-> kb
        (assoc-in [:runtime :suspended-trace] nil)
        (assoc-in [:runtime :trace-classify?] false)
        (assoc-in [:runtime :trace-unify?] false)
        (assoc-in [:runtime :trace-subsumes?] false)
        (assoc-in [:runtime :trace-constraints?] false)
        (assoc-in [:runtime :trace-other-situations?] false))))

(defn- announce
  [state text]
  (assoc state :text (str (:text state) text)))

(defn- say
  [state text]
  (assoc (announce state text) :value (term/km-list (symbol "t"))))

(defn activate-trace
  "Turn tracing on and record the Lisp sentence.

  The trace depth and the answer are left as they are. A spy uses this.
  The (trace) command zeroes the depth and answers (t)."
  [state]
  (let [state (assoc state :kb (reset-trace (:kb state)))]
    (if (get-in state [:kb :runtime :trace?] false)
      (announce state "(Tracing of KM is already switched on)\n")
      (-> state
          (assoc-in [:kb :runtime :trace?] true)
          (assoc-in [:kb :runtime :interactive-trace?] true)
          (announce "(Tracing of KM switched on)\n")))))

(defn trace-command
  "The (trace) and (tracekm) command.

  The depth is set to 0, then tracing is turned on. The answer is (t).
  This command does not push a goal."
  [state]
  (assoc (activate-trace (assoc-in state [:query :trace-depth] 0))
         :value (term/km-list (symbol "t"))))

(defn untrace-command
  "The (untrace) and (untracekm) command.

  The depth is set to 0. Both trace flags are cleared when tracing is
  on. The answer is (t)."
  [state]
  (let [state (-> state
                  (assoc-in [:query :trace-depth] 0)
                  (assoc :kb (reset-trace (:kb state))))]
    (if (get-in state [:kb :runtime :trace?] false)
      (-> state
          (assoc-in [:kb :runtime :trace?] false)
          (assoc-in [:kb :runtime :interactive-trace?] false)
          (say "(Tracing of KM switched off)\n"))
      (say state "(Tracing of KM is already switched off)\n"))))

(defn- unsuspend
  "Turn tracing back on once the depth has returned to the suspended depth.

  Nothing in this port sets the suspended depth. The menu that would is
  not read. The check is still made, so a stored depth can release."
  [state mode]
  (let [suspended (get-in state [:kb :runtime :suspended-trace])
        depth (or (:trace-depth (:query state)) 0)]
    (if (and (not (get-in state [:kb :runtime :trace?] false))
             (not= mode :comment)
             (some? suspended)
             (<= depth suspended))
      (-> state
          (assoc-in [:kb :runtime :suspended-trace] nil)
          (assoc-in [:kb :runtime :trace?] true))
      state)))

(defn km-trace
  "Record one call, exit, fail, or comment line.

  A call increments the trace depth and updates the maximum depth first,
  including when the trace flag is off. An exit or a fail decrements the
  depth after the line. A comment leaves the depth as it is. The line is
  written only when tracing is on."
  [state mode template args]
  (let [state (if (= mode :call)
                (let [depth (or (get-in state [:query :trace-depth]) 0)
                      max-depth (or (get-in state [:query :max-depth]) 0)]
                  (assoc state :query
                         (assoc (:query state)
                                :max-depth (if (>= depth max-depth) (inc depth) max-depth)
                                :trace-depth (inc depth))))
                state)
        state (unsuspend state mode)
        state (if (get-in state [:kb :runtime :trace?] false)
                (emit state mode template args)
                state)]
    (if (#{:exit :fail} mode)
      (update-in state [:query :trace-depth] (fnil dec 0))
      state)))

(defn make-comment
  "Append one comment line when comment display is on.

  The line is \"(COMMENT: \" and the formatted text and \")\". Comment
  display starts on. Older messages that this port never printed stay
  silent. Only a caller that uses this function produces a comment."
  [state template args]
  (if (get-in state [:kb :runtime :show-comments?] true)
    (let [body (format-km template (map explain/desource-for-printing args))]
      (update state :text #(str % "(COMMENT: " body ")\n")))
    state))

(defn comments-command
  "The (comments) command. The answer is (t)."
  [state]
  (if (get-in state [:kb :runtime :show-comments?] true)
    (say state "(Display of comments is already switched on)\n")
    (-> state
        (assoc-in [:kb :runtime :show-comments?] true)
        (say "(Display of comments is switched on)\n"))))

(defn nocomments-command
  "The (nocomments) command.

  An already silent display records nothing. The answer is still (t)."
  [state]
  (if (get-in state [:kb :runtime :show-comments?] true)
    (-> state
        (assoc-in [:kb :runtime :show-comments?] false)
        (say "(Display of comments is switched off)\n"))
    (assoc state :value (term/km-list (symbol "t")))))

(defn trace-to-file-on
  "Start appending trace lines to a file. The answer is (t).

  A missing name keeps the stored name, which starts as \"%trace.km\".
  A name that is not a string is recorded as a user error and the stored
  name stays."
  [state filename]
  (let [state (assoc-in state [:kb :runtime :trace-to-file?] true)
        state (cond
                (nil? filename) state
                (string? filename) (assoc-in state [:kb :runtime :trace-file] filename)
                :else (errors/report-error state :user-error
                                           "trace-to-file-on expected a string file name, and got %s."
                                           (print/km-format filename)))]
    (say state "(Trace-to-file switched on)\n")))

(defn trace-to-file-off
  "Stop appending trace lines to a file. The answer is (t)."
  [state]
  (-> state
      (assoc-in [:kb :runtime :trace-to-file?] false)
      (say "(Trace-to-file switched off)\n")))

(defn- spy-listing
  [points]
  (if (seq points)
    (str "The tracer will automatically switch on when evaluating these expressions/patterns:\n"
         (apply str (map #(str "      " (print/km-format %) "\n") points)))
    "(You have no spypoints declared)\n"))

(defn spy-command
  "Add one spypoint, or list the spypoints when expr is nil.

  A pattern already stored, by equal?, is not added again. The newest
  pattern is first. The answer is (t). &rest needs no substitution here:
  the reader and the matcher use the same symbol."
  [state expr]
  (let [points (vec (get-in state [:kb :runtime :spypoints] []))
        points (if (and (some? expr)
                        (not (some #(utils/equal? expr %) points)))
                 (into [expr] points)
                 points)]
    (-> state
        (assoc-in [:kb :runtime :spypoints] points)
        (say (spy-listing points)))))

(defn unspy-command
  "Remove every spypoint. The answer is (t)."
  [state]
  (-> state
      (assoc-in [:kb :runtime :spypoints] [])
      (say "(All spypoints removed)\n")))

(defn check-spy
  "Turn tracing on when expr matches a spypoint.

  The check runs before the expression is evaluated. A match records
  \"(Spypoint reached!)\" and then the trace-on sentence."
  [state expr]
  (let [points (get-in state [:kb :runtime :spypoints])]
    (if (and (seq points)
             (some #(some? (match/minimatch expr %)) points))
      (-> state
          (update :text #(str % "(Spypoint reached!)\n"))
          activate-trace)
      state)))
