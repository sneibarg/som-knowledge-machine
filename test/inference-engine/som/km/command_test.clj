(ns som.km.command-test
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.print :as print]
            [som.km.read :as read]
            [som.km.term :as term]
            [som.km.utils :as utils]))

(defn- term-of [text]
  (:value (read/read-term text)))

(defn- answer [text]
  (engine/evaluate text))

(defn- on
  [previous text]
  (engine/evaluate text {:kb (:kb previous) :query (:query previous)}))

(defn- slash [path]
  (str/replace path "\\" "/"))

(defn- temp-path [suffix]
  (.getAbsolutePath (java.io.File/createTempFile "km-step25-" suffix)))

(defmacro with-temp
  [binding & body]
  `(let [~binding (temp-path ".km")]
     (try
       ~@body
       (finally
         (io/delete-file ~binding true)))))

(defn- skolems [result]
  (or (get-in result [:query :skolems]) 0))

(deftest showme-prints-the-frame-and-an-empty-result-says-so
  (let [stored (answer "(Fred has (color (red)))")
        shown (on stored "(showme Fred)")
        empty (on stored "(showme (the color of Sue))")
        sue (on stored "(Sue has (color (blue)))")
        both (on sue "(showme (:set Fred Sue))")]
    (is (= (term-of "(Fred)") (:value shown)))
    (is (nil? (:error shown)))
    (is (str/includes? (:text shown) "(Fred has"))
    (is (str/includes? (:text shown) "(color (red))"))
    (is (nil? (:value empty)))
    (is (str/includes? (:text empty) "No frames to show"))
    (is (str/includes? (:text both) ";;; ----------"))
    (is (utils/member? (symbol "Fred") (:value both)))
    (is (utils/member? (symbol "Sue") (:value both)))))

(deftest showme-here-and-a-file-use-the-same-frame-text
  (with-temp path
    (let [stored (answer "(Fred has (color (red)))")
          here (on stored "(showme-here Fred)")
          filed (on stored (str "(showme Fred \"" (slash path) "\")"))
          written (slurp path :encoding "UTF-8")
          missing (on stored (str "(showme (the color of Sue) \"" (slash path) "\")"))
          emptied (slurp path :encoding "UTF-8")
          bad (answer "(showme Fred 1)")]
      (is (= (term-of "(Fred)") (:value here)))
      (is (str/includes? (:text here) "(Fred has"))
      (is (str/includes? written "(Fred has"))
      (is (str/includes? written "(color (red))"))
      (is (str/includes? (:text filed) "Output sent to file"))
      (is (str/includes? (:text filed) (str "\"" (slash path) "\"")))
      (is (str/includes? (:text missing) "No frames to show"))
      (is (str/includes? (:text missing) "Output sent to file"))
      (is (= "" emptied))
      (is (nil? (:value bad)))
      (is (some #(re-find #"should be a string" %) (:errors bad))))))

(deftest showme-all-sorts-slot-names-and-joins-rule-sets
  (let [aged (answer "(Fred has (color (red)) (Age (3)))")
        ordered (on aged "(showme-all Fred)")
        ruled (answer "(every Cat has (color (black)))")
        cat (on ruled "(_Cat1 has (instance-of (Cat)) (color (red)))")
        shown (on cat "(showme-all _Cat1)")
        text (:text ordered)]
    (is (= (term-of "(Fred)") (:value ordered)))
    (is (str/includes? text "(Fred has"))
    (is (str/includes? text "\n  (Age (3))"))
    (is (str/includes? text "\n  (color (red))"))
    (is (< (.indexOf text "\n  (Age ") (.indexOf text "\n  (color ")))
    (is (str/includes? (:text shown)
                       "  (color ((   (red)\n           && (black)))"))))

(deftest most-specific-and-most-general-follow-the-taxonomy
  (let [animal (answer "(Animal has (superclasses (Thing)))")
        cat (on animal "(Cat has (superclasses (Animal)))")
        specific (on cat "(the most-specific of (:set Animal Cat))")
        general (on specific "(the most-general of (:set Animal Cat))")]
    (is (= (term-of "(Cat)") (:value specific)))
    (is (= (term-of "(Animal)") (:value general)))
    (is (nil? (:error specific)))
    (is (nil? (:error general)))))

(deftest evaluate-all-prints-a-declared-slot
  (let [stored (answer "(Fred has (color (red)))")
        slot (on stored "(color has (instance-of (Slot)))")
        shown (on slot "(evaluate-all Fred)")]
    (is (= (term-of "(Fred)") (:value shown)))
    (is (nil? (:error shown)))
    (is (str/includes? (:text shown) "(Fred has"))
    (is (str/includes? (:text shown) "  (color (red))"))))

(deftest thelast-is-the-newest-stacked-instance
  (let [first-cat (answer "(a Cat)")
        second-cat (on first-cat "(a Cat)")
        latest (on second-cat "(thelast Cat)")
        none (on second-cat "(thelast Dog)")]
    (is (utils/eql? (term/car (:value second-cat)) (term/car (:value latest))))
    (is (not (utils/eql? (term/car (:value first-cat)) (term/car (:value latest)))))
    (is (nil? (:value none)))
    (is (empty? (:errors latest)))))

(deftest has-value-and-exists-answer-whether-the-expression-produced-a-value
  (let [stored (answer "(Fred has (color (red)))")
        filled (on stored "(has-value (the color of Fred))")
        missing (on stored "(has-value (the color of Sue))")
        named (answer "(has-value Fred)")
        summed (answer "(has-value (1 + 2))")
        empty (answer "(has-value nil)")
        renamed (on stored "(exists (the color of Fred))")
        warning (first (:warnings renamed))]
    (is (= (term-of "(t)") (:value filled)))
    (is (nil? (:value missing)))
    (is (= (term-of "(t)") (:value named)))
    (is (= (term-of "(t)") (:value summed)))
    (is (nil? (:value empty)))
    (is (= (term-of "(t)") (:value renamed)))
    (is (str/includes? warning "renamed"))
    (is (str/includes? warning "Please update your KB"))
    (is (nil? (:error renamed)))))

(deftest is-true-accepts-a-triple-and-rejects-anything-else
  (let [stored (answer "(Fred has (color (red)))")
        yes (on stored "(is-true (:triple Fred color red))")
        no (on stored "(is-true (:triple Fred color blue))")
        open (on stored "(is-true (:triple Fred color nil))")
        compared (answer "(is-true (:triple (1 + 2) > 0))")
        smaller (answer "(is-true (:triple (1 + 2) > 5))")
        broken (answer "(is-true (1 + 2))")]
    (is (= (term-of "(t)") (:value yes)))
    (is (nil? (:value no)))
    (is (= (term-of "(t)") (:value open)))
    (is (= (term-of "(t)") (:value compared)))
    (is (nil? (:value smaller)))
    (is (nil? (:value broken)))
    (is (some #(re-find #"should evaluate to a triple" %) (:errors broken)))
    (is (empty? (:errors yes)))))

(deftest all-true-and-some-true-walk-the-triples
  (let [stored (answer "(Fred has (color (red)))")
        all (on stored "(all-true (:set (:triple Fred color red) (:triple Fred age nil)))")
        stopped (on stored "(all-true (:set (:triple Fred color blue) (:triple Fred color red)))")
        none (answer "(all-true nil)")
        one (on stored "(some-true (:set (:triple Fred color blue) (:triple Fred color red)))")
        empty (answer "(some-true nil)")]
    (is (= (term-of "(t)") (:value all)))
    (is (nil? (:value stopped)))
    (is (= (term-of "(t)") (:value none)))
    (is (= (term-of "(t)") (:value one)))
    (is (nil? (:value empty)))))

(deftest print-and-format-write-the-value-list
  (let [printed (answer "(print (1 + 2))")
        returned (answer "(format nil \"~a\" (1 + 2))")
        written (answer "(format t \"~a\" 1)")
        silent (answer "(format NIL \"~a\" 1)")
        quoted (answer "(km-format nil \"~a\" \"hi\")")
        plain (answer "(format nil \"~a\" \"hi\")")
        bad (answer "(format 1 \"~a\" (a Cat))")
        upper (answer "(format T \"~a\" 1)")
        control (answer "(format t 1)")
        short (answer "(format nil \"~a\")")
        unknown (answer "(format nil \"~q\" 1)")]
    (is (= (term-of "(3)") (:value printed)))
    (is (str/includes? (:text printed) "(3)\n"))
    (is (= "(3)" (term/car (:value returned))))
    (is (= (term-of "(t)") (:value written)))
    (is (str/includes? (:text written) "(1)"))
    (is (= "(1)" (term/car (:value silent))))
    (is (str/includes? (term/car (:value quoted)) "\"hi\""))
    (is (= "(hi)" (term/car (:value plain))))
    (is (nil? (:value bad)))
    (is (zero? (skolems bad)))
    (is (some #(re-find #"Second argument" %) (:errors bad)))
    (is (nil? (:value upper)))
    (is (some #(re-find #"Second argument" %) (:errors upper)))
    (is (nil? (:value control)))
    (is (some #(re-find #"format control must be a string" %) (:errors control)))
    (is (nil? (:value short)))
    (is (some #(re-find #"Not enough arguments" %) (:errors short)))
    (is (nil? (:value unknown)))
    (is (some #(re-find #"Unknown format directive" %) (:errors unknown)))))

(deftest do-script-runs-the-actions-in-a-situation
  (let [idle (answer "(Script has (name (\"s\")))")
        skipped (on idle "(do-script Script)")
        sit (answer "(new-situation)")
        script (on sit "(Script has (actions (_Move)))")
        move (on script "(_Move has (add-list ((:triple Fred color green))))")
        done (on move "(do-script Script)")
        seen (on done "(the color of Fred)")]
    (is (nil? (:value skipped)))
    (is (empty? (:errors skipped)))
    (is (:ok done))
    (is (nil? (:error done)))
    (is (empty? (:errors done)))
    (is (= (term-of "(green)") (:value seen)))))

(deftest in-every-situation-runs-on-a-new-situation-and-reloads
  (with-temp path
    (let [ruled (answer "(in-every-situation Situation (TheSituation has (color (red))))")
          made (on ruled "(a Situation)")
          name (term/car (:value made))
          seen (on made (str "(in-situation " (print/km-format name)
                             " (the color of " (print/km-format name) "))"))
          self (answer "(in-every-situation Situation (Self has (color (blue))))")
          self-made (on self "(a Situation)")
          self-name (term/car (:value self-made))
          self-color (on self-made
                         (str "(in-situation " (print/km-format self-name)
                              " (the color of Self))"))
          saved (on ruled (str "(save-kb \"" (slash path) "\")"))
          written (slurp path :encoding "UTF-8")
          loaded (answer (str "(load-kb \"" (slash path) "\")"))
          again (on loaded "(a Situation)")
          again-name (term/car (:value again))
          reloaded (on again (str "(in-situation " (print/km-format again-name)
                                  " (the color of " (print/km-format again-name) "))"))
          refused (answer "(in-every-situation Cat (TheSituation has (color (red))))")
          bare (answer "(every Situation has (assertions (1)))")
          created (on bare "(a Situation)")]
      (is (empty? (:errors ruled)))
      (is (= (term-of "(red)") (:value seen)))
      (is (= (term-of "(blue)") (:value self-color)))
      (is (empty? (:errors self-color)))
      (is (= (term-of "(t)") (:value saved)))
      (is (str/includes? written "(in-every-situation"))
      (is (str/includes? written "TheSituation"))
      (is (not (str/includes? written "SubSelf")))
      (is (empty? (:errors loaded)))
      (is (= (term-of "(red)") (:value reloaded)))
      (is (nil? (:value refused)))
      (is (some #(re-find #"not a subclass of Situation" %) (:errors refused)))
      (is (some? name))
      (is (some? self-name))
      (is (some? again-name))
      (is (some #(re-find #"Unquoted assertion" %) (:errors created))))))

(deftest nowexists-is-a-syntax-error-and-anonymous-instancep-stays-refused
  (let [syntax (answer "(nowexists Fred)")]
    (is (:ok syntax))
    (is (nil? (:value syntax)))
    (is (not (:error syntax)))
    (is (some #(re-find #"Syntax error" %) (:errors syntax))))
  (is (= "not-ported" (:error (answer "(anonymous-instancep Fred)")))))
