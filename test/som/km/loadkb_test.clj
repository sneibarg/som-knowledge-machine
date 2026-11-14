(ns som.km.loadkb-test
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]
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
  [previous text]
  (engine/evaluate text {:kb (:kb previous) :query (:query previous)}))

(defn- name-of [result]
  (term/symbol-name (term/car (:value result))))

(defn- color-of
  [result & {:keys [situation]}]
  (:value (frame/get-vals (:kb result) (symbol "Fred") (symbol "color")
                          :situation situation)))

(defn- slash [path]
  (str/replace path "\\" "/"))

(defn- temp-path [suffix]
  (.getAbsolutePath (java.io.File/createTempFile "km-step13-" suffix)))

(defmacro with-temp
  [binding & body]
  `(let [~binding (temp-path ".km")]
     (try
       ~@body
       (finally
         (io/delete-file ~binding true)))))

(deftest undo-drops-the-logged-assertion
  (let [started (answer "(start-logging)")
        stored (on started "(Fred has (color (red)))")
        undone (on stored "(undo)")]
    (is (str/includes? (:text started) "(Started logging KM commands)"))
    (is (= (term-of "(t)") (:value undone)))
    (is (str/includes? (:text undone) "Undone"))
    (is (str/includes? (:text undone) "(Fred has (color (red)))"))
    (is (nil? (color-of undone)))))

(deftest one-undo-drops-only-the-later-assertion
  (let [started (answer "(start-logging)")
        red (on started "(Fred has (color (red)))")
        green (on red "(Fred has (color (green)))")
        undone (on green "(undo)")]
    (is (str/includes? (print/km-format (color-of green)) "red"))
    (is (< (str/index-of (print/km-format (color-of green)) "red")
           (str/index-of (print/km-format (color-of green)) "green")))
    (is (= (term-of "(red)") (color-of undone)))))

(deftest a-named-checkpoint-restores-the-earlier-value
  (let [started (answer "(start-logging)")
        blue (on started "(Fred has (color (blue)))")
        marked (on blue "(checkpoint here)")
        red (on marked "(Fred has (color (red)))")
        undone (on red "(undo here)")]
    (is (= (term-of "(t)") (:value marked)))
    (is (str/includes? (print/km-format (color-of red)) "blue"))
    (is (str/includes? (print/km-format (color-of red)) "red"))
    (is (= (term-of "(blue)") (color-of undone)))
    (is (str/includes? (:text undone) "Undone here"))))

(deftest keeping-kb-returns-the-value-and-restores-the-frames
  (let [kept (answer "(keeping-kb (Fred has (color (red))))")]
    (is (= (term-of "(Fred)") (:value kept)))
    (is (nil? (:error kept)))
    (is (nil? (color-of kept)))))

(deftest undo-creations-reuses-the-situation-name
  (let [started (answer "(start-creations-logging)")
        marked (on started "(set-creations-checkpoint)")
        made (on marked "(a Situation)")
        undone (on made "(undo-creations)")
        again (on undone "(a Situation)")]
    (is (= "_Situation1" (name-of made)))
    (is (= (term-of "(t)") (:value undone)))
    (is (not (frame/known-frame? (:kb undone) (symbol "_Situation1"))))
    (is (= "_Situation1" (name-of again)))))

(deftest undo-creations-is-refused-while-command-logging-is-on
  (let [started (answer "(start-logging)")
        creations (on started "(start-creations-logging)")
        undone (on creations "(undo-creations)")]
    (is (nil? (:value undone)))
    (is (str/includes? (:text undone) "Do (stop-logging) first"))))

(deftest two-saves-of-one-knowledge-base-match
  (let [stored (answer "(Fred has (color (red)))")
        once (on stored "(write-kb)")
        twice (on stored "(write-kb)")]
    (is (= (:text once) (:text twice)))
    (is (str/includes? (:text once) "(Fred has"))
    (is (str/includes? (:text once) ";;; Current state of the KB (KM 2.5.45)"))
    (is (not (str/includes? (:text once) "(now)")))))

(deftest a-saved-file-reloads-slot-order-situation-and-counter
  (with-temp path
    (let [red (answer "(Fred has (color (red)))")
          green (on red "(Fred has (color (green)))")
          sit (on green "(new-situation)")
          blue (on sit "(Fred has (color (blue)))")
          saved (on blue (str "(save-kb \"" (slash path) "\")"))
          loaded (on saved (str "(reload-kb \"" (slash path) "\")"))
          kb (:kb loaded)
          global-before (:value (frame/get-vals (:kb blue) (symbol "Fred")
                                                (symbol "color")
                                                :situation (symbol "*Global")))]
      (is (str/includes? (:text saved) "saved!"))
      (is (str/includes? (:text loaded) "loaded!"))
      (is (empty? (:errors loaded)))
      (is (= global-before
             (:value (frame/get-vals kb (symbol "Fred") (symbol "color")
                                     :situation (symbol "*Global")))))
      (is (= (term-of "(blue)")
             (:value (frame/get-vals kb (symbol "Fred") (symbol "color")
                                     :situation (symbol "_Situation1")))))
      (is (frame/situations-mode? kb))
      (is (utils/eql? (symbol "_Situation1") (frame/current-situation kb)))
      (is (= (:counter (:kb blue)) (:counter kb))))))

(deftest with-morphism-renames-a-symbol-during-the-load
  (with-temp path
    (spit path "(Node has (color (red)))\n" :encoding "UTF-8")
    (let [loaded (answer (str "(load-kb \"" (slash path)
                              "\" :with-morphism ((Node -> Device)))"))
          device (:value (frame/get-vals (:kb loaded) (symbol "Device")
                                         (symbol "color")))
          node (frame/known-frame? (:kb loaded) (symbol "Node"))]
      (is (= (term-of "(t)") (:value loaded)))
      (is (= (term-of "(red)") device))
      (is (not node)))))

(deftest load-patterns-keeps-only-the-matching-expression
  (with-temp path
    (spit path "(Fred has (color (red)))\n(Sue has (color (blue)))\n"
          :encoding "UTF-8")
    (let [loaded (answer (str "(load-kb \"" (slash path)
                              "\" :load-patterns ((?x has (color (red)))))"))]
      (is (= (term-of "(red)") (color-of loaded)))
      (is (not (frame/known-frame? (:kb loaded) (symbol "Sue")))))))

(deftest a-missing-file-is-an-error-and-answers-nil
  (let [missing (answer "(load-kb \"no-such-km-file.km\")")]
    (is (:ok missing))
    (is (nil? (:error missing)))
    (is (nil? (:value missing)))
    (is (some #(re-find #"No such file" %) (:errors missing)))))

(deftest fastsave-stays-refused
  (let [saved (answer "(fastsave-kb \"x.fkm\")")
        loaded (answer "(fastload-kb \"x.fkm\")")]
    (is (= "not-ported" (:error saved)))
    (is (re-find #"fastsave stays unported" (:message saved)))
    (is (= "not-ported" (:error loaded)))
    (is (re-find #"fastsave stays unported" (:message loaded)))))

(deftest a-utf8-string-round-trips-and-a-latin1-byte-is-read
  (with-temp path
    (let [stored (answer "(Fred has (nickname (\"café\")))")
          saved (on stored (str "(save-kb \"" (slash path) "\")"))
          loaded (on saved (str "(reload-kb \"" (slash path) "\")"))
          nickname (:value (frame/get-vals (:kb loaded) (symbol "Fred")
                                           (symbol "nickname")))]
      (is (= "café" (term/car nickname)))))
  (with-temp path
    (let [prefix (.getBytes "(Fred has (nickname (\"caf" "US-ASCII")
          suffix (.getBytes "\")))\n" "US-ASCII")
          bytes (byte-array (concat (seq prefix) [(unchecked-byte 0xE9)] (seq suffix)))]
      (with-open [out (java.io.FileOutputStream. path)]
        (.write out bytes))
      (let [loaded (answer (str "(load-kb \"" (slash path) "\")"))
            nickname (:value (frame/get-vals (:kb loaded) (symbol "Fred")
                                             (symbol "nickname")))]
        (is (empty? (:errors loaded)))
        (is (= "café" (term/car nickname)))))))

(deftest an-explanation-survives-a-reload
  (with-temp path
    (let [ruled (answer "(every Cat has (color (black)))")
          kitten (on ruled "(_Cat1 has (instance-of (Cat)))")
          seen (on kitten "(the color of _Cat1)")
          saved (on seen (str "(save-kb \"" (slash path)
                              "\" :include-explanationsp t)"))
          written (slurp path :encoding "UTF-8")
          loaded (on saved (str "(reload-kb \"" (slash path) "\")"))
          records (frame/explanations (:kb loaded) (symbol "_Cat1"))
          again (on loaded "(the color of _Cat1)")
          why (on again "(why)")]
      (is (str/includes? written "(explanation (:triple"))
      (is (str/includes? written "every Cat has"))
      (is (str/includes? written "(color (black))"))
      (is (some? records))
      (is (= (term-of "(black)") (:value again)))
      (is (str/includes? (:text why) "(every Cat has (color (black)))")))))

(deftest a-situation-local-explanation-reloads-into-that-situation
  (with-temp path
    (let [sit (answer "(new-situation)")
          place (term/car (:value sit))
          marked (on sit "(explanation (:triple Fred color red) ((added-at Cat \"local\")))")
          saved (on marked (str "(save-kb \"" (slash path) "\")"))
          written (slurp path :encoding "UTF-8")
          loaded (on saved (str "(reload-kb \"" (slash path) "\")"))
          local (frame/explanations (:kb loaded) (symbol "Fred") :situation place)
          global (frame/explanations (:kb loaded) (symbol "Fred"))]
      (is (str/includes? written "(in-situation "))
      (is (str/includes? written "added-at"))
      (is (some? local))
      (is (nil? global)))))

(deftest store-kb-and-restore-kb-return-to-the-saved-value
  (let [stored (answer "(store-kb)")
        changed (on stored "(Fred has (color (red)))")
        back (on changed "(restore-kb)")
        missing (answer "(restore-kb)")]
    (is (= (term-of "(t)") (:value stored)))
    (is (= (term-of "(red)") (color-of changed)))
    (is (= (term-of "(t)") (:value back)))
    (is (nil? (color-of back)))
    (is (nil? (:value missing)))
    (is (str/includes? (:text missing) "No stored KB state to restore!"))))

(deftest a-file-setq-of-an-unknown-name-is-refused-and-a-known-one-restores
  (with-temp path
    (spit path "(SETQ *NOT-A-PARAMETER* '1)\n(SETQ *KM-GENSYM-COUNTER* '41)\n"
          :encoding "UTF-8")
    (let [loaded (answer (str "(load-kb \"" (slash path) "\")"))
          prompt (answer "(SETQ *KM-GENSYM-COUNTER* '9)")]
      (is (some #(re-find #"NOT-A-PARAMETER" %) (:errors loaded)))
      (is (some #(re-find #"refused" %) (:errors loaded)))
      (is (= 41 (:counter (:kb loaded))))
      (is (= "not-ported" (:error prompt)))
      (is (re-find #"setq is not evaluated" (:message prompt))))))
