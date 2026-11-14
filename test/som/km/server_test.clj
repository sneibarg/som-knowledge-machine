(ns som.km.server-test
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [som.km.engine :as engine]
            [som.km.server :as server]))

(defn- body [text]
  (io/input-stream (.getBytes (str text) "UTF-8")))

(defn- parse [response]
  (json/read-str (:body response) :key-fn keyword))

(defn- without-statistics
  "Drop the clock-bearing statistics line before a whole-body comparison."
  [body]
  (dissoc body :statistics))

(deftest port-text
  (is (= 8080 (server/parse-port nil)))
  (is (= 0 (server/parse-port "0")))
  (is (= 65535 (server/parse-port "65535")))
  (is (thrown? clojure.lang.ExceptionInfo (server/parse-port "nope")))
  (is (thrown? clojure.lang.ExceptionInfo (server/parse-port "70000"))))

(deftest status-route-matches-the-engine
  (let [response (server/handler {:request-method :get :uri "/status" :headers {}})]
    (is (= 200 (:status response)))
    (is (str/starts-with? (get-in response [:headers "Content-Type"]) "application/json"))
    (is (= (:km-version (engine/status)) (:km-version (parse response))))
    (is (= (set (:interfaces (engine/status))) (set (:interfaces (parse response)))))))

(deftest query-route-matches-the-engine
  (let [response (server/handler {:request-method :post
                                  :uri "/query"
                                  :headers {"content-type" "text/plain; charset=utf-8"}
                                  :body (body "  (1 + 2)  ")})]
    (is (= 200 (:status response)))
    (is (= [3] (:value (parse response))))
    (is (str/includes? (:statistics (parse response)) "inferences"))
    (is (= (without-statistics (server/client-body (engine/evaluate "  (1 + 2)  ")))
           (without-statistics (parse response))))))

(deftest a-position-read-answers-that-value
  (let [response (server/handler {:request-method :post
                                  :uri "/query"
                                  :headers {"content-type" "text/plain"}
                                  :body (body "  (theNth 2 of (:set x y))  ")})]
    (is (= 200 (:status response)))
    (is (= [{:symbol "y"}] (:value (parse response))))
    (is (str/includes? (:statistics (parse response)) "inferences"))
    (is (= (without-statistics (server/client-body (engine/evaluate "  (theNth 2 of (:set x y))  ")))
           (without-statistics (parse response))))))

(deftest thing-subsumes-an-unplaced-class
  (let [response (server/handler {:request-method :post
                                  :uri "/query"
                                  :headers {"content-type" "text/plain"}
                                  :body (body "(Thing subsumes Cat)")})]
    (is (= 200 (:status response)))
    (is (= [{:symbol "t"}] (:value (parse response))))
    (is (str/includes? (:statistics (parse response)) "inferences"))
    (is (= (without-statistics (server/client-body (engine/evaluate "(Thing subsumes Cat)")))
           (without-statistics (parse response))))))

(deftest a-sometimes-body-answers-that-value
  (let [response (server/handler {:request-method :post
                                  :uri "/query"
                                  :headers {"content-type" "text/plain"}
                                  :body (body "  (sometimes (1 + 2))  ")})]
    (is (= 200 (:status response)))
    (is (= [3] (:value (parse response))))
    (is (str/includes? (:statistics (parse response)) "inferences"))
    (is (= (without-statistics (server/client-body (engine/evaluate "  (sometimes (1 + 2))  ")))
           (without-statistics (parse response))))))

(deftest a-conditional-answers-the-then-branch
  (let [response (server/handler {:request-method :post
                                  :uri "/query"
                                  :headers {"content-type" "text/plain"}
                                  :body (body "  (if t then 1 else 2)  ")})]
    (is (= 200 (:status response)))
    (is (= [1] (:value (parse response))))
    (is (str/includes? (:statistics (parse response)) "inferences"))
    (is (= (without-statistics (server/client-body (engine/evaluate "  (if t then 1 else 2)  ")))
           (without-statistics (parse response))))))

(deftest a-ratio-and-a-large-power-survive-json
  (let [ratio (server/handler {:request-method :post
                               :uri "/query"
                               :headers {"content-type" "text/plain"}
                               :body (body "(1 / 2)")})
        power (server/handler {:request-method :post
                               :uri "/query"
                               :headers {"content-type" "text/plain"}
                               :body (body "(2 ^ 100)")})]
    (is (= [{:ratio "1/2"}] (:value (parse ratio))))
    (is (= ["1267650600228229401496703205376"] (:value (parse power))))
    (is (= (without-statistics (server/client-body (engine/evaluate "(1 / 2)")))
           (without-statistics (parse ratio))))
    (is (= (without-statistics (server/client-body (engine/evaluate "(2 ^ 100)")))
           (without-statistics (parse power))))))

(deftest a-broken-expression-is-a-bad-request
  (let [response (server/handler {:request-method :post
                                  :uri "/query"
                                  :headers {"content-type" "text/plain"}
                                  :body (body "(a")})]
    (is (= 400 (:status response)))
    (is (= (engine/evaluate "(a") (parse response)))))

(deftest blank-query-is-a-bad-request
  (let [response (server/handler {:request-method :post
                                  :uri "/query"
                                  :headers {"content-type" "text/plain"}
                                  :body (body "  ")})]
    (is (= 400 (:status response)))
    (is (= "empty" (:error (parse response))))))

(deftest q-does-not-stop-the-service
  (let [response (server/handler {:request-method :post
                                  :uri "/query"
                                  :headers {"content-type" "text/plain"}
                                  :body (body "q")})]
    (is (= 200 (:status response)))
    (is (= [{:symbol "q"}] (:value (parse response))))
    (is (= (without-statistics (server/client-body (engine/evaluate "q")))
           (without-statistics (parse response))))))

(deftest json-is-not-a-query-body
  (let [response (server/handler {:request-method :post
                                  :uri "/query"
                                  :headers {"content-type" "application/json"}
                                  :body (body "{\"expr\":\"(a Cat)\"}")})]
    (is (= 415 (:status response)))
    (is (= "unsupported-media" (:error (parse response))))))

(deftest unknown-route
  (let [response (server/handler {:request-method :get :uri "/missing" :headers {}})]
    (is (= 404 (:status response)))
    (is (= "not-found" (:error (parse response))))))

(deftest index-names-the-two-routes
  (let [index (parse (server/handler {:request-method :get :uri "/" :headers {}}))]
    (is (= "GET /status" (get-in index [:routes :status])))
    (is (= "POST /query" (get-in index [:routes :query])))))

(defn- post
  "POST one expression and return the status and the parsed body."
  [base text]
  (let [connection (.openConnection (java.net.URL. (str base "/query")))]
    (.setRequestMethod connection "POST")
    (.setDoOutput connection true)
    (.setRequestProperty connection "Content-Type" "text/plain; charset=utf-8")
    (with-open [out (.getOutputStream connection)]
      (.write out (.getBytes text "UTF-8")))
    (let [status (.getResponseCode connection)
          stream (if (<= 200 status 299)
                   (.getInputStream connection)
                   (.getErrorStream connection))]
      {:status status
       :body (json/read-str (slurp stream) :key-fn keyword)})))

(deftest service-answers-over-http
  (let [http (server/start {:port 0})
        port (-> http .getAddress .getPort)
        base (str "http://127.0.0.1:" port)]
    (try
      (is (= "2.5.45"
             (:km-version (json/read-str (slurp (str base "/status")) :key-fn keyword))))
      (let [stored (post base "(Fred has (color (red)))")
            seen (post base "(the color of Fred)")
            apart (engine/evaluate "(the color of Fred)")]
        (is (= 200 (:status stored)))
        (is (= [{:symbol "Fred"}] (:value (:body stored))))
        (is (= 200 (:status seen)))
        (is (= [{:symbol "red"}] (:value (:body seen))))
        (is (nil? (:value apart)))
        (is (not (contains? (:body seen) :kb)))
        (is (not (contains? (:body seen) :query)))
        (let [written (post base "(write-kb)")
              fast (post base "(fastsave-kb \"x.fkm\")")]
          (is (= 200 (:status written)))
          (is (str/includes? (str (:text (:body written))) "(Fred has"))
          (is (= 501 (:status fast)))
          (is (= "not-ported" (:error (:body fast)))))
        (let [phrase (post base "(make-phrase (:seq \"a\" \"cat\"))")
              tree (post base "(taxonomy)")]
          (is (= 200 (:status phrase)))
          (is (= ["a cat"] (:value (:body phrase))))
          (is (= 200 (:status tree)))
          (is (str/includes? (str (:text (:body tree))) "Thing")))
        (let [same (post base "(1 & 1)")
              classified (post base "(_Cat1 has (instance-of (Cat)))")
              colored (post base "(_Cat1 has (color (red)))")
              found (post base "(the Cat with (color (red)))")
              created (post base "(a Cat)")]
          (is (= 200 (:status same)))
          (is (= [1] (:value (:body same))))
          (is (= 200 (:status classified)))
          (is (= 200 (:status colored)))
          (is (= 200 (:status found)))
          (is (= [{:symbol "_Cat1"}] (:value (:body found))))
          (is (= 200 (:status created)))
          (is (str/starts-with? (-> created :body :value first :symbol) "_Cat"))
          (let [ruled (post base "(every Cat has (color (black)))")
                kitten (post base "(_Cat2 has (instance-of (Cat)))")
                inherited (post base "(the color of _Cat2)")]
            (is (= 200 (:status ruled)))
            (is (= [{:symbol "Cat"}] (:value (:body ruled))))
            (is (= 200 (:status kitten)))
            (is (= 200 (:status inherited)))
            (is (= [{:symbol "black"}] (:value (:body inherited))))
            (let [because (post base "(why)")
                  opened (post base "(a-prototype Dog)")
                  pname (-> opened :body :value first :symbol)
                  furred (post base (str "(" pname " has (fur (brown)))"))
                  closed (post base "(end-prototype)")
                  dog (post base "(_Dog1 has (instance-of (Dog)))")
                  fur (post base "(the fur of _Dog1)")
                  sit (post base "(new-situation)")
                  back (post base "(global-situation)")]
              (is (= 200 (:status because)))
              (is (= [{:symbol "t"}] (:value (:body because))))
              (is (str/includes? (str (:text (:body because)))
                                 "(every Cat has (color (black)))"))
              (is (= 200 (:status opened)))
              (is (str/starts-with? pname "_Proto"))
              (is (= 200 (:status furred)))
              (is (= [{:symbol pname}] (:value (:body furred))))
              (is (= 200 (:status closed)))
              (is (= [{:symbol "t"}] (:value (:body closed))))
              (is (= 200 (:status dog)))
              (is (= 200 (:status fur)))
              (is (= [{:symbol "brown"}] (:value (:body fur))))
              (is (= 200 (:status sit)))
              (is (str/starts-with? (-> sit :body :value first :symbol) "_Situation"))
              (is (= 200 (:status back)))
              (is (= [{:symbol "*Global"}] (:value (:body back))))
              (let [defined (post base "(every House-Owner has-definition (instance-of (Person)))")]
                (is (= 200 (:status defined)))
                (is (= [{:symbol "House-Owner"}] (:value (:body defined)))))))))
      (let [lic (post base "(license)")]
        (is (= 200 (:status lic)))
        (is (nil? (:value (:body lic))))
        (is (str/includes? (str (:text (:body lic))) "Simplified BSD"))
        (is (str/includes? (str (:text (:body lic))) "peterc@allenai.org")))
      (finally
        (server/stop http)))))

(deftest a-comment-is-answered-over-http
  (let [text "(comment [Pet] \"a pet\" \"owned\")"
        response (server/handler {:request-method :post
                                  :uri "/query"
                                  :headers {"content-type" "text/plain; charset=utf-8"}
                                  :body (body text)})
        parsed (parse response)]
    (is (= 200 (:status response)))
    (is (= ["a pet" "owned"] (:value parsed)))
    (is (str/includes? (:statistics parsed) "inferences"))
    (is (= (without-statistics (server/client-body (engine/evaluate text)))
           (without-statistics parsed)))))
