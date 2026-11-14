# Maven library packaging

`clojure -T:build jar` packages the existing runtime namespaces and the root
`LICENSE` as `target/som-knowledge-machine-0.1.0-SNAPSHOT.jar`.
`clojure -T:build install` builds and installs the JAR and POM as
`org.springy.som:som-knowledge-machine:0.1.0-SNAPSHOT`. Maven resolves Clojure
and data.json from the generated POM. This step adds no Lisp forms or modules.
Run `clojure -M:test` to exercise the source checkout. Use `jar tf` on the
artifact to inspect its contents.

## Clojure follow-up for the packaged license

Update [`src/som/km/license.clj`](../../src/som/km/license.clj) so
`fallback-text` first tries `(io/resource "META-INF/som-knowledge-machine/LICENSE")`
and reads the URL with `slurp` and `:encoding "UTF-8"`. Keep `source-license`,
the working-directory `LICENSE`, and the short notice as fallbacks in that order.
The interpreter can continue calling `som.km.license/text`.

The Java 17 smoke test loaded the installed JAR from outside the checkout.
It verified KM version `2.5.45`, arithmetic, session isolation, and saving and
loading a knowledge base through an absolute path. The embedded license matched
the root file byte for byte, and `(license)` returned only the short notice.

After the lookup change, run a JVM
with the JAR and its Maven dependencies from a directory without a `LICENSE`
file, evaluate `(license)`, and compare its output with the full root `LICENSE`,
including the trailing newline. Repeat that check in the Spring Boot nested-JAR
smoke test when integrating the artifact into `som-nlp-service`.

## Verification

The source checkout passed `clojure -M:test` with 288 tests and 2,068 assertions.
Both build tasks passed on the project JDK. The packaged Java 17 smoke test
used the locally installed JAR and its runtime dependencies. Spring Boot
nested-JAR verification and publication to Nexus remain part of the consumer
integration.
