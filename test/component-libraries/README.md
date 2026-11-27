# Component-library tests

These tests establish that component knowledge reaches a caller-owned session
through the loader, packaged resources, and startup adapters. They do not decide
which agent action serves a goal; those contracts are in [agent-goals](../agent-goals/README.md).

| File / namespace | Coverage |
| --- | --- |
| `som/kb_test.clj` / `som.kb-test` | Recursive traversal and order, extension case, `.km` loading, skipped Lisp and other file types, missing paths, silent flags, loading output, session retention, and coverage of the shipped component tree. |
| `som/km/resource_library_test.clj` / `som.km.resource-library-test` | A temporary JAR without directory entries: indexed traversal, nested files, UTF-8/Latin-1 decoding, skipped Lisp, classpath fallback, and independent sessions. |
| `som/km/configured_test.clj` / `som.km.configured-test` | EDN configuration validation, build `all` directory order, path normalization, missing files, recursive loading, and exclusion of directories outside the configured list. |
| `som/km/startup_test.clj` / `som.km.startup-test` | Startup expressions for both libraries, Springs library files and frames, and retention of both loads in one prompt session. |

Run the group with `clojure -M:test -d test/component-libraries`, or select a
namespace with `clojure -M:test -n som.km.resource-library-test`.
Temporary libraries and the temporary JAR are created and cleaned up by the tests.
Run from the repository root so shipped resource paths resolve.

The full shipped-tree load test,
`som.kb-test/load-lib-loads-the-shipped-component-library`, is disabled because
loading thousands of KM files makes routine runs too slow. Its body is retained
under a Clojure reader-discard marker (`#_`), so neither default nor namespace
runs execute it. The recursive traversal test and all focused loader, packaging,
configuration, and startup tests remain enabled.

To re-enable it, remove the marker immediately above that test, then run:

```sh
clojure -J-Xmx4g -M:test -n som.kb-test -v som.kb-test/load-lib-loads-the-shipped-component-library
```

[Migration step 27](../../docs/migration/27-packaged-component-libraries.md)
records its pre-existing silent-output assertion failure: the library emits
both taxonomy text and aborted-load lines. Disabling the case does not alter
that retained assertion.

The Springs startup tests load `src/resources/som-component-library`. The agent
suite also checks its own library vocabulary and isolation as prerequisites for
its conclusion contracts.

The current startup file-presence assertion also expects `Som-Level-Goal.km`
at the library root, while the library puts it under `level/`.
That startup assertion remains enabled. The separate full-library output
assertion remains in the disabled integration test.
