# Packaged component libraries

The JAR contains an index of the staged resources. `load-lib` uses that index
to walk component libraries through the JVM context classloader. Existing
filesystem directories load directly. A missing `src/resources/...` directory
falls back to the packaged resource path. Explicit `classpath:resources/...`
paths select packaged resources. The default library paths select packaged
resources when the source tree is absent.

This extends the component loader derived from the component library's
`Readme.txt`. The recursive walk order, case-sensitive extension selection,
unevaluated Lisp entries, load options, and returned session state are retained.
The file loader accepts resource URLs and preserves its UTF-8 and ISO-8859-1
decoding. No new Lisp forms are introduced.

Build with `clojure -T:build jar`. A JVM consumer can evaluate
`(load-lib "src/resources/som-component-library" :silent t)` in a fresh session
and pass the returned `:kb` and `:query` to later evaluations. The shipped
configuration uses the same paths in a checkout and an imported JAR.

The regression test builds a temporary library JAR without directory entries
and checks traversal order, nested files, Latin-1 text, skipped Lisp code, and
session isolation. Run it with
`clojure -M:test -n som.km.resource-library-test`.

A Java 17 smoke test nested the rebuilt library and its runtime dependencies in
a Spring Boot executable JAR and ran it outside the checkout. It read the shipped
configuration, listed all eight configured directories, loaded the Springs of
MUD library, and checked that another session had no loaded facts.

The full suite ran 379 tests with 3,156 assertions. It retained the existing
failure in `som.kb-test/load-lib-loads-the-shipped-component-library` at line 294,
which expects silent-load text to contain only aborted-load lines. The shipped
library also produces taxonomy output. This assertion failed in the preceding
run before the classpath loader change. The new resource test passed, and the
suite reported no errors.
