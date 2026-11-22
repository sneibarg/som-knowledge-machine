---
name: clj-kondo
description: >-
  Lints this repository with clj-kondo and reports each finding. Does not
  change the code. Use when the user runs /clj-kondo or asks to lint the
  project, run clj-kondo, or include lint in a Clojure code review or
  repository alignment.
---

# clj-kondo

Lint the Clojure with the `clj-kondo` command. Report each finding. Do not change the code, and do not add a dependency.

## Run

From the repository root, lint the paths that exist among `src/som`, `test`, `build.clj`, and `deps.edn`:

```
clj-kondo --lint src/som test build.clj deps.edn
```

Drop a path that is missing. When the caller names a directory, run the command there and lint that directory's Clojure source, its tests, and `deps.edn` when those paths exist. Skip `src/knowledge-machine/`, `src/resources/`, `target/`, and other build output.

Use the project's `.clj-kondo` config when it is present. Do not write a config.

A non-zero exit that prints findings is a result. Record each finding. When the command is not on `PATH`, record that `clj-kondo` is missing and stop. Do not install it.

## Report

When a caller is already writing a report, add the findings to that report and do not write a second file.

Otherwise file the report in `docs/reports`. Create the folder when it is missing. Name the file `clj-kondo_<YYYY-MM-DDTHHMMSS>.md`, using the local time it is filed, in 24-hour form. A later run writes a new file.

For each finding, name the file and line, the level, and the message. If there are no findings, say the lint is clean.
