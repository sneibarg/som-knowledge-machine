---
name: clojure-code-review
description: >-
  Checks this repository's Clojure against the Coding Conventions in AGENTS.md
  and writes each unmet convention to a code review report in docs/reports.
  Does not change the code. Use when the user runs /clojure-code-review or
  asks for a Clojure code review, a conventions check, or a report of where
  the code breaks those conventions.
---

# Clojure code review

Read the Coding Conventions in `AGENTS.md`. When `AGENTS.override.md` exists, read the coding conventions it adds or replaces. Those conventions are the standard. Do not copy them into this skill or into a second checklist.

Review this repository's Clojure. Write the report and stop. The report file is the only write. Do not change the code.

## What to read

Review every `.clj` file in this repository. Also read `deps.edn`, which the conventions constrain. Skip `src/knowledge-machine/`, `src/resources/`, and `target/`. If the user names files, a namespace, or a diff, review that Clojure instead.

The Skills section of `AGENTS.md` names skills. It is not a coding convention. When a coding convention names a skill, read that skill and apply it.

Follow `.grok/skills/clj-kondo/SKILL.md` and add its findings to this report. Do not copy that skill's steps, and do not write a second report.

## Findings

Record a convention finding only when the code breaks a convention you read and you can point at the line. Cite the convention by where it sits in `AGENTS.md`. Leave out taste and a rewrite the convention does not require. Keep the lint findings from the clj-kondo skill.

## Report

File the report in `docs/reports`. Create the folder when it is missing. Name the file `clojure-code-review_<YYYY-MM-DDTHHMMSS>.md`, using the local time it is filed, in 24-hour form. A later run writes a new file.

For each convention finding, name the file and line, the convention it breaks, and the change that would meet it. Leave each lint finding in the form the clj-kondo skill specifies. If the review finds no unmet convention and the lint is clean, say so.
