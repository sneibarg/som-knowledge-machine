---
name: align-repository
description: >-
  Reports the proposed changes that would make springs-of-mud-agentic-player,
  springs-of-mud-server, som-server-modulith, or som-nlp-service meet the
  standards in that repository's AGENTS.md and the skills that file names.
  Files the alignment report and does not change code. Use when the user
  runs /align-repository or asks to align one of those repositories, bring
  it up to its standards, or report the changes that would match its
  conventions.
---

# Align repository

Write a report of the proposed changes that would make the named target satisfy its own `AGENTS.md`, and file it at the path under Report. That report is the whole task. The target's `AGENTS.md`, `AGENTS.override.md`, and the skills those files name are the standards. Read them. Do not copy those standards into this skill or into a second checklist.

Work from the repository that contains this skill. The report file is the only write. Do not edit, move, format, compile, test, or commit any other file in this repository or in the target.

## Target repositories

The valid target repositories are:

- `springs-of-mud-agentic-player`
- `springs-of-mud-server`
- `som-server-modulith`
- `som-nlp-service`

If the user did not name one of these, ask which target to report. A repository that is not in this list is not a target. Stop and say so.

Locate the checkout from the path the user gave or from a nearby project directory. Do not assume one absolute path. If the checkout is missing, ask for it.

The pointer to this skill in this repository's `AGENTS.md` names the skill. It is not a standard for a target, and this repository is not a target.

## Find the gaps

Read the target's `AGENTS.md` and `AGENTS.override.md` at its root. Include every section. Read each file cited in its Reference section and treat it as part of the standards. When a convention names a skill, read that skill.

Compare the source and tests that the target's standards describe. Skip build output, virtual environments, and dependency caches. Record each gap for the report.

When the user asks for lint, or the target contains Clojure, follow `.grok/skills/clj-kondo/SKILL.md` on that target. Add its findings to this report. Do not copy that skill's steps, and do not write a second report.

A proposal preserves behavior except where a standard requires a move or a file rename. When a standard requires a move, record what moves, the destination path, and each importer. If the move would leave an import cycle, record that the cycle blocks the move. When a standard names a formatter, record a formatting proposal for a file the move touches.

Propose a change to configuration, credentials files, or collection documents only when a standard requires that change. Omit passwords, JWTs, client secrets, and `Authorization` headers from the report.

## Report

File the report in this repository at `docs/alignment`. Create the folder when it is missing. Name the file with the target repository from Target repositories and the local time it is filed, in 24-hour form: `<repository>_<YYYY-MM-DDTHHMMSS>.md`. A later run writes a new file.

For each recorded gap, name the file, the standard it addresses, and the proposed change, including any move, importer, and cycle notes. Leave each lint finding in the form the clj-kondo skill specifies. If the comparison finds no gap, say there is nothing to propose. If a gap cannot be stated precisely, name the file and what is still unknown.
