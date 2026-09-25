# Rationale

A rationale record explains one design choice that a knowledgeable reader could
reasonably have made differently. It answers "why is it this way, and not the
obvious other way?" and nothing else. The definitions a choice leads to live in
the [specification](../spec/README.md) and the design chapters.

## When to write a record

Write one only if all four hold.

1. The choice is visible in the specification or the design, and it is in force.
2. A real alternative existed and was rejected for a reason that can be stated:
   a counterexample, a lost property, a cost. A choice with no credible
   alternative is a definition, and belongs where it is defined.
3. The reason does not fit where the choice is stated. If one paragraph beside
   the definition is enough, write that paragraph there and no record here.
4. A reader who disagrees can tell from the record what evidence would reopen
   the choice.

## What a record contains

| Part | Content |
|---|---|
| Title | The choice, as a statement. "Connections keep the order of shared events", not "Connection ordering" |
| Opening | What was chosen, in one paragraph, with a link to the page that defines or designs it |
| Alternatives | Each rejected alternative with the specific reason it fails |
| Reason | Why the chosen one holds up, where the alternatives do not say it already |
| Reopen when | A concrete condition that an observer can check |
| References | Primary literature, only where the reason rests on it |

A record covers one choice, or a few that cannot be understood apart. It is at
most 80 lines. A record that needs more is compensating for a design chapter
that does not explain itself; fix the chapter.

## What a record never contains

- **How the choice was reached.** Who compared what, in which order, on which
  date, against which snapshot; review findings and their dispositions;
  experiment logistics, validation results, counts of checked declarations.
- **Definitions or requirements.** A rule is never stated only here. The record
  links to the page that owns it.
- **Plans and progress.** What is implemented, what remains and what comes next
  belong to the [status page](../status.md) and the [roadmap](../roadmap.md).
- **Names of work units.** Labels of studies, stages, goals or review items mean
  nothing to a reader of the design. Say what the thing is.
- **History.** A record describes the choice in force. When the choice changes,
  the record is rewritten or deleted in the same change. Superseded reasoning is
  not kept beside it; version control keeps it.

## Where a record is found

A record is reached from the page whose design it explains, at the point where
the question arises; the file name is the choice, and the folder listing is the
whole set. This page keeps no list of records, so adding one changes the page
that raises the question and nothing else.

The [documentation check](../../tests/check_docs.py) enforces what can be checked:
the length limit, a link to an owning page outside this folder, a link back from a page
outside this folder, a stated reopening condition, and the absence of dates,
temporary paths, commit identifiers and work-unit labels.
