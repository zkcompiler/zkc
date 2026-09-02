# F0-V2B2D2 Fresh completed-record schema

This package answers the schema form of the `fresh-runtime-oracle-receipts`
B2D pressure family at bounded research resolution. It derives an exact candidate
`ExecutionView.completed_record_schema` from each admitted D1 Core and Fresh
Protocol. It never derives the schema from a run.

Run from the repository root:

```sh
python3 -B evaluation/formal-source-fresh-run-schema-f0v2b2d2/run.py --check
```

The frozen result is
`Affirmative/F0V2B2D2-A-FRESH-RUN-SCHEMA`: 53 findings over five exact
candidate bodies.

## Exact question

Can the `ExecutionView`'s `completed_record_schema` be stated in the selected
finite description universe so that, for each of the five D1 carriers, a typed
owner path and an independent cold byte-derived path agree on one exact schema
body that fixes:

- every occurrence's receipt arity and value types;
- all three Fresh Challenge receipts;
- every Published, Queried, and Answered Oracle receipt branch, including mode,
  visibility, value types, and the LogicalAccess zero-output fixation marker;
- terminal references, receipt prefixes, verdicts, and public-output types;
- the sum `CompletedRun | InterpretationFailed | StrategyStopped`, with
  `InterpretationFailed` exactly `None` for Fresh and `StrategyStopped`
  carrying a terminal-delimited partial record; and
- the qualified operational noncompletion partition by name, outside the
  completed-record sum?

The schema answer is affirmative for the five exact D1 carriers and the candidate
choices frozen here. It is not an owner-page publication result. Five places
where the current target text does not select one exact body remain
`CannotAnswer` findings below. Runtime generation and replay remain open.

## Candidate schema

The package extends the B2B finite description universe by source delta and
compiles that source independently with the recursive and iterative B2B
compilers. The candidate body contains:

| Surface | Exact finite content per carrier |
|---|---:|
| Occurrence receipt schemas | 23 |
| Fresh Challenge receipt schemas | 3 |
| Oracle receipt schemas | 9: Published, Queried, Answered for each mode |
| Completed terminal alternatives | 3 |
| Strategy-stopped partial alternatives | 4 |
| Named operational noncompletion classes outside the sum | 8 |

The three Oracle modes retain different publication laws:

- `FullCanonical` publishes canonical outputs with their exact value types;
- `PublicBinding` publishes the public binding with its exact value type; and
- `LogicalAccess` publishes no output and instead carries the typed fixation
  marker selected by this candidate.

The schema source gives each qualified noncompletion case its Foundation name:
`Unsupported`,
`MissingDependency`, `CannotAnswer`, `KindMismatch`, `Malformed`, `Refused`,
`DeterministicLimitExceeded`, and `CheckerFailure`. These are operational
outcomes, not variants of the record sum.

## Independent evidence paths

The typed path admits each exact D1 Core and Fresh Protocol, retains the
process-local authority, and derives the candidate schema from those static
sources. The cold path does not import the typed D2 model. It separately
compiles the schema source, authenticates and parses Core and Fresh Protocol
bytes, re-authenticates module and algorithm closure, and derives the same
schema body.

The paths agree on five distinct values and canonical bodies totaling 168,652
bytes. All bodies round-trip and typed reprojection is deterministic. The
package invokes no runtime strategy, samples no Challenge, produces no
receipt values, executes no run, and executes no replay.

## Negative discriminators

Ten individually schema-valid substitutions are admitted by the structural
grammar but refused by exact owner comparison with stable codes:

| Mutation | Refusal code |
|---|---|
| Change a receipt branch | `F0V2B2D2-R-RECEIPT-BRANCH` |
| Change a receipt coordinate | `F0V2B2D2-R-RECEIPT-COORDINATE` |
| Change receipt visibility | `F0V2B2D2-R-RECEIPT-VISIBILITY` |
| Change receipt arity | `F0V2B2D2-R-RECEIPT-ARITY` |
| Change a receipt value type | `F0V2B2D2-R-RECEIPT-TYPE` |
| Change a terminal reference | `F0V2B2D2-R-TERMINAL-REFERENCE` |
| Change the stopping terminal | `F0V2B2D2-R-STOPPING-TERMINAL` |
| Add a receipt after an inactive occurrence | `F0V2B2D2-R-INACTIVE-OCCURRENCE-RECEIPT` |
| Omit the LogicalAccess fixation marker | `F0V2B2D2-R-FIXATION-MARKER` |
| Upgrade PublicBinding to FullCanonical | `F0V2B2D2-R-PUBLICATION-MODE` |

Cold controls also reject a cross-Core Fresh Protocol and incomplete algorithm
closure, and classify truncated Core bytes as malformed.

## Target obligations retained as CannotAnswer

The candidate makes enough choices to test finite representability, but the
current owner text does not determine those choices uniquely:

- `docs-next/pir/interactive-core.md:1091-1092` requires a LogicalAccess
  fixation marker, while lines 1758-1765 do not place that marker in the
  Published receipt.
- Lines 1704 and 1767-1775 do not state the exact occurrence-receipt prefix at
  the first active terminal.
- Line 1777 does not define the exact body of `PartialRunRecord`.
- Lines 1791-1794 exclude `StrategyStopped` from
  `CompletedProtocolRecord`, and lines 1814-1817 classify a partial record as
  diagnostic rather than completed.
- Line 2128 names `run_record_schema`, not `completed_record_schema`.

The package records these as
`F0V2B2D2-C-FIXATION-RECEIPT-PLACEMENT`,
`F0V2B2D2-C-TERMINAL-RECEIPT-PREFIX`,
`F0V2B2D2-C-PARTIAL-RUN-BODY`, `F0V2B2D2-C-OUTCOME-OWNER`, and
`F0V2B2D2-C-EXECUTION-FIELD-NAME`. It does not edit the target owner page.

## Result boundary

A pass establishes finite source compilation, exact static derivation,
typed/cold differential agreement, canonical-byte agreement, and mutation
discrimination for five exact candidate Core/Fresh pairs. It supports only:

```text
candidate profile
  -> exact admitted Core and Fresh Protocol
  -> exact candidate completed-record schema
```

It does not establish a run, replay equality, generated receipt conformance,
runtime or live-implementation correspondence, general-Core derivation,
canonical transport or identity selection, target publication, mechanized
refinement, relation truth, protocol soundness, Fiat--Shamir security,
random-oracle security, concrete hash/sponge security, or QROM applicability.
