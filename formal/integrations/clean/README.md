# Clean relation integration

This optional Lake package exports a selected fragment of
[Clean](https://github.com/Verified-zkEVM/clean) flat AIR components into the
independent zkc finite AIR (`Zkc.Relation.AIR`) and proves the correspondence
against Clean's own definitions. The main `formal/` package has no Clean
dependency. The package uses a local path dependency on main and exact pins.

```sh
just test-lean-clean          # from the repository root: fetch, build, audit, control
cd formal/integrations/clean
lake build
lake env lean --run TestsClean/Control.lean   # print the native comparison control
```

The first build clones the pinned sources into `.lake/packages`.
`just fetch-lean clean` links the main package's sources there and fetches
Mathlib's published objects; alternatively link those entries to an existing
checkout of the same revisions. Do not run `lake update`: it would re-resolve the
reviewed manifest. `just test-lean-clean` also requires
[the committed control](../../../tests/fixtures/clean/air-control.json) to be
byte-identical to the producer's output. `python3 reproduce.py --with-clean` in
`formal/` rebuilds this package without prior Lean objects and makes the same
comparison.

`lake build` builds the library and its controls. The generated
[TestsClean.Audit](TestsClean/Audit.lean) (`checks/audit_imports.py`) audits
every owned declaration with `Tools.DeclarationAudit`, whose dependency rule
keeps `ZkcClean` free of tests, tools, examples and the ArkLib package and keeps
the main library free of this package and Clean ([rule controls](TestsClean/AuditRules.lean)).
[TestsClean.UpstreamStatus](TestsClean/UpstreamStatus.lean) records the axioms of
the selected bridge and upstream declarations. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted in their transitive proof cones.

## Pins

| Dependency | Revision |
|---|---|
| Lean | `leanprover/lean4:v4.33.1` |
| Clean | `b449bf590f93e13827c3c7e747e392d6969aa380` |
| Mathlib | `0df444a360eaa60ab8c11dca51a86af692955474`, the main package's pin |
| CompPoly | `a09455a22fea4623a2a1c5b363cf6efc61486a83`, Clean's resolution |

The remaining entries of [the manifest](lake-manifest.json) are the main
package's revisions; Clean's own manifest selects the same ones. Clean's library
requires module-system importers, but a `module` file cannot import the main zkc
library, so both libraries here set `allowNonModules`.

## Admitted fragment

`exportComponent` reads `Air.Flat.Component.operations` of one component. It
refuses any lookup or channel interaction anywhere in the flattened operations,
including nested subcircuits; a component's body is itself a nested subcircuit.
It skips witness operations: witness generation does not restrict the accepted
witnesses. It exports every assertion in order, constants by Clean's canonical
`FiniteField.val` and variables as columns of the component's `width`. A
variable at or beyond that width is refused, because `Environment.fromArray`
would read zero there.

`Artifact.decode` is import admission into the zkc AIR. It checks the field
size, canonical constants and column range, decodes constants with
`FiniteField.fromNat` (`Nat.cast` on prime fields `F p`) and applies every
assertion to every row at offset zero. There are no public inputs.

Outside this fragment: lookups, channels and their balance, verifier tables,
ensembles of several tables, adjacent-row or cyclic windows (Clean's inductive
tables), challenge-dependent constraints, empty tables and public bindings.
Nested subcircuits and loops are accepted only because Clean's constraint
semantics flattens them and the restriction is checked on the flattened list.

## Claims and their premises

| Declaration | Claim | Premises and limit |
|---|---|---|
| [Flatten](ZkcClean/Flatten.lean): `flatten_eq_toFlat` | The kernel-evaluable flattening equals upstream `Operations.toFlat` | None; upstream `NestedOperations.toFlat` is well-founded and does not reduce in the kernel |
| [Export](ZkcClean/Export.lean): `exportComponent_ok`, `exportOperations_eq_ok`, `exportOperations_refused` | A successful export has no lookup or interaction at any depth, only in-range variables, and exactly the encoded upstream `Operations.constraints`; it succeeds exactly on that fragment | Export result; `width` is `Component.width` |
| [Expression](ZkcClean/Expression.lean): `export_expression`, `evaluateAt_decode` | The imported expression evaluates to Clean's `Expression.eval` on the row environment | Successful export of the expression; every read function, statement and `Environment.data` |
| [Relation](ZkcClean/Relation.lean): `holds_iff`, `table_holds_iff` | The zkc `AIR.family` relation holds iff `Operations.ConstraintsHold` holds on every row, respectively upstream `Air.Flat.Table.Constraints` | Successful export and import; nonempty trace of the artifact's width, or a table with `width` equal to it; one `Environment.data` for all rows |
| Same module: `constraintsHold_data`, `decode_export` | Constraints in the fragment do not read `Environment.data`; import of an exported artifact always succeeds | Successful export |
| [Specification](ZkcClean/Specification.lean): `guarantees_of_export`, `table_guarantees_of_export` | `FullGuarantees` and `FullRequirements` (table `Guarantees` and `Requirements`) hold | Successful export: no interaction exists |
| Same module: `row_spec`, `table_spec` | The zkc relation gives the component's `Spec` per row, and the table's `Spec` and `Requirements` | The component's actual `Assumptions`, which may constrain `Environment.data`; via upstream `Component.weakSoundness`, `Table.weakSoundness` |
| [Native](ZkcClean/Native.lean): `export_ring`, `component_ring` | Each imported assertion's shared ring tree (`AIR.Expr.toRing`) evaluates to the upstream constraint's `Expression.eval`, in export order | Successful export and import; composes `export_expression` with `Zkc.Relation.AIR.Expr.toRing_eval` |
| Same module: `native_ring`, `component_native_ring` | The Lean `Term.ring` interpretation of assertion `j`, with residue literals and input `i` bound to column `i`, evaluates to upstream constraint `j` on the row | A `PrimePresentation`: Clean's `fromNat` is `Nat.cast` on a prime field of the presented size |
| Same module: `no_presentation_of_not_prime` | A Clean field of non-prime size, such as a binary field, has no presentation | None |

The theorems relate Lean terms: a Clean component, its exported artifact and the
zkc relation decoded from that artifact. They do not prove a native importer,
evaluator, DAG decoder or compiled execution, channel balance, a STARK reduction,
Fiat-Shamir security or VM adequacy. The native comparison below is a checked
comparison on fixed rows, not a decoder theorem.

## Native presentation and comparison

An artifact carries Clean's canonical naturals (`FiniteField.val`). Native finite
AIR and `zkc.ring/0` literals denote residues in a prime field, which is Clean's
meaning only when `fromNat` is `Nat.cast`. `emitRelation` and `emitArena`
therefore require a `PrimePresentation` and refuse any presentation outside the
installed native fields (currently `koala-bear`), a different field size,
noncanonical constants, out-of-range columns and native size limits. Clean's
class also describes binary fields; they have no presentation and are not
emitted. [Presentation](TestsClean/Presentation.lean) shows that a prime size is
not enough: a lawful prime-size Clean field whose naturals are not residues
passes import admission but has no presentation.

[TestsClean.Control](TestsClean/Control.lean) is the producer. Run with
`lake env lean --run`, Lean's interpreter evaluates the actual upstream
definitions: `exportComponent`, Clean's witness generator
(`FlatOperation.dynamicWitnesses`) for rows from input values, and
`Expression.eval` of every upstream `Operations.constraints` expression for the
source residuals. It refuses to print unless the zkc AIR model of the decoded
export gives the same residuals on every row. The `zkc.clean-air-control/0`
document holds, per component, the emitted `zkc.air.v0` relation and
`zkc.ring/0` relation arena, the rows and their residuals and verdicts. Mutants
are functions of the actual export (a changed constant, a changed column, a
deleted assertion); each is emitted with its own relation and arena, and its
residuals come from the zkc AIR model, not from Clean.
The document is one canonical JSON line (sorted keys, no spaces) with exactly
these members; the native tools refuse any other shape:

```text
{"format": "zkc.clean-air-control/0",
 "source": {"repository": URL, "revision": COMMIT},
 "presentation": {"field": "koala-bear", "modulus": "2130706433"},
 "components": [{"name", "declaration",
                 "rows": [{"name", "cells": [canonical decimal, ...]}],
                 "subjects": [{"name": "export" first, then mutants,
                               "reference": "clean" | "model",
                               "relation": zkc.air.v0 object, "arena": zkc.ring/0 array,
                               "rows": [{"residuals": [decimal, ...], "holds": bool}]}]}]}
```

[Mutations](TestsClean/Mutations.lean) proves that these mutations of the export
are exactly the artifacts refuted in [Bits](TestsClean/Bits.lean), that each is
still admitted and is not the export, and instantiates the ring-tree theorems.

The [native comparison](../../../tests/protocol/test_clean_air_conformance.py)
runs on the committed control. The C++ tool admits each relation with the
native AIR reader and evaluates it with `AIR::evaluate`, requires each
relation's and arena's native identity to be the digest of its emitted bytes,
and derives one `AIR::expressionView` arena per assertion. The Rust driver
admits every arena independently and evaluates it with the KoalaBear/Ext8
`ring::rows` provider, scalar and packed, whose arithmetic schedule the ring
kernels share. All must agree with the control's residuals. A mutant is admitted
yet has a different identity and disagrees with Clean on the row of its kernel
refutation. Python compares strings only.

Trust boundary: control residuals come from Lean's interpreter evaluating
upstream definitions, not from the kernel; kernel checks cover the fixed traces
in Bits and the mutation equalities. The JSON emission, the C++ readers and
`expressionView`, and the Rust reader and provider are tested on this control,
not proved. The committed control is the current export only when
`just test-lean-clean` (or the fresh reproduction) has been run.

## Controls

The controls use the KoalaBear field `F 2130706433`. Kernel evaluation
(`decide +kernel`) computes exports and both relations; the source side uses
`constraintsHold_iff_flatten`, independent of the exporter and the zkc relation.

- [Bits](TestsClean/Bits.lean): upstream `Gadgets.toBits 4`, four outputs with
  nested Boolean and Equality subcircuits. The export equals an explicitly
  written artifact; honest and invalid traces get the same verdict from both
  relations; an altered constant, an altered column index and a deleted
  booleanity assertion each change the artifact and are refuted on a concrete
  trace. The deleted assertion admits the non-Boolean decomposition
  `0 = -2 + 2·1`. `specification` instantiates `row_spec`.
- [Nested](TestsClean/Nested.lean): upstream `Gadgets.IsEqual` on pairs; four
  assertions three subcircuit levels deep and none shallow.
- [Refusals](TestsClean/Refusals.lean): a lookup only inside a nested
  subcircuit (`Addition8Full`), channel interactions (`add8`), an out-of-range
  variable that Clean would read as zero, and import of noncanonical constants,
  out-of-range columns or a different field size.
- [Mutations](TestsClean/Mutations.lean) and
  [Presentation](TestsClean/Presentation.lean): mutation provenance, mutation and
  emission refusals, and the presentation contract, as described above.
