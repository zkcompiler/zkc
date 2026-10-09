# Clean relation integration

This optional Lake package exports a selected fragment of
[Clean](https://github.com/Verified-zkEVM/clean) flat AIR components into the
independent zkc finite AIR (`Zkc.Relation.AIR`) and proves the correspondence
against Clean's own definitions. The main `formal/` package has no Clean
dependency. The package uses a local path dependency on main and exact pins.

```sh
cd formal/integrations/clean
lake build
```

The first build clones the pinned sources into `.lake/packages`. Fetch Mathlib's
published objects there with `lake exe cache get`, or link those entries to an
existing checkout of the same revisions. Do not run `lake update`: it would
re-resolve the reviewed manifest.

`lake build` builds the library and its controls. [TestsClean.Audit](TestsClean/Audit.lean)
audits every owned declaration with `Tools.DeclarationAudit` and records the axioms
of the selected bridge and upstream declarations. Only `propext`,
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

The theorems relate Lean terms: a Clean component, its exported artifact and the
zkc relation decoded from that artifact. They do not prove a native importer,
evaluator, DAG decoder or compiled execution, channel balance, a STARK reduction
or Fiat-Shamir security. The Rust and C++ paths need their own checked artifact
comparison or proved decoder before these statements describe them.

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
