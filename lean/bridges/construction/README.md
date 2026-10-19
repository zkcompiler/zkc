# Transcript-construction bridge

The compiled proof Entries of the subject manifests in
[`lean/subjects`](../../subjects/README.md) with the construction profile are
connected to the
[formal transcript-construction rule](../../docs/spec/fiat-shamir.md) and the
[participant projection rule](../../docs/spec/participant-projection.md) by the
subject driver, [`lean/bridges/subject.py`](../subject.py). `check.py` here is
its compatibility entry point: it runs the driver on every manifest with the
construction profile. `render.py` renders a `zkc.constructed-participant/0`
export as Lean data. The driver is part of
`python3 common/tests/run.py lean-native`.

## Reproduce

From the repository root, with the compiler and the main Lean package built:

```sh
python3 lean/bridges/construction/check.py --output build/experiments/construction/run-1
python3 lean/bridges/subject.py --subject schnorr --check --output build/experiments/subjects/run-1
```

`--compiler` selects `zkc-compile` (default `build/compiler/zkc-compile`) and
`--lake` the Lake executable. `--output` must be a new or empty directory; each
subject writes into its own subdirectory. `--write` rewrites the generated Lean
modules the manifests own from the fresh exports instead of requiring them to
be unchanged.

## What is checked

For each subject with the construction profile:

1. `language-emit`, `language-interface` and `language-bundle` produce the
   Entry's original source, its interface and the native deployment; the
   interface and the deployment must name the emitted bytes, and the policy is
   retained.
2. `protocol-construct-proof` constructs the candidate, and
   [`protocol-constructed-participant`](../../../docs/spec/formats/constructed-participant.md)
   checks and exports its validator. `protocol-structured` exports the original.
   Both exports must name the same source bytes and policy.
3. The generated modules must equal the fresh renderings byte for byte: the
   original's data (rendered by the structured bridge's `snapshot.py`), the
   constructed participant (rendered by `render.py`), the typed bodies printed
   from the admitted original by the structured bridge's `bodies.py`, and the
   per-Entry glue. The glue admits the original from the printed bodies with
   `structured_views` (or names an existing Views module), checks the composed
   rules (`compiled`) and the selection of the export's inputs and acceptance
   output (`selection_checked`) in the kernel, and instantiates
   `Zkc.Construction.compiled_selected`, so `compiled_transform` holds with no
   proof specific to the Entry. A manifest's `[construction] model` adds the
   definitional equation of the original validator with a model process and the
   interactive reading of the constructed program (`spec_equation`).
4. A generated Lean file runs the composed check `checkCompiled` and the
   selection check in the kernel on the fresh export against the admitted
   original, which must be accepted with axioms among `propext`,
   `Classical.choice` and `Quot.sound`. The fresh original snapshot must be the
   retained one (`original_retained`, by `rfl`), so the retained admission is
   the fresh original's admission. The same file checks that the Lean model of
   the canonical occurrence encoding (`templateTree`) encodes every exported
   template to exactly its native bytes.
5. The manifest's generic mutation kinds are applied to the fresh export (see
   `python3 lean/bridges/subject.py --list-mutations`): each applicable site must
   change the export, still render, and be refused by the rule its kind names
   (a `construction-` or `projection-` code, recorded); a kind that keeps the
   transcript wiring must also be accepted by `checkExport` alone. Native kinds
   mutate the candidate MLIR, which the native checker must refuse with the
   kind's code.

The retained `report.json` lists commands, exit statuses and checks, and each
subject's `evidence.json` the artifact and module digests, kernel results and
mutation outcomes.

## Boundaries

`render.py` classifies operations by exact name, operation binding and attribute
set, including `arith.andi` on Booleans as the Boolean conjunction. An
unrecognized operation is retained as unsupported for the rule to refuse; a
recognized one with another shape refuses the export
(`lean/checks/check_construction_renderer.py` exercises the conjunction). It
decodes each origin's canonical bytes into a template with its application and
repeat steps, requires the static coordinate array to be empty and re-encodes it
exactly. It parses printed MLIR types of the scalar, vector, index, transcript
and coordinate sorts and refuses others. A loop's captured block arguments
denote its captured operands in every iteration, so the rendered body refers
to those operands directly and the rendered loop keeps its count and carried
values; a captured transcript, or a capture whose block argument has another
sort, refuses the export (the renderer check exercises both, and a nested loop
capturing its enclosing induction index). Native exporter correctness, this
rendering, and the meanings of native kernels are tested boundaries, not
theorems.
