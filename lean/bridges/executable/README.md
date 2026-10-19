# Executable bridge

The `zkc.program/0` validators that the runtime admits for the compiled proof
Entries of the subject manifests in [`lean/subjects`](../../subjects/README.md)
with the executable profile are connected to the
[executable stage](../../docs/spec/executable.md) and to the runtime itself by
the subject driver, [`lean/bridges/subject.py`](../subject.py), with
`--runtime`. `check.py` here is its compatibility entry point: it runs the
driver on every manifest with the executable profile (or the named
`--subject`s). `render.py` renders the validator of a native deployment as Lean
data. The driver is part of `python3 common/tests/run.py lean-native`.

## Reproduce

From the repository root, with the compiler, the runtime CLI, the main Lean
package and the [ArkLib integration](../../integrations/arklib/README.md)
built:

```sh
python3 lean/bridges/executable/check.py --output build/experiments/executable/run-1
python3 lean/bridges/subject.py --subject sumcheck --check --runtime \
  --output build/experiments/subjects/run-1
```

`--compiler`, `--native` and `--lake` select the tools. `--output` must be a new
or empty directory. `--write` rewrites the generated modules from the fresh
programs and exports instead of requiring them to be unchanged.

## What is checked

For each subject with the executable profile, after the construction checks:

1. `language-package` produces the Entry package. The package's artifact must
   be the deployment, its original the emitted bytes, the deployment's inner
   digest the SHA-256 of its `zkc.program/0` candidate, and the constructed
   export's policy the deployment's policy. Declared variants
   (`[executable] variants`) are bundled with their options.
2. The program data, rendered by `render.py` with one definition per local
   function, and the generated executable facts must equal the fresh renderings
   byte for byte. The facts module states the accepted reading (`lowered`,
   `accepted`), the helpers the constructed validator calls, its static charge
   and message types when they are static, and admission of the published
   inputs; the kernel checks each. The facts are declared in the namespace
   the Entry's hand executable module continues (`[executable] namespace`).
3. A generated Lean file runs `checkLowering` in the kernel on the fresh
   rendering against the fresh constructed-validator export, which must be
   accepted with axioms among `propext`, `Classical.choice` and `Quot.sound`,
   and accepts every declared variant. Lean evaluates the reading's static
   charge, message types, helpers and whether the reading is the constructed
   validator instruction for instruction (checked against `[executable] exact`
   when declared). The acceptance threshold is derived from the Lean charge: the
   static total charge, or the manifest's charge function at the public inputs
   it names, evaluated once the generated facts are regenerated. Every module a
   generated Lean file imports, hand proofs included, is built before the file
   is evaluated, so no result comes from a stale build. The manifest's generic program mutation kinds are applied to the
   fresh program: each applicable one must be refused by the rule (its reason is
   recorded), or accepted when its kind changes only what the rule does not read
   (a helper body's computation, which a preparation obligation covers).
   Helper kinds edit the local function of a called helper: wherever the
   helper rule (`checkHelpers`) accepts the actual helper against the admitted
   program's checked helper of its name, the rule must refuse the copy (its
   refusal is recorded) while the lowering rule accepts it. The
   validator's row of the deployment's role map, which the runtime uses, must
   select the policy's acceptance output and take the policy's public inputs in
   order, and the same file proves that the Lean statement's acceptance position
   and public inputs are that row's.
4. The runtime proves and verifies with the package under its pin. The verifier
   runs on the honest proof at every instruction budget from 0 to one past the
   derived threshold and on generic proof edits chosen by payload shape: a
   wrongly tagged first message, a group message outside the group, a field
   message out of range, every field message changed to another value, the last
   message missing or truncated, a trailing byte and another header binding.
   For each case, the runtime's outcome, stop site, local call, charged
   instructions, transcript transitions, read messages and whole-proof
   consumption must equal those `execute` predicts for the same bytes, under the
   Entry's checked occurrence context, with every value read as zero in
   `ZMod 5` except that the decoder refuses exactly the payloads an edit
   corrupted and reads a changed message as one. The runtime must accept exactly
   the honest proof at the threshold budget, one past it, and without a budget,
   and must reject every changed message.
5. In the ArkLib integration, every theorem of each manifest's receipt chain
   must depend only on `propext`, `Classical.choice` and `Quot.sound`. A walk
   over the constants each receipt theorem's proof uses must reach the
   declarations the manifest lists as used and avoid those it lists as unused.
   The walk then lists the Entry-specific theorems it reaches (in example
   namespaces) whose statement is an equation between processes, with whether
   the kernel checks each by evaluation (`rfl`) and whether its statement names
   a compiled meaning (`spec`, `ideal`, `execute`, `validate`, `metered` or their
   steps). None may name a compiled meaning. The classification must flag the
   generated `spec_equation` of a subject with a model when the walk starts from
   it.
6. Each subject's `evidence.json` records the artifact digests, the runtime's
   role-map selection, the derived threshold, the runtime summary, the axiom
   closures and proof dependencies of step 5 and the requested assumptions. The
   runtime must accept the honest proof under the recorded package pin, report
   that pin and reject a changed proof. A package whose program compares every
   data value with itself is refused under that pin; re-pinned, it accepts the
   changed proof but its program digest differs from the record's; a program
   changed without its inner digest is refused by the runtime's candidate
   binding.

The retained `report.json` lists commands, exit statuses, digests and every
check.

## Boundaries

The comparison covers control: budgets, loop iterations, local calls and the
call context at a stop, framing, decoding failures, explicit rejections and
transcript transitions; frame events are not compared. Values are mapped to a
small field, so the verifier's Boolean on an accepted run is the runtime's; the
Lean prediction only says that the run returned. The codec's validity decisions
are supplied by the edit, not checked. None of the cases reaches the inputs on
which the runtime and the meaning are known to differ, which are listed in
[support](../../docs/support.md). This is bounded agreement evidence for the
trusted execution link, not a proof that the runtime implements the executable
meaning. The renderer's reading of the program bytes is a trusted link: the
data names the digest of the bytes it was read from, and step 2 requires the
fresh rendering, but no Lean reader of the bytes is proved.
