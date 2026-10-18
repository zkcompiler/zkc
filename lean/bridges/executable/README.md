# Executable bridge

`check.py` connects the `zkc.program/0` validator that the runtime admits for
the compiled `example::Proof` Schnorr Entry to the
[executable stage](../../docs/spec/executable.md) and to the runtime itself. It
is part of `python3 common/tests/run.py lean-native`.

## Reproduce

From `lean/`, with the compiler, the runtime CLI, the main Lean package and the
[ArkLib integration](../../integrations/arklib/README.md) built:

```sh
python3 bridges/executable/check.py --compiler ../build/compiler/zkc-compile \
  --native ../target/release/zkc --output ../build/experiments/executable/run-1
```

`--lake` selects the Lake executable. `--output` must be a new or empty
directory. `--write` rewrites the committed validator data from the fresh
program instead of requiring it to be unchanged.

## What is checked

1. `language-emit`, `language-bundle` and `language-package` produce the
   original source, the native deployment and the Entry package. The package's
   artifact must be the deployment, its original the emitted bytes, the
   deployment's inner digest the SHA-256 of its `zkc.program/0` candidate, and
   the constructed export's policy the deployment's policy.
2. `lean/ZkcExamples/Executable/SchnorrProofProgramData.lean`, rendered by
   `render.py` from the deployment, and the two construction data files, rendered
   by the structured and construction renderers from the fresh exports, must equal
   the fresh renderings byte for byte.
3. A generated Lean file runs `checkLowering` in the kernel on the fresh
   rendering against the fresh constructed-validator export, which must be
   accepted with a total charge of 25 and axioms among `propext`,
   `Classical.choice` and `Quot.sound`, and on nine mutated programs, each
   refused for its named reason: operands of the final addition swapped
   (instruction 12), the final comparison made trivial (instruction 13),
   returned values swapped, the base observed instead of the commitment
   (instruction 2), a consumed transcript state reused, an uninstalled
   implementation, an unadmitted representation, a helper's formal retyped
   (its call site) and a duplicated helper. The validator's row of the
   deployment's role map, which the runtime uses, must select the policy's
   acceptance output and take the policy's public inputs in order, and the
   same file proves that the Lean statement's acceptance position and public
   inputs are that row's.
4. The runtime proves and verifies with the package under its pin. The verifier
   runs on the honest proof at every instruction budget from 0 to 26 and on
   eight mutated proofs: undecodable commitments, an out-of-range response, a
   wrong response, a missing or truncated response, a trailing byte and another
   header binding. For each, the runtime's outcome, stop site, local call,
   charged instructions, transcript transitions, read messages and whole-proof
   consumption must equal those `execute` predicts for the same bytes, under the
   Entry's checked occurrence context and with a decoder that refuses exactly
   the payloads the mutation corrupted. The
   runtime must accept exactly the honest proof at budgets 25 and 26 and
   without a budget, and must reject the wrong response as
   `artifact-rejected`, which the value-free prediction cannot distinguish.
5. In the ArkLib integration, every theorem of the receipt's chain, from the
   lowering rule to the byte-level knowledge-soundness theorem, must depend only
   on `propext`, `Classical.choice` and `Quot.sound`. A walk over the constants
   the byte-level theorem's proof uses must reach the general rules
   (`Zkc.Construction.compiled_transform`, `check_sound`, `project_sound`, the
   lowering rule's `validate_ideal` and `validate_rejects`), the admitted
   original they are applied to (`SchnorrProof.imported`) and the Entry's
   per-compile checks (`SchnorrProof.compiled`, the executable `accepted`), and
   must not reach `ZkcExamples.Construction.SchnorrProof.spec_equation`. The walk
   then lists the Entry-specific theorems it reaches (in example namespaces)
   whose statement is an equation between processes, with whether the kernel
   checks each by evaluation (`rfl`) and whether its statement names a compiled
   meaning (`spec`, `ideal`, `execute`, `validate` or their steps). None may name
   a compiled meaning: the chain uses no equation specific to this Entry about
   the compiled program. The classification must flag `spec_equation` when the
   walk starts from it. The original-side equations are recorded: today the
   kernel-evaluated `SchnorrProof.process_equation` (the admitted original's
   validator is the Schnorr experiment the VCVio consumer uses) and
   `SchnorrProofBinding.formula_process` (the process of the retained DLog
   formula), and `original_verifier` and `verifier_correspondence`, derived from
   them.
6. `receipt.json` names the compiler, runtime, Lean toolchain and manifest
   identities, the source module, original, export, program, deployment,
   descriptor and package digests, the Lean data digests, the runtime's
   role-map selection, the checked rules (the composed construction and
   projection check `checkCompiled` with its admitted subject, its soundness
   theorems, and the lowering rule), the theorem, the checked axioms of its
   chain, the proof dependencies checked in step 5 and the remaining
   assumptions. Under the receipt's package pin the
   runtime must accept the honest proof, report that pin and reject the wrong
   response. A package with a mutated program is refused under that pin;
   re-pinned, it accepts the wrong response but its program digest differs from
   the receipt's; a program changed without its inner digest is refused by the
   runtime's candidate binding.

The retained `report.json` lists commands, exit statuses, digests, the paired
runtime and Lean observations and every check.

## Boundaries

The comparison covers control: budgets, the local-call context at a stop,
framing, decoding failures and transcript transitions; frame events are not
compared. Values are mapped to a small field, so the verifier's Boolean on an
accepted run is the runtime's; the Lean prediction only says that the run
returned. The codec's validity decisions are supplied by the mutation, not
checked. None of the cases reaches the inputs on which the runtime and the
meaning are known to differ, which are listed in
[support](../../docs/support.md). This is bounded agreement evidence for the
trusted execution link, not a proof that the runtime implements the executable
meaning.
