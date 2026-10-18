# Executable bridge

`check.py` connects the `zkc.program/0` validators that the runtime admits for
the compiled `example::Proof` Entries of the Schnorr and Sumcheck examples to
the [executable stage](../../docs/spec/executable.md) and to the runtime itself.
It is part of `python3 common/tests/run.py lean-native`.

## Reproduce

From `lean/`, with the compiler, the runtime CLI, the main Lean package and the
[ArkLib integration](../../integrations/arklib/README.md) built:

```sh
python3 bridges/executable/check.py --compiler ../build/compiler/zkc-compile \
  --native ../target/release/zkc --output ../build/experiments/executable/run-1
```

`--lake` selects the Lake executable. `--output` must be a new or empty
directory. `--subject schnorr` or `--subject sumcheck` checks one subject
(default: both). `--write` rewrites the committed program data from the fresh
programs instead of requiring it to be unchanged.

## What is checked

For each subject:

1. `language-emit`, `language-bundle` and `language-package` produce the
   original source, the native deployment and the Entry package. The package's
   artifact must be the deployment, its original the emitted bytes, the
   deployment's inner digest the SHA-256 of its `zkc.program/0` candidate, and
   the constructed export's policy the deployment's policy.
2. The committed program data (`SchnorrProofProgramData.lean`,
   `SumcheckProofProgramData.lean`), rendered by `render.py` from the
   deployment with one definition per local function, and the construction data
   (the original's structured rendering and the constructed participant) must
   equal the fresh renderings byte for byte. The Sumcheck original,
   `SumcheckSourceData.lean`, is owned by the structured bridge and compared
   here.
3. A generated Lean file runs `checkLowering` in the kernel on the fresh
   rendering against the fresh constructed-validator export, which must be
   accepted with axioms among `propext`, `Classical.choice` and `Quot.sound`:
   for Schnorr with a total charge of 25, for Sumcheck with the three helpers
   the constructed validator calls by name. It runs the rule on mutated
   programs. For Schnorr nine are refused for their named reasons: operands of
   the final addition swapped (instruction 12), the final comparison made
   trivial (instruction 13), returned values swapped, the base observed instead
   of the commitment (instruction 2), a consumed transcript state reused, an
   uninstalled implementation, an unadmitted representation, a helper's formal
   retyped (its call site) and a duplicated helper. For Sumcheck eight are
   refused: the loop's maximum raised and the round check made trivial (the loop
   instruction), the loop counted by the claim and the carried point and claim
   swapped (the loop and the round check's call site), a consumed transcript
   state reused in a round, the empty-point call retargeted to another function
   (its call site), returned values swapped and an uninstalled observation
   implementation. A changed constant in the terminal check's body is accepted:
   the rule reads a helper body for its sorts and transcript freedom only, and
   what it computes is the obligation `SumcheckHelpers.check_prepared`
   discharges for the committed program, which step 2 ties to the fresh one.
   The validator's row of the deployment's role map, which the runtime uses,
   must select the policy's acceptance output and take the policy's public
   inputs in order, and the same file proves that the Lean statement's
   acceptance position and public inputs are that row's.
4. The runtime proves and verifies with the package under its pin. The verifier
   runs on the honest proof at every instruction budget from 0 to one past its
   acceptance threshold (26 for Schnorr, 191 for Sumcheck) and on mutated
   proofs. Schnorr's eight are undecodable commitments, an out-of-range
   response, a wrong response, a missing or truncated response, a trailing byte
   and another header binding. Sumcheck's eight are an out-of-range and a
   wrongly tagged round message, a changed round message in the first and in
   the second round, a missing or truncated last message, a trailing byte and
   another header binding. For each case, the runtime's outcome, stop site,
   local call, charged instructions, transcript transitions, read messages and
   whole-proof consumption must equal those `execute` predicts for the same
   bytes, under the Entry's checked occurrence context, with every value read
   as zero in `ZMod 5` except that the decoder refuses exactly the payloads a
   mutation corrupted and reads a changed message as one. The changed Sumcheck
   messages stop both meanings at the round check's explicit rejection inside
   its local call, in the round where they occur. The runtime must accept
   exactly the honest proof at the threshold budget (25 and 190), one past it,
   and without a budget. It must reject the wrong Schnorr response as
   `artifact-rejected`, which the value-free prediction cannot distinguish.
5. In the ArkLib integration, every theorem of each receipt's chain, from the
   lowering rule and the helper preparation to the byte-level theorems
   (`ExecutableSchnorrFiatShamir.knowledge_soundness`,
   `ExecutableSumcheckFiatShamir.adaptive_soundness`), must depend only on
   `propext`, `Classical.choice` and `Quot.sound`. A walk over the constants each
   byte-level theorem's proof uses must reach the general rules
   (`Zkc.Construction.compiled_transform`, `check_sound`, `project_sound`, and
   the lowering rule's `validate_ideal` and `validate_rejects` for Schnorr or
   `validate_prunes` for Sumcheck), the admitted original they are applied to
   and the Entry's per-compile checks (`compiled`, the executable `accepted`),
   for Sumcheck also `SumcheckHelpers.check_prepared`, `Prunes.prEvent_le` and
   the binding's `initial_determined`; the Schnorr proof must not reach
   `ZkcExamples.Construction.SchnorrProof.spec_equation`. The walk then lists
   the Entry-specific theorems it reaches (in example namespaces) whose
   statement is an equation between processes, with whether the kernel checks
   each by evaluation (`rfl`) and whether its statement names a compiled
   meaning (`spec`, `ideal`, `execute`, `validate`, `metered` or their steps).
   None may name a compiled meaning: the chains use no equation specific to an
   Entry about the compiled program. The classification must flag
   `spec_equation` when the walk starts from it. The original-side equations
   are recorded in each receipt.
6. `receipt.json` names the compiler, runtime, Lean toolchain and manifest
   identities, the source module, original, export, program, deployment,
   descriptor and package digests, the Lean data digests, the runtime's
   role-map selection, the checked rules (the composed construction and
   projection check `checkCompiled` with its admitted subject, its soundness
   theorems, and the lowering rule with, for Sumcheck, the helper preparation),
   the theorem, the checked axioms of its chain, the proof dependencies checked
   in step 5 and the remaining assumptions. Under the receipt's package pin the
   runtime must accept the honest proof, report that pin and reject the wrong
   proof. A package with a mutated program (the Schnorr comparison made trivial;
   the Sumcheck round check and terminal comparison made trivial) is refused
   under that pin; re-pinned, it accepts the wrong proof but its program digest
   differs from the receipt's; a program changed without its inner digest is
   refused by the runtime's candidate binding.

The retained `report.json` lists commands, exit statuses, digests, the paired
runtime and Lean observations and every check.

## Boundaries

The comparison covers control: budgets, loop iterations, local calls and the
call context at a stop, framing, decoding failures, explicit rejections and
transcript transitions; frame events are not compared. Values are mapped to a
small field, so the verifier's Boolean on an accepted run is the runtime's; the
Lean prediction only says that the run returned. The codec's validity decisions
are supplied by the mutation, not checked. None of the cases reaches the inputs
on which the runtime and the meaning are known to differ, which are listed in
[support](../../docs/support.md). This is bounded agreement evidence for the
trusted execution link, not a proof that the runtime implements the executable
meaning. The renderer's reading of the program bytes is a trusted link: the
data names the digest of the bytes it was read from, and step 2 requires the
fresh rendering, but no Lean reader of the bytes is proved.
