# Protocol verification in Lean

The maintained formal libraries other than Core share one typed `Region` source and
one effectful `Process` semantics. Independent structured-source admission supplies
an actual typed program. The protocol framework supplies quantitative contracts,
structural proof construction, installation and claim assembly. The mathematical libraries
and optional ArkLib and Clean adapters are independent of a native connection.

The former scalar source views, generated subject proofs, constructed-participant
connections and executable-byte proof route have been retired. Their native
formats remain supported by the compiler and runtime; no replacement formal
connection is implied. The current package does not claim compiled Schnorr,
Sumcheck, GKR, FRI or STARK security. See [support](docs/support.md) for the exact
boundary, and [source construction](docs/spec/source-construction.md) for the
shared framework and actual-source law installation.

## What is proved

<!-- BEGIN GENERATED what-is-proved: lean/checks/check_records.py --write -->
| Subject | Result | Theorems | Owner |
|---|---|---|---|
| Structured import | Independent admission, declaration linking, checked primitives, maps and realizations, protocol applications, Boolean selection and repeats | `Zkc.Source.Structured.Imported.exactSubject`, `Zkc.Source.Structured.check_ok_inversion`, `Zkc.Source.Structured.Imported.protocolApplication` | [Structured source](docs/spec/structured-source.md), [support](docs/support.md) |
| Multilinear Sumcheck | Table laws for any round count; ArkLib `n / \|F\|` complete and `k / \|F\|` residual bounds | `Zkc.Protocols.Sumcheck.Multilinear.check_of_residual`, `ZkcSecurity.ArkLib.Sumcheck.Multilinear.publicTable_soundness`, `ZkcSecurity.ArkLib.Sumcheck.Multilinear.residual_soundness` | [Mathematics](docs/spec/multilinear-sumcheck.md), [security](docs/spec/multilinear-sumcheck-security.md) |
| Clean AIR | A flat AIR export preserves its constraints and selected specification | `ZkcClean.guarantees_of_export`, `ZkcClean.holds_iff`, `ZkcClean.table_spec` | [Clean integration](adapters/clean/README.md) |
| Scoped KZG evaluation binding | The concrete average-success opening game is the pinned ArkLib binding experiment and is bounded by the pinned reduction, under a named resource-admissibility predicate, reduction closure, budget and scoped SDH hardness. No efficiency theorem, all-functions hardness, knowledge soundness, source import or native realization is claimed | `ZkcArkLib.Kzg.averageSuccess_eq_bindingExperiment`, `ZkcArkLib.Kzg.scoped_bound` | [Selected property adapters](docs/spec/selected-property-adapters.md), [ArkLib integration](adapters/arklib/README.md) |
| Shared quantitative source construction | Upper and lower bounds over the actual typed Region/Process meaning, reusable structural operation/callback rules and complete adaptive/stateful model clients; generated-controller correspondence is separate | `ProtocolProof.OperationSpec.lowerBound_iff_triple`, `ProtocolProof.OperationSpec.upperBound_iff_triple`, `ProtocolProof.Construction.regionOperation`, `ProtocolProof.Construction.finiteRepeat`, `ProtocolProofExamples.AdaptiveSource.adaptive_soundness`, `ProtocolProofExamples.AdaptiveSource.honest_completeness`, `ProtocolProofExamples.StatefulOracle.proximity`, `ProtocolProofExamples.StatefulOracle.honest_completeness` | [Construction](docs/spec/source-construction.md), [Authoring](docs/development/source-construction.md) |
| Actual-source law installation | Exact helper dependency framing and participant installation on admitted native exports; repeated-call reuse, shared service state and finite-loop clients. No generated-controller or compiled cryptographic security endpoint is claimed | `Zkc.Verification.Construction.helper`, `Zkc.Verification.Construction.component`, `Zkc.Verification.Construction.protocol`, `ActualSourceConstruction.Twice.participant_law`, `ActualSourceConstruction.DrawPair.participant_law`, `ActualSourceConstruction.Replace.participant_law` | [Construction](docs/spec/source-construction.md), [Authoring](docs/development/source-construction.md) |
| Proposition-valued readings | Charged, exact and cost readings of the actual typed Region/Process meaning, constructed by the common constructor with one rule per primitive node and connected by adequacy to the retained Fiat–Shamir endpoint and an interactive endpoint; model clients: Sumcheck soundness, soundness for a prover-chosen statement sent in the clear (identity extractor, not extraction from a commitment), an exact three-move characterization, and the opening check in an ideal algebraic game (representations fixed before the secret, no published reference string; not KZG evaluation binding). These clients are model verifiers; imported core sides are in the row of the core language. No compiled protocol is connected | `ZkcSecurity.Obligations.WeakestPrecondition.call_spec`, `ZkcSecurity.Obligations.WeakestPrecondition.call_cost`, `ZkcSecurity.Obligations.WeakestPrecondition.charged_of_triple`, `ZkcSecurity.Obligations.WeakestPrecondition.costBound_of_triple`, `ZkcSecurity.Obligations.WeakestPrecondition.bounded_of_exact`, `ZkcSecurity.Interactive.soundness`, `ProtocolProofExamples.ChargedSumcheck.fiat_shamir_soundness`, `ProtocolProofExamples.ChargedSumcheck.interactive_soundness`, `ProtocolProofExamples.ExtractionSumcheck.extraction_soundness`, `ProtocolProofExamples.ExactThreeMove.transcript_decides`, `ProtocolProofExamples.SetupOpening.setup_soundness` | [Weakest preconditions](docs/spec/weakest-preconditions.md), [Construction](docs/spec/source-construction.md), [Authoring](docs/development/source-construction.md) |
| Core language | A kernel-checked model of `zkc.core/0` packages: typed definitions, residual well-formedness and, for every side, a process over one effect signature, with equations for one operation at a time and generated table and entry equations. The common constructor walks a side at a literal side with one step per operation, reuses a law of a callee through `apply`, and reads the side by a transcript interface with an explicit policy for secrets. Clients, for every model: the exact reading of the Schnorr verifier and of the setup and verifier of an opening protocol (a characterization of runs, not binding), and the Sumcheck verifier's interactive `rounds / \|F\|` and Fiat–Shamir `(queries + rounds) / \|F\|` bounds under field and restricted multilinearity laws of the model, which the model that restricts a table by folding satisfies: at that model a claim that is not the sum of a table of `2^n` scalars is accepted with probability at most `n / \|F\|`. Oracle operations, `match`, contracts, stages other than the original and the package bytes are outside | `Zkc.Core.Reason.stop_ne_incomplete`, `Zkc.Core.sideMeaning_step`, `Zkc.Core.repeat_meaning`, `Zkc.Core.apply_meaning`, `Zkc.Core.agreed_single`, `Zkc.Core.Program.table_unfold`, `Zkc.Core.Program.entry_there`, `Zkc.Tests.Core.Schnorr.honest_accepts`, `Zkc.Tests.Core.Sumcheck.sumcheck_verifier`, `Zkc.Core.Step.pure_row`, `Zkc.Core.Step.apply`, `Zkc.Core.Step.repeat`, `Zkc.Core.Transcript.forall_recovered`, `Zkc.Tests.Verification.Core.Schnorr.verifier_decides`, `Zkc.Tests.Verification.Core.Sumcheck.round_wrong`, `Zkc.Tests.Verification.Core.Sumcheck.interactive_soundness`, `Zkc.Tests.Verification.Core.Sumcheck.fiat_shamir_soundness`, `Zkc.Tests.Verification.Core.Sumcheck.fold_laws`, `Zkc.Tests.Verification.Core.Sumcheck.table_soundness`, `Zkc.Tests.Verification.Core.Opening.setup_verifier_decides` | [Core language model](docs/spec/core-language.md), [Construction](docs/spec/source-construction.md), [Authoring](docs/development/source-construction.md) |
<!-- END GENERATED what-is-proved -->

The table is generated from the reviewed theorem ledger. Its locks detect changes
to cited statements; hashes do not prove semantic preservation. Fresh declaration
records also inspect stored proof bodies and axiom dependencies, including private
declarations. An empty native endpoint registry confers no native guarantee.

## Architecture

| Package | Responsibility |
| --- | --- |
| [Program](program/README.md) | Typed contexts, regions, processes, outcomes and deterministic execution |
| [Protocol](protocol/README.md) | Reusable mathematical interfaces, probability, quantitative construction and security claims |
| IR | Concrete operation meanings, nominal domains, independent structured-source admission and source contracts |
| [Verification](verification/README.md) | Mathematical laws instantiated against concrete IR meanings |
| [ArkLib](adapters/arklib/README.md), [Clean](adapters/clean/README.md) | Explicitly scoped external mathematical adapters |
| [Applications](applications/README.md) | Surviving concrete downstream consumers |
| [Core](core/README.md) | The re-founded core language and its tool: elaboration, steps, links, executor and structural theorems. No Lake dependency; its dependent is Formal, and its import closure is disjoint from those of the other packages |
| [Formal](formal/README.md) | Statements about admitted programs over Core's meaning, and their proofs: the relation of two models of a program, the model of a package's rows in an arithmetic, and the arithmetic of BLS12-381 related to the model that runs. Requires Core; no dependent |

Source meaning, mathematical assumptions, source association and a security claim
are separate judgments. A mathematical law cannot change an admitted operation or
replace its reached stop with a successful return. A lookup name identifies a
candidate proof; its checked type determines applicability.

## Build and use

Follow [development](../docs/development/README.md) for pinned dependencies. Run
Lake from the owning package, for example:

```sh
cd lean/protocol
lake build +Zkc.Tests.Protocol.Construction.AdaptiveSource
```

`just test-lean` checks the maintained core. `just test-lean-integration` adds the
optional mathematical adapters and consumers. The independent `lean-native` lane
checks actual structured-source admission and compares execution with the native
SSA reference; it generates no protocol proof. Select affected checks and reuse
valid incremental results as described in the [test guide](../common/tests/README.md).

`python3 lean/reproduce.py --help` describes reproducible package builds and audits.
The old subject manifests, bridge generators and assurance-report CLI are absent.
Generic declaration records are documented [here](docs/spec/declaration-records.md).

## Further reading

- [Formal reference](docs/README.md) and [architecture](docs/architecture.md)
- [Construction authoring](docs/development/source-construction.md)
- [Framework claims and open boundaries](protocol/docs/CLAIMS.md)
- [Native assurance scope](../docs/assurance.md)
