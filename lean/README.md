# Protocol verification in Lean

This package holds independent Lean models of zkc programs and proves claims
about the programs the compiler actually exports. Two imports connect it to the
compiler: the scalar common-source profile, and the structured profile, which
admits original protocol-stage PIR with shared helpers, participants, services,
protocol applications and repeats. Lean checks each import's typed admission;
for selected imports it proves open-process contracts from checked derivations
and local mathematical laws. Optional packages then apply ArkLib and VCVio
security theorems to those subjects.

The [formal reference](docs/README.md) defines the models, and
[support](docs/support.md) states the exact scope and assumptions of each claim.
Native compilation below the original stage is outside these claims except
where a checked rule relates a later artifact: the constructed validators of
compiled proof Entries and the executable validators the runtime admits for the
Schnorr and Sumcheck Entries and a deferred-rounds fixture.
Providers and production arithmetic are outside them. Fiat–Shamir claims cover
the Schnorr family (for Schnorr, the transform of the imported interactive
verifier, the compiled proof Entry and its executable validator; for Schnorr AND
and Chaum–Pedersen, the transforms of the imported interactive verifiers) and
the transform of any validator with a round-by-round soundness certificate,
applied to the imported Sumcheck verifier, to the ideal interpretation of the
compiled Sumcheck proof Entry and to its executable validator, to the plain
GKR verifier and the ideal interpretation of the compiled GKR proof Entry, to the
ideal interpretation of a compiled guessing Entry through a certificate imported
from ArkLib's worst-case round-by-round soundness, to verifiers with committed
tables read with roots and openings, and to the FRI verifier model with
commitments read in the clear and with words committed by Merkle trees, under
named assumptions. For the native hash-chain suites a provider simulation
reduces the construction's byte-level chain model to the history oracle; the
link from the compiled transcript handlers and installed kernels to that model
remains an obligation. The Schnorr-family and GKR claims fix the statement; the other
multi-round ones also cover statements chosen after the oracle queries when the initial
transcript determines them, which the compiled and executable Sumcheck statements
discharge with a typed public-value binding of the table values, claim and round
count. That binding establishes statement determination only; that the native
transcript absorbs the encoded rows remains assumed. The [common](bridges/common/README.md)
and [structured](bridges/structured/README.md) bridges test the native boundary
with independent execution and negative controls.

## What is proved

<!-- BEGIN GENERATED what-is-proved: lean/checks/check_records.py --write -->
| Subject | Result | Theorems | Owner |
|---|---|---|---|
| Scalar imports | Admission and open-process contracts of exported scalar programs; Schnorr completeness, special soundness and rejection; the two-round degree-two Sumcheck bound `4 / \|F\|` | `Zkc.Source.Common.Native.Snapshot.check_parts`, `Zkc.Protocols.Schnorr.Common.VerifierContract.perfect_completeness`, `Zkc.Protocols.Schnorr.Common.VerifierContract.special_soundness`, `Zkc.Protocols.Sumcheck.Common.VerifierContract.soundness` | [Scalar import](docs/spec/common-source.md), [support](docs/support.md) |
| Structured import | Independent admission, declaration linking, checked primitives, maps and realizations, protocol applications and repeats | `Zkc.Source.Structured.Imported.exactSubject`, `Zkc.Source.Structured.check_ok_inversion`, `Zkc.Source.Structured.Imported.protocolApplication` | [Structured source](docs/spec/structured-source.md), [support](docs/support.md) |
| Interactive Schnorr | Verifier contracts over the actual export; an honest prover derived from checked sends; VCVio Sigma completeness, special soundness and fresh-challenge simulation | `ZkcExamples.Structured.SchnorrInteractive.perfect_completeness`, `ZkcExamples.Structured.SchnorrInteractive.special_soundness`, `ZkcSecurity.Examples.StructuredSchnorrSigma.fresh_challenge_hvzk` | [Schnorr subject](docs/support.md#interactive-schnorr), [security integration](integrations/arklib/README.md) |
| Compiled Schnorr proof | Checked transcript-construction and participant projection rules accept the actual compiled validator; by their composed soundness, the ideal interpretation of the exported validator is the Fiat–Shamir transform of the original verifier, with a fixed-statement extraction-probability bound in the random-oracle model via VCVio | `ZkcExamples.Construction.SchnorrProof.compiled_transform`, `ZkcSecurity.Examples.CompiledSchnorrFiatShamir.knowledge_soundness` | [Fiat–Shamir construction](docs/spec/fiat-shamir.md), [participant projection](docs/spec/participant-projection.md), [support](docs/support.md) |
| Executable Schnorr proof | A checked lowering rule accepts the `zkc.program/0` validator the runtime admits against that constructed validator; its meaning, with proof framing, any decoder, an instruction budget, frames and transcript custody, reflects acceptance at every budget, and the extraction bound transfers to provers of proof bytes through the general construction, projection and lowering rules, with no Entry-specific equation about the compiled program | `ZkcExamples.Executable.SchnorrProof.executable_transform`, `ZkcSecurity.Examples.ExecutableSchnorrFiatShamir.knowledge_soundness` | [Executable stage](docs/spec/executable.md), [support](docs/support.md) |
| Executable Sumcheck proof and normalization | The lowering rule accepts the executable Sumcheck validator, with a loop and helper calls whose program bodies are proved to implement the source's checked helpers (the helpers inside the helper rule's recipe table by the rule, proved sound once, and the terminal check by its own proof), and, through checked normalization of pure total calculations, a deferred-rounds program that computes a round's product after a later draw; accepted normal forms have equal ideal meanings. Host validation prunes the transform of the original Sumcheck verifier at every budget, so the compiled bounds transfer to provers of proof bytes; at a budget sufficient for every run the executable is the ideal meaning, and honest-prover completeness holds at every budget of at least `68 + 59 · rounds` instructions for every round count up to the Entry's static maximum, with proofs that do not depend on the value of the maximum | `Zkc.Executable.checkNormalized_sound`, `Zkc.Executable.checkHelpers_sound`, `ZkcExamples.Executable.SumcheckProof.executable_transform_prunes`, `ZkcExamples.Executable.SumcheckCompleteness.honest_accepted`, `ZkcExamples.Executable.SumcheckFamily.honest_accepted`, `ZkcSecurity.Examples.ExecutableSumcheckFiatShamir.adaptive_soundness`, `ZkcExamples.Executable.DeferredRounds.executable_validate` | [Executable stage](docs/spec/executable.md#the-compiled-sumcheck-proof-verifier), [normalization](docs/spec/executable.md#normalization), [support](docs/support.md) |
| Compiled Sumcheck proofs | The same composed rules accept the actual compiled validators of the Sumcheck example, with a protocol application and a repeat, and of its composed variant, with two applications; the ideal interpretation of each is the Fiat–Shamir transform of the original verifier, for the first the source rounds followed by the multilinear check. Composed with the multi-round bound, the first's ideal interpretation accepts a false claim with probability at most `(Q + n) / \|F\|` in the random-oracle model for a fixed well-formed statement, attained on a concrete instance, and adaptively chosen statements are bounded under the typed public-value binding of the table values, claim and round count, which establishes statement determination only (native absorption of the encoded rows remains assumed); the composed variant has no security theorem | `ZkcExamples.Construction.SumcheckProof.compiled_transform`, `ZkcExamples.Construction.ComposedSumcheckProof.compiled_transform`, `ZkcSecurity.Examples.CompiledSumcheckFiatShamir.soundness`, `ZkcSecurity.Examples.CompiledSumcheckFiatShamir.adaptive_soundness` | [Participant projection](docs/spec/participant-projection.md#the-compiled-sumcheck-proof-entry), [multi-round security](docs/spec/fiat-shamir-security.md#the-compiled-sumcheck-proof-entry), [support](docs/support.md) |
| GKR | The plain verifier of the GKR library has a charged certificate composed from one reduction per phase, each at its challenge site's error (`1 / \|F\|` at the output point, ArkLib's degree-two successor bound `2 / \|F\|` for the layer rounds, Schwartz–Zippel on a line `width / \|F\|` for the line challenge); against a weighted adversary budget, each oracle key charged its site's error, its transform accepts claimed outputs other than the circuit's with probability at most the prover's charge plus `(width + layers (2 width + 1)) max 2 width / \|F\|`, and against `Q` queries at most `(Q + width + layers (2 width + 1)) max 2 width / \|F\|`, in a random oracle on all typed histories. The composed construction and projection check accepts the compiled GKR proof Entry, so its ideal interpretation is the transform of the admitted original, whose generated normal form reads as the plain verifier on well-formed statements within the Entry's maxima (width and layers at most four); the compiled verifier inherits both bounds for a fixed statement | `ZkcSecurity.Examples.GkrFiatShamir.soundness`, `ZkcSecurity.Examples.GkrFiatShamir.soundness_charged`, `ZkcExamples.Construction.GkrProof.compiled_transform`, `ZkcExamples.Structured.GkrSourceVerifier.verifier_reads`, `ZkcSecurity.Examples.CompiledGkrFiatShamir.soundness`, `ZkcSecurity.Examples.CompiledGkrFiatShamir.soundness_charged` | [Multi-round security](docs/spec/fiat-shamir-security.md#the-plain-gkr-verifier), [support](docs/support.md) |
| Multi-round Fiat–Shamir | Soundness over typed query sites: for any validator signature with a transcript interface whose sites decode the raw answer of their occurrence, possibly refusing, each oracle key is charged its site's error under the site's realized decoding law (exact, masking with refusal, KoalaBear low-bit masks, BLS12-381 reduction, proof-of-work-gated and compound sites). As instances, soundness of the transform of any validator from round-by-round soundness, `(Q + budget) * error` in a random oracle on all typed histories, also for adaptively chosen statements and decoded challenges; the imported Sumcheck verifier's transform at `(Q + n) / \|F\|`, with composition theorems whose only premise about a compiled verifier is its construction equality, discharged for the compiled Sumcheck proof Entry. Law records of realized decoding laws with five constructors and the gated accepted-value decoder; raw answers by the last event and the lifting of uniform-sort certificates; binding codecs over typed public-value binding events, which establish statement determination | `ZkcSecurity.FiatShamir.Typed.adaptive_soundness_charged`, `ZkcSecurity.FiatShamir.Typed.adaptive_soundness_weighted`, `ZkcSecurity.FiatShamir.adaptive_soundness`, `ZkcSecurity.Examples.SumcheckFiatShamir.compiled_adaptive_soundness` | [Multi-round security](docs/spec/fiat-shamir-security.md#typed-query-sites), [support](docs/support.md) |
| ArkLib certificate import | ArkLib's worst-case round-by-round soundness of a verifier with a guarded verdict becomes a typed certificate of its process form, each challenge round charged its own error, and transports to a participant validator that realizes the process form; a worst-case proof stated in ArkLib's framework, written for the example, bounds the compiled verifier of a guessing fixture Entry by `(Q + 1) / \|F\|`, attained at zero queries | `ZkcSecurity.FiatShamir.Upstream.worstCase_soundness`, `ZkcSecurity.FiatShamir.Upstream.worstCase_adaptive_soundness_weighted`, `ZkcSecurity.Examples.CompiledGuessFiatShamir.soundness` | [Imported certificates](docs/spec/fiat-shamir-security.md#imports-from-arklibs-round-by-round-soundness), [support](docs/support.md) |
| Hash-chain provider simulation | For the native hash-chain suites' byte-level chain model with the byte hash as a random oracle, the concrete experiment exceeds the history-oracle experiment by at most `(q + V)² / \|S\|` for `q` adversary and `V` verifier calls, so a typed certificate bounds acceptance of a false statement by `(q + queries) · bound + (q + V)² / \|S\|`; the byte framing is injective and prefix-free. The theorem is about the byte-level chain model; the link from the compiled transcript handlers and installed Keccak-256 kernels to that model is an obligation | `ZkcSecurity.HashChain.concrete_le_simulated`, `ZkcSecurity.HashChain.concrete_soundness`, `ZkcSecurity.HashChain.Encoding.frame_prefixFree` | [Provider simulations](docs/spec/fiat-shamir-security.md#provider-simulations), [support](docs/support.md) |
| Committed tables and openings | A verifier that sees roots and openings, read in one random oracle with its hash calls, accepts a statement false for its tables extracted at a transcript checkpoint with probability at most the typed certificate's charges plus one charge per hash call; Merkle trees with raw and with hashed leaves are extractable; the committed-opening experiment's intended bound holds for a total straight-line extractor | `ZkcSecurity.Commitment.soundness_weighted`, `ZkcSecurity.Commitment.soundness`, `ZkcSecurity.Examples.CommittedOpening.intendedBound`, `ZkcSecurity.Examples.CommittedOpeningBridge.soundness` | [Verifiers with committed tables](docs/spec/fiat-shamir-security.md#verifiers-with-committed-tables), [support](docs/support.md) |
| Construction obligations | Formal readings of the construction obligations, each refuted by a model counterexample; the type of provider simulations; typed requests on challenge occurrences and the data shape of interaction patterns | `ZkcSecurity.FiatShamir.Obligations.not_determines`, `TestsSecurity.Counterexamples.Operands.count_not_authenticated`, `TestsSecurity.Counterexamples.Openings.depth_not_fixed`, `TestsSecurity.Counterexamples.Couplings.chain_collision`, `TestsSecurity.Counterexamples.Laws.correlated_not_realized` | [Construction obligations](docs/spec/fiat-shamir-security.md#construction-obligations), [typed requests](docs/spec/fiat-shamir.md#typed-requests), [counterexamples](docs/support.md#construction-obligation-counterexamples) |
| FRI low-degree test | The library verifier at the ideal interpretation of its commitments accepts exactly when ArkLib's FRI query checks accept, and accepts the honest prover on every codeword; a round-by-round certificate with explicit errors per folding challenge and for the compound query draw bounds acceptance of a far committed word by every prover, unconditionally in the unique-decoding regime and, at low rates, up to the cube-root radius `1 - (ρ + η)^(1/3)` of ArkLib's generalized Johnson folding bound, inside the Johnson radius, and is also stated over the verifier's residual processes; through the typed-site engine, the Fiat–Shamir transform with one query-block key and commitments in the clear accepts a far initial word, chosen after the prover's queries, with probability at most the prover's charge plus every folding error and the block's error; with words committed by Merkle trees with one field element per hashed leaf, the same holds, plus a charge per hash call, for acceptance together with the initial word being far for its extraction at a verifier checkpoint, completed with zero where the extraction misses. The model is a transcription of the library verifier, not the compiled library | `ZkcSecurity.ArkLib.Fri.RoundByRound.soundness`, `ZkcSecurity.ArkLib.Fri.soundness_uniqueDecoding`, `ZkcSecurity.ArkLib.Fri.soundness_generalizedJohnson`, `ZkcSecurity.Examples.FriFiatShamir.fiatShamir_soundness` | [FRI security](docs/spec/fri-security.md), [support](docs/support.md) |
| Sigma compositions | Actual Schnorr AND and Chaum–Pedersen subjects; shared and independent witness contexts over the retained `DLog` relation; a generic shared-challenge composition theorem; VCVio completeness, special soundness and HVZK of both imported Σ-protocols, and fixed-statement Fiat–Shamir knowledge soundness of their transforms; the composed construction and projection check accepts both compiled proof Entries, whose ideal interpretations are the transforms of their original verifiers, and each compiled verifier has fixed-statement knowledge soundness in the random-oracle model as the registered knowledge endpoint applied to its subject's evidence | `ZkcSecurity.Examples.SchnorrAndSigma.knowledge_soundness`, `ZkcSecurity.Examples.ChaumPedersenSigma.knowledge_soundness`, `ZkcExamples.Construction.SchnorrAndProof.compiled_transform`, `ZkcExamples.Construction.ChaumPedersenProof.compiled_transform`, `ZkcSecurity.Examples.Subjects.SchnorrAnd.knowledge_soundness`, `ZkcSecurity.Examples.Subjects.ChaumPedersen.knowledge_soundness` | [Sigma compositions](docs/support.md#sigma-compositions), [participant projection](docs/spec/participant-projection.md#the-compiled-sigma-proof-entries) |
| Okamoto | Over the generated normal forms of the original-stage Okamoto unit: two accepting verifier runs with one commitment and distinct challenges give a representation of the point for which the retained target holds, and the actual verifier accepts the honest prover's messages; the composed construction and projection check accepts a compiled Okamoto proof Entry, whose ideal interpretation is the transform of its original verifier; that verifier has fixed-statement knowledge soundness of a representation in the random-oracle model, as the registered knowledge endpoint applied to the subject's evidence | `ZkcExamples.Structured.Okamoto.extract_representation`, `ZkcExamples.Structured.Okamoto.extracted_target`, `ZkcExamples.Structured.Okamoto.honest_accepts`, `ZkcExamples.Construction.OkamotoProof.compiled_transform`, `ZkcSecurity.Examples.Subjects.Okamoto.knowledge_soundness` | [Okamoto subject](docs/support.md#okamoto-representation-proof) |
| Participant normal forms | `normal_forms.py` generates each role's process, its equation against the admitted unit, its run and the binding of a contract clause from a short request, as ordinary Lean source the kernel checks. Each process equation is an instance of one soundness theorem of the verified participant normalizer, whose form the compiled normalizer prints and the kernel checks by evaluation; a definitional root equation is checked by `kernel_rfl` alone. For a body that applies other protocols, also inside a repeat callback, the callee's generated normal form stands at the application's child context, and each role's invocation at any caller context is stated; a repeat anywhere in a body binds its returned state, and a callback's repeat on an admitted count is the fold of the callback's normal form, by one generic law. Chaum–Pedersen, Schnorr AND, interactive Schnorr, Okamoto, the Sumcheck units and roots, the GKR layer Sumcheck and the GKR root use it | `ZkcExamples.Structured.ChaumPedersenNormalForms.verifier_process`, `ZkcExamples.Structured.OkamotoNormalForms.verifier_process`, `ZkcExamples.Structured.OkamotoNormalForms.exact_clause`, `ZkcExamples.Structured.SchnorrAndNormalForms.verifier_process`, `Zkc.Source.Structured.NormalForm.normalize_sound`, `Zkc.Source.Structured.NormalForm.callback_sound_uniform`, `ZkcExamples.Structured.SumcheckSourceNormalForms.verifier_invoke`, `ZkcExamples.Structured.GkrRoundsNormalForms.verifierRounds_invoke`, `ZkcExamples.Structured.GkrSourceNormalForms.verifierLayer_process`, `ZkcExamples.Structured.NormalFormSteps.repeat_embed`, `ZkcExamples.Structured.GkrSourceNormalForms.verifier_participant` | [Structured bridge](bridges/structured/README.md#generated-participant-normal-forms), [support](docs/support.md#source-only-sumcheck-verifier) |
| Logical contexts | Port-independent binders whose atoms transport along port maps; the existing contract layer is an instance; the Sumcheck residual bound holds on the retained and a port-repacked Reduction export | `Zkc.Source.Structured.Logical.PortMap.atom_holds`, `ZkcSecurity.Examples.CausalSumcheck.Iteration.repeat_uniform_residual_soundness` | [Logical contexts](docs/design/logical-contexts.md), [support](docs/support.md) |
| Multilinear Sumcheck | Table laws for any round count; ArkLib `n / \|F\|` complete and `k / \|F\|` residual bounds | `Zkc.Protocols.Sumcheck.Multilinear.check_of_residual`, `ZkcSecurity.ArkLib.Sumcheck.Multilinear.publicTable_soundness`, `ZkcSecurity.ArkLib.Sumcheck.Multilinear.residual_soundness` | [Mathematics](docs/spec/multilinear-sumcheck.md), [security](docs/spec/multilinear-sumcheck-security.md) |
| Imported Sumcheck and Reduce | Plain verifier and prover equations; the prover's per-round fold invariant; honest-prover completeness of both actual pairs for every challenge tape that supplies the rounds; `n / \|F\|` bounds on the actual admitted roots under the uniform query service | `ZkcExamples.Structured.SumcheckProverLaws.loop_honest`, `ZkcSecurity.Examples.CausalSumcheck.SourceVerifier.source_returned_true_bound`, `ZkcSecurity.Examples.CausalSumcheck.SourceVerifier.reduction_residual_bound` | [Verifier equations](docs/support.md#source-only-sumcheck-verifier), [honest prover](docs/support.md#honest-sumcheck-prover), [uniform queries](docs/spec/uniform-query-service.md#actual-imported-roots) |
| Authored DSL target | The imported Schnorr relation denotes discrete logarithm; two accepting transcripts yield a witness for it | `ZkcExamples.Structured.SchnorrBinding.target_special_soundness` | [Verification](docs/spec/verification.md) |
| Clean AIR | A flat AIR export preserves its constraints and selected specification | `ZkcClean.guarantees_of_export`, `ZkcClean.holds_iff`, `ZkcClean.table_spec` | [Clean integration](integrations/clean/README.md) |
<!-- END GENERATED what-is-proved -->

## Architecture

- `Zkc`: typed mathematics and role-local PIR semantics, a shared multi-result
  [structured carrier](docs/design/structured-computations.md), exact refinement,
  specification certificates, protocol contracts and finite security models;
  the checked compiler-stage rules: transcript construction and participant
  projection (`Zkc.Construction`), and executable lowering with normalization
  and completeness (`Zkc.Executable`).
- `ZkcExamples`: actual imported programs, equivalent source forms, composed
  residual/opening clients, effectful structured endpoint examples and a
  downstream custom property; the exported constructed validators of compiled
  proof Entries with their checks (`ZkcExamples.Construction`) and the
  executable validators the runtime admits (`ZkcExamples.Executable`).
- `ZkcTools`: executable scalar and structured references, header parser and
  declaration audit.
- [Security integration](integrations/arklib/README.md): optional ArkLib/VCVio
  consumers. The core does not import these libraries.
- [Clean integration](integrations/clean/README.md): isolated finite AIR export
  and native fixture producer; independent of protocol security consumers.

## Build and use

The [toolchain](lean-toolchain) and the three owning Lake manifests pin a coherent
Lean 4.34.1 dependency closure. See the [dependency rationale](docs/dependencies.md).
From `lean/`, `lake build` builds all maintained core libraries, examples, controls,
executables and declaration audits. The optional packages each use `lake build`
from their own directories. [Development](../docs/development/README.md) describes
Nix and the `just fetch-lean`, `just test-lean`, `just test-lean-integration`, and
`just test-lean-clean` entry points.

`just test-lean-native` additionally checks the native import and authored
specification boundary, including differential execution and negative controls.

### Verify an authored property

From the repository root, after preparing the native compiler and Lean packages:

```sh
python3 lean/bridges/common/verify.py \
  --module=example=examples/projects/schnorr/main.zkc \
  --module=schnorr=libraries/protocols/sigma/schnorr/lib.zkc --entry=example::Interactive \
  --compiler=build/compiler/zkc-compile \
  --spec=lean/bridges/common/requests/schnorr-dsl.json \
  --output=build/reports/lean/schnorr
```

A successful receipt says `verified-in-model`, records exact requested properties,
premises, source/request/certificate identities and dependency manifest identity.
An unsupported contract or an unproved correspondence remains `unresolved`.
The [verification specification](docs/spec/verification.md) explains author input,
proof generation, checked subjects and extension points.

### Reproduce from source

For an isolated build from exact dependency source checkouts, with no prior
project or dependency Lean objects:

```sh
cd lean
python3 reproduce.py --with-arklib --with-clean \
  --dependency-cache .lake/packages \
  --integration-dependency-cache integrations/arklib/.lake/packages \
  --integration-dependency-cache integrations/clean/.lake/packages \
  --output /tmp/zkc-formal-reproduction
```

Use a fresh output directory. The reproducer records source drift, toolchains,
builds, audits, standalone consumers and the Clean fixture comparison. Omit cache
arguments to fetch exact sources. The installed Lean/Std toolchain is trusted.

## Further reading

- Bridges: [common](bridges/common/README.md), [structured](bridges/structured/README.md),
  [transcript construction](bridges/construction/README.md),
  [executable](bridges/executable/README.md)
  and [participant comparison](bridges/structured/participant.md).
- [Dependencies](docs/dependencies.md) and the
  [design rationale](docs/design/protocol-verification.md).
