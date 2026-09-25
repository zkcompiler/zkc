# ArkLib integration

This optional Lake package connects actual ArkLib protocol/reduction types and
VCVio/PolyFun computations to the maintained zkc library. Main `formal/` has no
external protocol-library dependency. The package uses a local path dependency
on main and compatible exact Lean/Mathlib pins.

The [integration maintenance guide](../../../docs/development/extensions.md)
separates formal correspondence from native execution adapters and identifies
pin ownership. Native dependency versions do not select ArkLib sources or
supply theorem hypotheses.

```sh
cd formal/integrations/arklib
lake build
```

Use narrow `ZkcArkLib.*` imports. There is no universal security adapter or
blanket certification of ArkLib. [TestsArkLib.Audit](TestsArkLib/Audit.lean)
audits all owned integration and test declarations. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted in their transitive proof cones.

## Claims and their premises

| API and checked declaration | Actual claim | Supplied premises and limit |
|---|---|---|
| [Sumcheck.Scalar](ZkcArkLib/Sumcheck/Scalar.lean): `source_acceptance`, `checked_verifier`, `checked_reduction` | Typed scalar schedule in actual `ProtocolSpec`; checked evaluator replacement gives verifier and reduction equality | `hornerCheck = true`, interpreted commutative ring; arbitrary supplied ArkLib prover, witnesses and shared-oracle interface. This is the indexed product-family schedule, not ArkLib's polynomial-oracle Sumcheck protocol |
| Same module: `checked_soundness` | Equivalence of actual `Verifier.soundness` propositions after replacement | Language, initialization, oracle interpreter and error remain fixed; source soundness is not manufactured by this transport |
| [OneRound.Prover](ZkcArkLib/Sumcheck/OneRound/Prover.lean): `actual_eq`; [Security](ZkcArkLib/Sumcheck/OneRound/Security.lean): `actual_bound`, `experiment_bound` | The actual reduction runs the pre-challenge coefficient choice and fresh challenge; false-claim acceptance is at most `2/card D` | Field, injective challenge embedding, finite sampleable domain, false claim `s ≠ 2`; arbitrary private state/coins sampled before the draw. The fixed one-variable family has Boolean sum 2 |
| [OneRound.Kernel](ZkcArkLib/Sumcheck/OneRound/Kernel.lean): `kernel_transport`, `experiment_bound`, `adaptive_claim_bound` | Same actual reduction under a supplied state-dependent sampler; bound `2*ε` | Conditional point-mass cap at every reachable pre-draw state, injective embedding and false claim there. Uniform marginals alone do not supply the cap |
| [LocalProver.Source](ZkcArkLib/LocalProver/Source.lean), [Admission](ZkcArkLib/LocalProver/Admission.lean), [Observation](ZkcArkLib/LocalProver/Observation.lean) | Actual finite local program, common execution, no missing-input fallback, complete local cut and conditional challenge observation | Checked formation/inputs; positive-mass commit for conditioning. Abort remains an outcome and does not consume a challenge |
| [LocalProver.Provider](ZkcArkLib/LocalProver/Provider.lean): `source_consumer_exact`, `source_acceptance_bound`, `initialized_acceptance_bound` | Guarded source/provider execution feeds the reduction at a committed boundary; the consumer equality projects to verifier outcomes | Product initialization and point cap, false claims at reached requesting commits, finite resource budget. Local source cannot inspect provider-private state |
| [CapturedPrograms](ZkcArkLib/CapturedPrograms/Installation.lean): `initialized_experiment_bound` | Checked installation and issuance feed the local-prover boundary-sampler experiment, including refusal | Actual capacity/selection/input premises; supplied point cap and false claim at reachable commits. This experiment runs the local-prover component, not the paired service or persistent-provider consumer; five captures belong to this application |
| [PolyFun.Blocks](ZkcArkLib/PolyFun/Blocks.lean): `execute_agrees`; [Reads](ZkcArkLib/PolyFun/Reads.lean): `two_semantics`, `two_erasure` | Actual `FreeM` interpretation matches block execution and dependent sequential reads | Supplied handlers/hash/supplier; complete result, state, offset and events, including failure. This does not extract native code |
| [Sumcheck.Bytecode](ZkcArkLib/Sumcheck/Bytecode.lean): `source_consumer`, `integrated_consumer`; [BytecodeProbability](ZkcArkLib/Sumcheck/BytecodeProbability.lean): `induced_consumer`, `acceptance_mass` | Actual represented bytecode/verifier projection and its source-induced acceptance distribution | Canonical claim and three-word payload with no trailing bytes; actual selected source reference. The transcript law is induced from the same input/hash experiment, not assumed equal to independent uniform challenges |
| [OneRound.Native](ZkcArkLib/Sumcheck/OneRound/Native.lean): `native_source_verifier`, `native_parameters` | Deterministic modeled-byte challenge correspondence and exact support mismatch | Hash range is `2^61`, modulus is `2^61 + 3297`; no full-residue uniformity, primality, entropy or native security follows |

[Stopping](ZkcArkLib/Sumcheck/Stopping.lean) and
[bytecode stopping controls](TestsArkLib/BytecodeStopping.lean) retain two
important separators: deferred verification can consume a challenge after an
early verifier would reject, and oracle exhaustion differs from verifier
rejection. Equality of acceptance verdicts alone cannot transport resource state.

The main library's general finite interactive Sumcheck theorem is separate:
`Zkc.Protocols.Sumcheck.Security` covers any dimension and a fixed polynomial of
per-coordinate degree at most two, with bound `2*n/card F`. Its proof uses
Mathlib's polynomial root bound and does not rely on an admitted ArkLib knowledge
proof. This integration does not identify those two protocols without a theorem.

## Exact external status

The [manifest](lake-manifest.json) pins ArkLib
`3f3f045dd295834c262bd6f0d9dfdfee07cc8e76`, VCVio
`7607103730459b127e2218fb36f5f13c2d65c038`, and PolyFun
`bb7e1003544b8461e3d484fc51c61b2ff865250f`.

[UpstreamStatus](TestsArkLib/UpstreamStatus.lean) checks these selected theorem
cones at build time. It is a status test, not a zkc cryptographic adapter:

| Selected declaration | Pinned status | Adoption requirement |
|---|---|---|
| `FiatShamir.euf_cma_to_nma`, `euf_nma_bound`, `euf_cma_bound` | Standard axioms only | Matching Sigma signature experiment, special soundness, HVZK/predictability and query premises; these results concern signature unforgeability |
| `fiatShamir_completeness` | Contains `sorryAx` | Prove the needed scoped instance or wait for a reviewed upstream proof; no closed instantiation is claimed |
| `FiatShamirWithAbort.euf_cma_bound`, `euf_cma_bound_perfectHVZK` | Contains `sorryAx`; source warns about the signed-error statement | Repair the theorem's statement and probability premises before using it |

Owned library theorems do not depend on these incomplete declarations. Status
changes fail the test and trigger a proposition, axiom-cone and consumer review.
A proof parameter may express a missing law, but without a supplier it yields
only a conditional theorem. Native contract trust, cryptographic assumptions,
missing mathematical proofs and undischarged hypotheses remain distinct.

The [research agenda](../../design/research-agenda.md#3-external-libraries-and-theorem-boundaries)
tracks general FS/duplex and knowledge questions. General results belong upstream
where useful; zkc remains responsible for its source, encoding, query, observer
and failure correspondence. Updating an upstream pin cannot prove those adapters.
