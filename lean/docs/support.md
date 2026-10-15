# Supported claims

All results below concern stated mathematical models and exact selected imports.
They do not certify arbitrary DSL programs or the full native lowering pipeline.

| Surface | Maintained claim | Explicit boundary |
|---|---|---|
| Core execution | Typed mathematical/role-local programs; exact process refinement; shared-state sequential composition; machine prefix/resumption and finite-process completion | General native loops and external waiting are not imported by the scalar profile |
| Structured source | Multi-result closed callbacks and lexical binding; strict formation in both directions; scalar/mathematical/participant/import bridges; contextual equality, totality and compatible effect translation | Shared structural carrier; native transformation correctness requires separate correspondence |
| Structured native import | Whole-unit original schema, separate protocol roots and kinded named helpers; explicit scalar/group interpretation, owner-only Local calls, shared participant effects, computational availability and service admission | No general availability soundness, eager/demand correspondence, affine resources, native correctness or relation/formula binding theorem |
| Optional component semantics | Same typed Region with closed callbacks; generic lookup, optional named Math calls, all-present adequacy, exact resolution and full-table framing; shared scalar/group evaluator | Static availability is a separate computational check; adequacy alone proves neither admission nor native correspondence |
| Structured helper inlining | Generic invocation/body binding law preserving complete processes and suffixes; exact original/prepared model equality for Schnorr-response and multilinear-claim scalar Entries; admitted arithmetic mutation counterexample | Explicit lookup/body equation and exact retained subjects; no general native pass correctness or interactive protocol security |
| Ordered finite semantics | Admission-preserving effectful folds, product/zip laws and conditional pure replacement | Evaluated mathematical domains; native capacity, failure diagnostics and domain lowering require their own correspondence |
| Scalar import | Checked admission and source-specific open-process correspondence for actual exports | Native exporter, interface resolver and constructor rendering are reviewed/tested, not universally proved |
| Schnorr | Imported verifier completeness, two-transcript special soundness and custom invalid-equation rejection | Algebraic group/module interpretation; no discrete-log hardness reduction or whole native prover proof |
| Structured Schnorr | Actual Interactive, Helpers and Reordered source contracts over arbitrary scalar/group values; exact prover process for Interactive; EarlyChallenge contract refutation | Named helpers and dormant formula retained; no inferred relation binding, native BLS/RNG correspondence or availability soundness theorem |
| VCVio Schnorr | Equality for every event on commitment, fixed honest challenge, response and actual verifier outcome under uniform nonce/response sampling | Handwritten honest-prover strategy with the imported verifier outcome; no compiled-prover correspondence, malicious-verifier, concurrent or Fiat–Shamir theorem |
| ArkLib Sumcheck | Actual imported two-round degree-two verifier acceptance on a false public sum claim is at most `4 / |F|` | Finite field; reached fresh uniform queries; causal coefficient-message strategies, including arbitrary private probabilistic mixtures chosen before verifier draws |
| [Multilinear Sumcheck mathematics](spec/multilinear-sumcheck.md) | Arbitrary-length ordered prefix restriction and suffix marginalization, endpoint-message laws, explicit delivery agreements, residual truth and complete public-table discharge, including zero rounds | Independent scalar-table model over rings; core has no optional security dependencies |
| [Multilinear interactive security](spec/multilinear-sumcheck-security.md) | Complete `n / |F|` and partial residual `k / |F|` bounds, degree-one endpoint/table transport, checked public-table observation, and honest completeness | Fixed verifier table/false initial sum; finite field and fresh uniform challenges; arbitrary causal effectful ArkLib strategies; exact original or derived marginal oracle; no PIR/source/native correspondence |
| Public factor openings | Imported composed verifier bound `4 / |F|`; generic conditional bound `4 / |F| + epsilon` | Public polynomial factor checks prove zero opening error; PCS binding/extractability needs a separate opening theorem |
| Authored DSL target | Imported Schnorr relation denotes discrete-log; two accepting imported verifier transcripts yield a witness accepted by that relation | Bounded scalar formula adapter and tested interface selector binding |
| Clean | Admitted lookup/channel-free flat AIR export preserves constraints and selected source specification; native control fixture retained | Finite rows/field/ring interpretation; native agreement is differential, not decoder correctness |

Scalar source forms include original, helper-based, reordered and Horner implementations.
The scalar exporter currently inlines helpers before Lean import. Structured
helper proofs retain the definitions and invoke checked prefix-linking laws.
The factor-opening case combines Sumcheck residuals with two subsequent adaptive
openings. Negative controls include early challenges, wrong residuals/points,
stale bindings, correlated-coin requests, invalid dormant definitions, false
relation bodies, wrong subjects and forbidden axioms.

The optional security package invokes ArkLib's
`Sumcheck.Interaction.Native.execute_soundness`. Its adapter constructs degree-
bounded messages and the public polynomial oracle, proves all evaluation/domain
laws and equality of accepted-event computations. The quadratic adapter connects
an imported scalar verifier; the arbitrary-round multilinear adapter connects
independent table contracts and ArkLib's causal interaction, with source and
native correspondence still separate. VCVio's uniform-event transport proves
Schnorr's simulator law.
Some unrelated upstream declarations contain `sorry`; the transitive axioms of
owned claimed results are audited separately and must use only Lean's standard
three axioms. A build of all upstream sources is not asserted.

For precise APIs read the theorem statements in `Zkc`, `ZkcExamples`, and
`integrations/arklib/ZkcSecurity`; [architecture](architecture.md) explains their
roles. [Bridge commands](../bridges/common/README.md) reproduce finite checks.
The scalar bridge's Z/97 comparisons do not establish BLS12-381 arithmetic.
The [structured bridge](../bridges/structured/README.md) separately compares
full-size BLS12-381 scalar values with direct SSA execution and selected production
Runner cases. Those finite comparisons do not establish native executable
soundness, randomness or transcript encoding.
