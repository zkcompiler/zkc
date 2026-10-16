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
| Structured Schnorr | Actual Interactive, Helpers and Reordered verifier contracts over arbitrary scalar/group values; Interactive prover observations supply a causal Strategy, exact stopped prefixes and completeness under equal bases, the verifier-key witness relation and honest delivery; EarlyChallenge contract refutation | Unconstrained unused prover key; successful fixed nonce/challenge replies and send acknowledgements; partial ordered extraction; shared extraction constructor alone asserts no causality; no native execution, joint scheduler, relation binding or availability soundness theorem |
| VCVio Schnorr | Equality for every public-view event under fixed challenge and uniform nonce/response sampling; Interactive source-derived messages and actual verifier outcome transfer to the existing simulator | Generic and earlier consumers retain the handwritten strategy; new Interactive consumer derives it from checked source sends. No native prover/RNG correspondence, malicious-verifier, concurrent or Fiat–Shamir theorem |
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

## Structured primitive contracts

The structured model independently admits all retained binding metadata,
including unused rows, and resolves exact fifteen-operation ABIs. General
`PrimitiveLaws` state conditional u64 arithmetic equations, overflow/underflow
and zero-divisor refusal, list length exhaustion, sum, ordered split/append and
equality. `Evaluation.exec_missing` and `exec_stopping_prefix` retain strict
operand sequencing and continuation stops. `Finite.fold_range_state` supplies
an indexed invariant for counted loops without imposing unreachable callback
premises. General helper framing, effect interpretation, all-present adequacy,
inlining and closed projection remain applicable to the extended vocabulary.
These are logical equations, independent of native allocation, runtime resource
cost, source translation correctness and security. Actual source client coverage
is recorded separately from these generic laws.

Five complete fresh original subjects are kernel-admitted: unchanged library
Shape/Table/Halves wrappers, an independent eight-result arithmetic/vector caller
and a two-role pure-index caller. Full-table equations discharge every helper
premise through exact admitted body views. Successful table/halves contracts
preserve ordered values and prove the two halves' shapes and reconstruction;
source short-circuit laws use silent observations. A separate Sequence theorem
proves the observed refusal prefix for arbitrary vectors with representable
length plus one; no observed Shape/Table/Halves site law is claimed.
The library equations state representation premises explicitly; the independent
Sequence equation covers all logical inputs. See the
[source contract](spec/structured-source.md#actual-library-primitive-subjects)
for exact scope and theorem owners. Full Sumcheck's maps, realization, protocol
application and repetition remain outside this admission profile.

The executable reference propagates generated index/vector bounds through the
checked source before running the existing evaluator. Separate analysis and
logical-work budgets, conservative branch/loop joins and typed reply envelopes
can refuse cheap concrete runs. In particular, a valid source equation does not
imply CLI preflight success. These controls do not prove abstract-transfer
soundness, exact host costs or agreement with native capacity thresholds.
