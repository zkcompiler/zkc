# Supported claims

All results below concern stated mathematical models and exact selected imports.
They do not certify arbitrary DSL programs or the full native lowering pipeline.

| Surface | Maintained claim | Explicit boundary |
|---|---|---|
| Core execution | Typed mathematical/role-local programs; exact process refinement; shared-state sequential composition; machine prefix/resumption and finite-process completion | General native loops and external waiting are not imported by the scalar profile |
| Structured source | Multi-result closed callbacks and lexical binding; strict formation in both directions; scalar/mathematical/participant/import bridges; contextual equality, totality and compatible effect translation | Shared structural carrier; native transformation correctness requires separate correspondence |
| Structured native import | Whole-unit original schema, separate protocol roots and kinded named helpers; explicit scalar/group interpretation, owner-only Local calls, shared participant effects, computational availability and service admission | No general availability soundness, eager/demand correspondence, affine resources, native correctness or relation/formula binding theorem |
| Optional component semantics | Same typed Region with closed callbacks; generic lookup, optional named Math calls, all-present adequacy, exact resolution and full-table framing; shared scalar/group evaluator | Static availability is a separate computational check; adequacy alone proves neither admission nor native correspondence |
| Retained protocol applications | Exact original/checked association in both directions; complete-signature linking, contextual prefix/full-table laws, optional call masks, outside-roster skip and effect interpretation | Supported static native profile; no repeat, generic availability/preflight soundness or native execution correspondence |
| Retained preparations | Exact retained realization/map declarations, whole-unit transitive profile admission, full-ABI realization totality, ordered row/broadcast maps and stopped-prefix laws | Logical model; helper-value formulas require equations for the actual checked table; native resource limits remain separate |
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
for exact scope and theorem owners. Retained maps and realizations use that same admission and semantic carrier.
Retained protocol application has the separate contract below. Repetition,
conditional completion and construction-start remain outside admission;
this profile does not admit the full Sumcheck protocol.

The executable reference propagates generated index/vector bounds through the
checked source before running the existing evaluator. Separate analysis and
logical-work budgets, conservative branch/loop joins and typed reply envelopes
can refuse cheap concrete runs. In particular, a valid source equation does not
imply CLI preflight success. These controls do not prove abstract-transfer
soundness, exact host costs or agreement with native capacity thresholds.

## Retained map and realization contracts

Retained realizations derive an invocation and positional return from the original
helper reference. Their checked region-free Math closure has a semantic totality
proof over the complete ABI, including vector projections, empty results and
multiple results. The imported-unit theorem requires checked-definition membership
and exact equality to the retained declaration's derived raw body. It has no
caller-supplied execution or callee-totality premise. Ordinary Math definitions
retain their broader existing profile.

Retained maps derive one typed `Op.map` and a positional return. Their root helper
returns one field value; every operation in the complete transitive Math closure,
including unused operations and callees, satisfies the scalar-ring profile.
`MapLaws` checks all row shapes in source order before invoking any row, retains
scalar broadcast positions, and preserves helper effects and stopped prefixes.
Empty rows return an empty vector without invoking the helper. Direct optional
maps require all arguments; Local wrappers retain their existing strict boundary,
and Math projections retain per-result optionality.

The complete retained First and Prefix source subjects use their own checked
helper tables and explicit singleton closed projections. First validates the
table, splits contiguous halves, maps interpolation, subtracts the dimension and
returns the ordered values/dimension/width triple. Prefix composes those steps in
point order, including an empty point and rejection of too many coordinates.
Their arbitrary-width shape results and one-column most-significant-bit-first
restriction results use the independent list restriction mathematics.
Independent two-role Combination and ConstantRows
subjects cover interleaved broadcasts, the formula `s*a-t*b+3`, unused row shapes,
owner/nonowner behavior and missing unused inputs. RealizeValues proves the
actual vector projection through its retained realization. Each source equation
uses exact retained-body views and discharges helper equations through the full
checked table. These are model-level source contracts, not native execution,
protocol security or a full Sumcheck source theorem.

The executable map bounds reserve all row-shape work and repeated actual helper
work without changing existing budgets. Empty-row pruning follows the complete
shape check. This is a logical workload bound, not exact CPU accounting:
concrete positional list lookup depth is not charged as processor steps. General
transfer soundness and native resource correspondence remain separate obligations.

## Retained protocol application contracts

A complete six-field signature includes the ordered roster, input/output types
and input/output scopes. Exact source association exposes both the original
function and its actual checked lowering; a shared name or signature does not
establish body identity. Dependency ordering permutes complete checked values.
From an actual admitted raw application, inversion laws recover its original
instruction, resolved finite role substitution and statement-free callee check.
Service operands retain their lexical formal-input index, nominal contract and
mapped singleton declared owner independently of equal runtime handles.
Protocol closures capture the strict earlier prefix and use the existing
Math/Local helper tables, the one typed Region carrier and PIR process semantics.

Generic laws preserve the selected root participant coordinate through nested
role substitutions and qualify sites using the complete rendered parent and its
UTF-8 byte length. Calls mask optional inputs and results, skip outsiders even
with zero outputs, and preserve reached actions and stops. Optional Math
projections and strict owned Local input sequencing keep their separate contracts.
Helper internal marks remain raw. Site erasure removes internal observations,
while qualified send, receive and query labels remain observable.

The complete unchanged Application, ServiceOrder and nested-wrapper snapshots
have explicit checked candidates and named kernel admission proofs. Application
proves both participant equations with independent optional inputs and the exact
observed mark sequence. ServiceOrder proves the ordered process for each role;
handler equations cover aliased and distinct service handles, independently
received values, false guards, consumed provider stops and unconsumed mismatches.
The wrapper preserves the full rendered parent at nested sites. These proofs
use literal full-signature body views of the admitted source. Source digests and
finite native comparisons remain separate byte/execution evidence.

Whole-unit native-summary and effective-site checks operate in original source
order. They enforce existing native all-root constraints, including dormant
protocols and reachable pure helper calls; this closes a prior independent-reader
parity gap even in units with no application. These computational checks do not
prove native traversal correspondence or abstract-preflight soundness. The CLI
maintains separate analysis, logical-work, typed-reply and observer capacities.
The effective-site collision check uses the standard ordered string set with an
exposed ordinary string comparator, allowing concrete source admission proofs
across module boundaries. Its empty/insert membership laws preserve the earlier
duplicate criterion. The visit
cap remains a logical bound, not a CPU-time guarantee.

A flat selected body keeps its closed projection despite valid dormant
applications. A reachable application refuses that narrower Lean view. Native
one-role closed execution supports more; paired application comparisons use
open execution. General availability, eager/demand agreement, native execution,
provider randomness and security remain separate obligations.
