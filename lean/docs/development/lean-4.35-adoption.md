# Lean 4.35 adoption decisions

This describes the library and proof-authoring choices in the Lean 4.35 upgrade.
Dependency revisions are recorded in the owning manifests; the upstream Clean
patch remains content-hashed. CI ownership and canonical security meanings do
not change. Local validation receipts and measurements accompany the PR.

## Proof authoring

The [WP specification](../spec/weakest-preconditions.md) gives the exact
interpretations and adequacy boundaries. Charged rejection and pathwise cost
use local `Std.WP` instances over the existing process, with primitive,
component and bounded-loop specs. Raw Sumcheck root rejection, root cost and
two-root cost use `vcgen`. Honest completeness uses a separate concrete-run WP;
its pointwise shared-table theorem consumes the existing cached experiment
bridge and explicitly requires empty private-service interfaces.

This adopts the new tactic where it removes proof plumbing while retaining
mathematical component contracts. It does not replace every theorem mentioning
cost or rejection:

- `terminal_rejected`, `terminal_cost` and `both_rejected` describe finite pure
  checks. Their case splits directly expose acceptance and add no interaction
  calculus for a VC generator to simplify.
- Sumcheck round/loop soundness establishes the residual invariant and polynomial
  escape bound. These are the mathematical inputs to the WP, not consequences
  of control-flow verification. Existing proofs are installed through
  `derivation_spec`; loop-invariant specs support new proofs without reopening
  process recursion.
- Cost renaming, interface simulation, uniform/domain transport, and source
  correspondence are relational statements about two interpretations. Replacing
  them with a unary triple would require rebuilding the same transport proof.
- `derive_component_cost` infers an unknown compositional budget from installed
  component bounds before checking domination by the requested budget. `vcgen`
  propagates assertions for an already chosen interpretation and budget; it is
  not a replacement for that inference algorithm. This small checked-proof
  search remains, with its existing unsupported-component failure controls.
- Generated endpoints apply shared family contracts in one line. Those
  contracts now contain the relevant WP proof. Emitting the family's VCs anew
  for every source instance would duplicate mathematical obligations and
  increase authored code. Generators emitting cost synthesis retain the
  inference distinction above.

The opaque adaptive prover is not assigned an invented deterministic WP.
Its probabilistic sampling, query resources, cache extension and observation
couplings remain in VCVio-backed experiment theorems. A fixed-table completeness
proof does not establish zero knowledge, extraction, or adversarial soundness.

## Kernel and build choices

Remaining constructor-equality decision procedures in lowering plans and the
Clean result type use `decidable_of_iff`. Trivial disjoint constructors and the
dependent ArkLib message comparison retain their necessary case splits.

Array/Vector operations becoming kernel-reducible does not imply constant-time
kernel access: Array's logical representation still uses a list. A bounded
`Availability.inputEnvironment` comparison preserved reverse SSA order and
measured these kernel heartbeat counts:

| Inputs | Existing recursion | `Array.ofFn` |
|---|---:|---:|
| 32 | 727,722 | 735,779 |
| 128 | 10,556,843 | 10,587,949 |

The alternative showed no benefit, so representations remain unchanged. An
explicit `toList` equality transport reduced the same synthetic whole-array
comparison to 181,300 and 2,258,479 heartbeats. Availability does not compare
whole environments, so this is not evidence to change its current algorithm or
claim a GKR speedup. Dependent `Values` also encodes typing and refusal behavior;
a container rewrite needs a real workload improvement and preserved semantics.

Repeated GKR admission and certificate measurements distinguish kernel checking,
tactic execution, imports and wall time. The GKR workload is kernel-dominated;
precompiling its small tactic does not accelerate kernel evaluation of the
certificate. `precompileLibrary` requests native objects for the whole owning
library and shared libraries for transitive imports. With current library
ownership this expands to hundreds of owned modules and potentially Mathlib's
large closure; merely moving a tactic file does not remove its imports. Without
measured tactic dominance, this additional build scope is not adopted.

Two repetitions of identical driver sources gave the following bounded
measurements. Times are seconds; `not reported` is not a measured zero.

| Workload | Lean | Wall range | Kernel range | Tactic range | Import range |
|---|---|---:|---:|---:|---:|
| GKR admission | 4.34 | 144.71–151.20 | 106–110 | 0.0281–0.0290 | 0.889–0.893 |
| GKR admission | 4.35 | 127.56–160.08 | 98.4–121 | 0.0284–0.0286 | 0.662–0.676 |
| Construction certificates | 4.34 | 12.64–13.19 | 3.74–3.82 | 0.0048–0.0051 | 6.21–6.24 |
| Construction certificates | 4.35 | 7.33–9.98 | 4.48–5.86 | 0.0041–0.0057 | 1.49–2.54 |
| Slot certificates | 4.34 | 2.27–2.32 | not reported | not reported | 1.36–1.39 |
| Slot certificates | 4.35 | 2.82–4.07 | not reported | not reported | 1.65–2.25 |

These are shared-host observations, with concurrent work and differing cache
warmth, not a controlled performance comparison. Dependency versions and
underlying proof bodies change with the upgrade; driver hashes match. Profiler
categories can overlap. Initial runs missing generated dependencies are retained
in the PR evidence but excluded from the table. The evidence supports the
kernel-versus-tactic decision, not a throughput improvement or regression claim.

## Exact upstream reuse

The upgrade uses current VCVio, ArkLib, CompPoly, PolyFun and Mathlib directly.
Additional exact matches replace the local query-simulation composition,
uniform-sample equivalence, list drop-last law and unused `ofFn` injectivity
wrapper. The previous upgrade's six replacements and `Nat.powMod` remain.

The local until-bad relation preserves heterogeneous states and a bad-event
escape; the inspected upstream alternatives have different hypotheses or
observations. Deferred sampling preserves an indexed remaining-query invariant
and stochastic filling. Memoization preserves final cache, chronological first
occurrences and cache/log agreement. Table-log costs allow arbitrary ordered
additive cost carriers, whereas ArkLib's matching-name results specialize to
natural-number costs. These stronger or different contracts remain local.

Upstream KZG results require identifying a source/provider with its polynomial
encoding, SRS, scheme, pairing and experiment, plus the stated hardness
assumptions. There is no existing zkc KZG realization whose local proof they
replace. Fischlin uses repeated challenge search, a threshold and an online
extractor; it proves a different transformation from the current Fiat–Shamir
endpoints. Its almost-completeness theorem cannot prove perfect completeness.
Importing these theorems without their missing correspondences would strengthen
no current claim. These are semantic reasons, not version-compatibility excuses.

## Checking and warnings

[Independent checking](independent-checking.md) exports all 88 locked statements
and their dependencies across four packages. Explicit baseline and candidate
artifacts feed `lake comparator` and `lake check --paranoid`; partial runs and
resource failures cannot acquire a full verdict. The process checks preserve
sandboxing and standard-axiom policy, with controls for corrupted proofs,
changed statements and changed referenced definitions.

Production warning suppressions are removed at their generators as well as in
outputs. Unused generated parameters retain their positions and types with
appropriate unused names; proof aliases use theorem declarations; synthetic
nested callback names avoid duplicate namespaces. Unneeded simp arguments and
fallback tactic branches are removed. Remaining test exceptions explain the
negative or state-restoration behavior they exercise. `warningAsError` stays on.
