# ZK-Protocol Expressibility Validation Portfolio

> **Kind:** Temporary R2 protocol-selection and validation-depth contract
> **State:** Selected portfolio; repaired/refrozen `P01` is retained at T3
> after exact-snapshot independent re-review; `P02` native FRI/IOR is retained
> at T3 as a two-lane `ConservativeExtension` result
> **Authority:** None. This page selects research pressure and evidence depth;
> it does not define target semantics, supported protocols, theorem
> applicability, implementation conformance, or the final v0 boundary.
> **Current baseline:** The repaired `FRI-Grind-1` finite witness is closed. It
> is prior evidence, not a native FRI/IOR inhabitant and not a general
> expressibility result.
> **Downstream boundary:** R3 model redesign and R4 selection consume these
> results. Stage 4B remains inactive.
> **Disposition:** Absorb the final support boundary, selected abstractions,
> rationale, and retained evidence into durable owners, then delete this page.

## 1. Decision and purpose

Before selecting the v0 protocol model, R2 will test whether it can describe a
structurally diverse portfolio of ZK protocols and proof-system components.
The portfolio pairs canonical families with recent variants that change
protocol shape rather than merely constants.

The objective is not to claim a universal protocol language. It is to learn:

1. which families inhabit the candidate model without semantic loss;
2. which require a conservative, owner-local extension;
3. which expose a missing cross-domain abstraction;
4. which require a fundamental change to Core, authority, identity, execution,
   Relations, composition, or Analysis; and
5. which capabilities should remain explicit v0 extension boundaries.

Protocol count is not evidence of generality. A single opaque callback,
uninterpreted term, or implementation escape hatch can make any language look
expressive while making admission, identity, composition, and independent
checking meaningless.

## 2. What counts as theoretical validation

Every studied case must reconstruct the protocol from a primary source and
account for the applicable items below:

- statement, witness, public parameters, setup material, and their owners;
- actor roles, visibility, strategy state, causality, and non-anticipation;
- ordered phases, messages, challenges, checks, aborts, rejections, and
  successful or residual termination;
- Fresh, Fiat--Shamir, external, setup-derived, or shared randomness;
- direct messages, committed objects, logical oracles, queries, openings, and
  authenticated evidence;
- field, extension-field, group, ring, module, polynomial, code, and domain
  assumptions without hiding them in a universal value kind;
- relation/statement grounding and any directional, lossy, or range-checked
  bridge;
- subprotocol calls, interleaving, shared challenges, reductions,
  accumulation, folding, and recursion;
- semantic identities versus validation, source, realization, and replay
  identities;
- admission, execution, correspondence, theorem applicability, quantitative
  Analysis, and implementation conformance as separate judgments; and
- exact omissions, abstraction loss, residual trust, and non-claims.

An encoding passes only if the source protocol can be reconstructed without
moving semantic authority into an evaluator, codec, backend, report, or opaque
extension. The work validates the representation of a protocol and its
obligations; it does not reproduce or certify the paper's proofs.

## 3. Differentiated validation strength

The portfolio deliberately uses different depths.

| Level | Required evidence | What it can establish |
|---|---|---|
| `T1 Boundary analysis` | Source-grounded anatomy, current-model mapping, exact variant delta, required owners, obstructions, and non-claims | Whether the case reveals a credible semantic boundary or missing capability |
| `T2 Constructive encoding` | All T1 evidence plus a complete typed abstract trace/object graph, identities, grounding, constructions, composition, failures, resources, and representative negative mutations | Whether a paper-faithful instance can inhabit the candidate model without opaque escape or authority duplication |
| `T3 Executable falsification` | All T2 evidence plus frozen finite inputs, executable admission/execution or checking, named positive and negative cases, bounded resources, exact identities, and non-authoring replay | Whether one finite inhabitant and its rejection boundaries are reproducible |

`Holdout` is an orthogonal tag, not a fourth depth. A holdout is not used to
redesign the candidate before semantic freeze. A cold reader then attempts its
assigned T1 or T2 validation against the frozen model. A holdout-discovered
defect may reopen the model, but the failed frozen attempt remains evidence.

### Promotion rule

A case moves to a stronger level only when its unresolved pressure can change a
shared semantic decision. Promote T1 to T2 when prose mapping leaves ownership,
ordering, identity, or composition ambiguous. Promote T2 to T3 when competing
models appear equally expressive, a claimed rejection boundary needs actual
execution, or a local workaround may be self-fulfilling. Do not promote only
because a protocol is prominent.

### Classification vocabulary

Each completed case receives exactly one primary classification:

- `Native`: the current model expresses the protocol without semantic change;
- `ProfileOrModule`: an owner-local profile or module suffices;
- `ConservativeExtension`: a new typed primitive is needed but existing
  subjects and meanings remain valid;
- `ModelingWorkaround`: representation is possible only through an undesirable
  encoding that must not count as support;
- `SemanticLoss`: an essential source distinction cannot be recovered;
- `FundamentalObstruction`: Core, authority, identity, lifecycle, or a shared
  boundary must change;
- `IntentionalBoundary`: the capability is deliberately outside v0; or
- `Undetermined`: the assigned depth did not resolve the question.

## 4. Portfolio

### 4.1 Deep executable anchors

| ID | Case | Level | Principal pressure |
|---|---|---:|---|
| `P01` | Minimal Schnorr/Sigma identification, Fresh and Fiat--Shamir forms | T3 | Statement binding, prover strategy, response-after-challenge causality, Fresh/FS factorization, special-soundness and HVZK applicability boundaries |
| `P02` | Native FRI/IOR through query and authenticated opening | T3 | Logical oracle ownership, commitment/opening compilation, draw multiplicity, authentication, residual versus acceptance, BCS/salting boundaries |

`P01` is a retained T3 result at its exact finite scope. Its repaired 69-test
packet passed separate lifecycle and provenance cold rechecks on the final
source-bound identity. `P02` is retained through one combined packet with two
distinct lanes: an early-terminated finite profile with the full historical
replay packet and an exact three-fold/scalar-terminal classical control with
frozen public replay. The exact lane closes fixed-coin deterministic verifier-
shape correspondence to the cited Algorithm 1, not the randomized source
Protocol or any theorem. The case-level primary classification is
`ConservativeExtension`; family closure, BCS, property Analysis, and the outer
relation remain open. It does not reuse the fixture-local invented acceptance
condition withdrawn by `FRI-Grind-1`. The
[final retention record](native-fri-ior-final-classification-and-retention.md)
owns the precise gate and reopening boundary.

### 4.2 Constructive canonical families

| ID | Case | Level | Principal pressure |
|---|---|---:|---|
| `P03` | Classical Sumcheck | T2 | Round-local derived claims, polynomial messages, verifier coins, final evaluation, and reduction residuals |
| `P04` | GKR-style layered reduction | T2 | Nested Sumcheck use, layer-to-layer claim transformation, verifier state, and subprotocol composition |
| `P05` | KZG single and batched polynomial openings | T2 | SRS/setup authority, group-valued commitments, evaluation claims, batching challenge, and pairing checks |
| `P06` | PLONK with permutation and one lookup argument | T2 | Multi-phase challenges, argument composition, tables, quotient/evaluation claims, PCS boundary, and proof packaging |
| `P07` | Groth16/QAP preprocessing SNARK | T2 | Noninteractive-by-construction protocol, structured setup, CRS specialization, group proof elements, and pairing verification without an online public-coin core |
| `P08` | Bulletproofs inner-product/range-proof path | T2 | Logarithmic recursive interaction, vector commitments, aggregation, Fiat--Shamir, and relation-specific proof composition |
| `P09` | Nova, HyperNova, and ProtoStar folding comparison | T2 | Evolving instances and accumulators, step relations, multi-folding, special-sound protocol accumulation, recursion, and separate ZK wrapping/blinding |
| `P10` | Imported verifier and recursive proof verification | T2 | Proof-as-relation-input, bounded descent, nested context/transcript identity, imported semantics, and cycle avoidance |

Sumcheck, GKR, FRI, polynomial commitments, folding schemes, and accumulation
schemes are not automatically zero-knowledge protocols in isolation. Each case
must state whether it is an interactive proof, argument, IOP/IOPP, PCS,
compiler, folding/accumulation primitive, or complete ZK system, and must not
inherit properties from the system that embeds it.

### 4.3 Recent design-set variants

These variants may influence redesign before freeze.

| ID | Variant | Level | Why it is not redundant |
|---|---|---:|---|
| `V01` | [A Fiat--Shamir Transformation From Duplex Sponges](https://eprint.iacr.org/2025/536) | T2 | Replaces a simple prefix-hash view with a stateful absorb/squeeze construction, explicit codecs, salt, and permutation-call discipline |
| `V02` | [Zero-Knowledge Polynomial Commitment in Binary Fields](https://eprint.iacr.org/2025/1015) | T2 | Interleaves Sumcheck and FRI folding, shares challenges, uses virtual combination oracles, and adds hiding in characteristic two |
| `V03` | [GKR for Boolean Circuits with Sub-linear RAM Operations](https://eprint.iacr.org/2025/717) | T2 | Packs Boolean words into univariate polynomials and couples GKR to a binary-polynomial PCS and word-RAM cost model |
| `V04` | [LatticeFold+](https://eprint.iacr.org/2025/247) | T2 | Uses lattice commitments, an algebraic range proof, double commitments, small fields, and a Sumcheck-based folding transformation |
| `V05` | [Improving Logarithmic Derivative Lookups Using GKR](https://eprint.iacr.org/2023/1284) and [Logup*](https://eprint.iacr.org/2025/946) | T1 | Changes lookup/table organization through fractional Sumcheck, indexed lookup structure, and PCS conversion rather than only a new PLONK gate |

Any V01--V05 result that changes a shared model decision must be restated as an
explicit requirement or candidate before R3. Paper-specific mechanisms remain
in profiles or modules unless at least two materially different families need
the same semantic law.

### 4.3.1 Current algebraic-interaction disposition

The cross-case
[Algebraic Interaction and Reduction](algebraic-interaction-and-reduction/README.md)
package has completed its constructive records for classical Sumcheck,
layered GKR, the ideal-overwrite-duplex transform, and packed Boolean GKR. The
provisional classifications are respectively `Native`, `Native`,
`ConservativeExtension`, and `Native`.

The Sumcheck classification is bounded to an explicit finite polynomial;
generic polynomial-oracle semantics remain open. The GKR classification uses
one flat finite Core; reusable checked elaboration remains deferred. The
duplex construction is not yet an active profile, and the packed result makes
no RAM-consistency or PCS-support claim. The assigned constructive depth and
one bounded closure review are complete for these four entries.

### 4.4 Holdout and frontier cases

Only the named selection rationale is visible before freeze; detailed encoding
is deferred to the holdout pass.

| ID | Holdout | Target depth | Withheld pressure |
|---|---|---:|---|
| `H01` | [WHIR](https://eprint.iacr.org/2024/1586) | T2 | A constrained Reed--Solomon IOPP with richer multilinear and univariate query forms than a FRI-specific oracle vocabulary |
| `H02` | [Circle STARKs](https://eprint.iacr.org/2024/278) | T1 | A STARK over circle-curve domains and function spaces rather than an ordinary multiplicative-subgroup/univariate assumption |
| `H03` | [WARPfold](https://eprint.iacr.org/2024/354) | T1 | Range-checked bridges among multiple non-native fields and movement between proof systems |
| `H04` | [On the Power of Sumcheck in Secure Multiparty Computation](https://eprint.iacr.org/2025/177) | T1 | Multiple parties jointly emulate both Sumcheck prover and verifier roles |
| `H05` | [Transparent SNARKs over Galois Rings](https://eprint.iacr.org/2025/263) | T1 | Protocol construction over Galois rings, testing whether field-only assumptions are semantic or merely profile-local |

`H04` and `H05` may legitimately end as intentional v0 boundaries. Their value
is to make the two-party and algebraic scope explicit rather than silently
universal.

### 4.5 Reserve boundary probes

The following do not receive work unless an earlier case or reviewer exposes a
specific unresolved question:

- MPC-in-the-head and selective-opening protocols;
- designated-verifier or verifier-private-coin protocols;
- threshold, distributed-prover, and multi-prover protocols beyond H04;
- post-quantum Sigma protocols with rejection sampling or aborts;
- asynchronous, concurrent, or resettable composition; and
- quantum-message or quantum-verifier protocols.

Reserve status is not a claim that the model supports them.

## 5. Coverage check

The selected portfolio spans the following independent axes.

| Axis | Covered contrast |
|---|---|
| Interaction | Three-move, multi-round, logarithmic-round, oracle, noninteractive preprocessing, and recursive/folding |
| Randomness | Fresh public coins, Fiat--Shamir, stateful sponge, setup-derived material, shared subprotocol challenges, and external tapes |
| Communication | Scalars, group elements, polynomial messages, direct proofs, logical oracles, commitments, queries, openings, and accumulators |
| Algebra | Prime and binary fields, extensions, groups and pairings, codes and domains, lattices/modules, non-native bridges, and Galois rings |
| Setup | Transparent, universal/updateable SRS, circuit-specific preprocessing, and commitment-key profiles |
| Composition | Sequential reduction, interleaving, batching, lookup composition, accumulation, folding, recursion, and imported verification |
| Roles | Ordinary prover/verifier, distributed proof construction, and joint MPC emulation |
| Analysis | Completeness, soundness, knowledge, HVZK/ZK, RBR, ROM/QROM, extraction, and quantitative loss remain separately applicable |

Coverage means selected pressure, not support.

## 6. Work order

Cases proceed by semantic dependency rather than publication date:

1. **Interaction and Fiat--Shamir:** P01, then V01.
2. **Algebraic reduction:** P03, P04, then V03.
3. **Oracle and commitment layer:** P02, V02, then P05.
4. **Complete argument organizations:** P06, P07, P08, then V05.
5. **Accumulation and recursion:** P09, V04, then P10.
6. **Provisional semantic freeze:** synthesize design-set results without
   consulting holdout details beyond their frozen selection rationale.
7. **Cold holdout validation:** H01--H05 at their assigned depths.
8. **R2 convergence:** classify all cases, retain obstructions and extension
   boundaries, and derive only the bounded R3 research questions they require.

A cluster may stop early when a fundamental obstruction invalidates the model.
Repair and refreeze precede later dependent cases. Independent families should
not all be rewritten around an already-failed shared boundary.

## 7. Per-case output contract

Each case receives one compact record rather than a copy of the shared method:

```text
source and version
protocol kind and claimed scope
canonical anatomy and variant delta
candidate-model correspondence
authority and identity map
one complete representative trace or object graph
relation/statement and construction/composition boundaries
negative mutations or counterexamples appropriate to its level
classification and exact obstruction or extension
non-claims and open Analysis obligations
model-change request, if any
promotion or closure decision
```

T3 executable packages may have code, fixtures, tests, and machine reports.
T1 and T2 cases should remain documents unless promotion is justified. Shared
definitions belong in a small common ledger; case pages link to them rather
than repeating them.

## 8. Model-change and holdout discipline

1. Design-set cases may propose changes but cannot silently edit durable target
   pages.
2. Every change request states whether it is owner-local, conservative, or
   fundamental and which completed cases must be replayed.
3. A provisional model freeze binds the exact semantic pages or finite model
   used for holdout validation.
4. Holdout readers may record an obstruction but do not repair the model in
   place.
5. If a holdout reopens the model, retain the failed result, adjudicate the
   change, refreeze, and rerun affected holdouts.
6. A case cannot pass through equal sample values, post-hoc identity matching,
   self-authored success evidence, or a positive check guaranteed by input
   shape.

External validation is most valuable at two gates: after the provisional
design-set freeze and after any holdout-driven repair. The reviewer should
receive the frozen model, one assigned source, the output contract, known
non-claims, and no expected correspondence map.

## 9. R2 exit condition

R2 can converge when:

- P01 and P02 satisfy T3 or retain a decisive failed witness;
- every P03--P10 and V01--V05 case reaches its assigned depth or has an
  explicit superseding obstruction;
- H01 reaches T2 and H02--H05 reach T1 against a frozen model;
- every result has one classification and an exact owner or boundary;
- cross-case concepts are derived from repeated need rather than one paper;
- no unresolved result is hidden by an opaque escape mechanism;
- R3 questions are bounded to actual obstructions and credible opportunities;
  and
- no protocol-security, theorem-applicability, general expressiveness, or
  implementation-support claim is inferred from the portfolio.

The first exit row is now satisfied by the two retained deep anchors. Every
other row remains active: the remaining protocol, variant, and holdout cases
have not been waived or implied by the FRI/IOR result.

## 10. Known risks and non-claims

The portfolio may still overfit published families, and primary papers may
leave implementation conventions or proof-system composition implicit. A
recent date is not evidence of sound design, and a canonical paper is not
authority for zkc. The same mechanism may appear under different vocabulary;
conversely, similar vocabulary may hide different semantics.

Passing all selected cases would support a bounded claim: the frozen model
constructively represented the named families and survived several withheld
structural variants. It would not prove completeness for all current or future
ZK protocols, cryptographic security, property transport, performance, or
fitness for every backend.

## 11. Intended durable destinations and deletion trigger

Accepted shared semantics go only to their exact owners under `pir/`,
`relations/`, `analysis/`, `compiler/`, and `project/`. Protocol-specific
profiles remain owner-local. Retained rationale goes to the eventual decision
record; supported and intentionally unsupported boundaries go to the v0 scope;
replayable finite evidence goes to `evidence/` only if its claim is still
needed.

Delete this page after R2--R4 results are absorbed, the durable scope and
extension boundaries are explicit, retained cases have stable evidence homes,
and no durable page depends on this temporary portfolio.
