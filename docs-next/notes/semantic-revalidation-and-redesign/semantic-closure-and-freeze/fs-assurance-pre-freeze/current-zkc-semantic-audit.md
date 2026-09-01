# Current zkc Fiat--Shamir Semantic Audit

> **Kind:** Temporary live-target reconstruction and gap register
> **Audited baseline:** 808ec2d575da126f1d5cb22ad050ca52696dd75e
> **Authority:** None. Each conclusion below is relative to the linked owner.

## 1. Audit conclusion

The selected redesign is structurally capable of expressing a sound
Fiat--Shamir assurance program without an ownership redesign.

The strongest existing result is not “Fiat--Shamir is secure.” It is:

> For an admitted canonical-framed construction, the logical challenge
> schedule and every pre-draw transition input are derived from one admitted
> InteractiveCore, checked exactly at runtime, and exposed through
> owner-issued views that downstream profiles cannot replace with authored
> transcript lists.

That closes the target-design defects previously described as no derived
transcript obligation, parallel readers of round structure, and no Statement
route. It does not close concrete encoding, primitive binding, challenge
distribution, oracle-model correspondence, theorem applicability, dynamic
OIR execution, parser, provider, or deployment obligations.

The correct disposition is therefore a conditional semantic-freeze go with
explicit post-freeze activation gates. No gap found here requires a new
FSKernel, a transcript root authority, or a semantic token owner.

## 2. Audited owner graph

| Owner | Current FS responsibility | Current result | Explicit nonownership |
|---|---|---|---|
| Foundation | Canonical values, identities, profiles, admission, qualified outcomes, algorithms, capabilities | Provides exact carriers and failure partition used by every FS layer | Protocol meaning and cryptographic property truth |
| PIR / InteractiveCore | Verifier-observable interaction, input roles, total schedule, guards, challenges, public-coin eligibility | One source of logical chronology and binding coordinates | External relation completeness, theorem truth, endpoint implementation |
| PIR / canonical FS | Construction identity, typed frames, DerivedPrefix, RequiredInfluence, namespace, state-transition ABI, retry and failure | Exact structural construction and runtime prefix equality | Injectivity, collision resistance, random-oracle behavior, distribution, theorem, parser, provider |
| PIR / Interface and Plan | Exact external input assignment and Statement member map over admitted Core bindings | Every Core Statement BindingRef must have one external Statement member | Whether the application supplied all semantically expected Statements before Core formation |
| Relations | Whole Statement correspondence, relation slots, equations, witness and run meaning | Can compare exact selected external Statement surface with every selected K2 binding region | Transcript scheduling and security property |
| Analysis | Experiment, adversary, source property, theorem, quantitative bound, assumptions, applicability, qualified result | One precise classical adaptive AFK lane demonstrates exact query/process and sampler intake | OIR projection and implementation conformance |
| OIR | Source-independent endpoint graph, exact static FS contract, projection relation | Canonical-framed static projection preserves exact graph fields under bounded equality | Protocol transformation, dynamic receipts/execution, concrete provider |
| Realization | Supplier binding, lowering, parser, target-specific RealizesOir, deployment and invocation | Selected lifecycle and outcome contract; full runtime design remains unactivated | Property truth, source meaning, projection truth |
| Consumer / deployment policy | Joins exact qualified results and accepts retained assumptions for one use | Architectural slot exists | Authority to manufacture a missing owner judgment |

The factorization follows responsibility rather than implementation phase:

~~~text
InteractiveCore
  -> canonical FS structure
  -> external Statement correspondence
  -> cryptographic qualification
  -> static endpoint projection
  -> concrete realization
  -> deployment reliance
~~~

Each arrow consumes exact typed results. No arrow upgrades an observation or
citation into the preceding owner's judgment.

## 3. Canonical PIR construction audit

The complete construction is defined by
[Canonical-Framed Fiat--Shamir Construction](../../../../pir/fiat-shamir.md).
The following properties are present in the audited target.

### 3.1 One admitted source schedule

Protocol is factored as InteractiveCore plus a challenge interpretation.
Fiat--Shamir does not author a second list of rounds or “items to hash.”
Construction formation reads the admitted Core, including:

- Core input roles and scope;
- total occurrence order;
- active guards and challenge conditions;
- prover and verifier messages;
- public Oracle publications, queries, and answers;
- claims, reductions, required publications, and terminal influence;
- challenge domains and correlation;
- module-owned influence additions where supported.

This matters more than cosmetic single-source-of-truth wording. A downstream
profile receives owner-issued exact views and coordinates; it does not receive
authority to reinterpret the Core schedule.

### 3.2 Typed, derived actions

Initialization and occurrence actions are functions of the admitted Core,
construction, invocation, and prior receipts. Frames retain kind, exact owner
coordinate, typed value, scope, and required headers. The canonical family
includes Core, construction, and application-domain separation rather than
raw payload concatenation.

There is no authored challenge-prefix field in construction identity.
A cached or replayed sequence must compare equal to the derived result before
use.

### 3.3 RequiredInfluence and Last-Challenge structure

For challenge c, RequiredInfluence is an order-preserving filter over the full
DerivedPrefix. Its base law includes all opened-scope bindings, every active
prior prover/verifier message, public Oracle activity, guards, previous draws,
and challenge conditions. Reduction requirements may strengthen the law with
exact prior publication atoms and their least required following challenge.
They cannot remove a base requirement or name a future/current-draw atom.

This design closes two different failure modes:

- ordinary prior material is included because it is in the derived total Core
  schedule; and
- protocol-specific last-challenge material is included because the reduction
  contract can name the exact publication/challenge dependency.

The second still depends on accurate protocol semantics. No generic transcript
mechanism can infer that a batching challenge mathematically needs a value
that the protocol author did not model as such.

### 3.4 Runtime exactness

Immediately before the first draw of c, the runtime law is exact equality:

~~~text
TransitionInputLog(actual_receipts_before_draw_c) = DerivedPrefix(c)
~~~

This rejects injected, omitted, duplicated, reordered, substituted, wrongly
scoped, and wrong-kind transition inputs. RequiredInfluence remains an audit
projection of the full equality, not a weaker acceptance path.

The equality is stronger than checking a state digest. It retains the complete
ordered receipt inputs, so a noninjective state transition cannot hide a
schedule mismatch. Equally importantly, PIR says that this does not prove the
transition itself is injective or cryptographically binding.

### 3.5 Namespace, retry, and failure

Challenge namespace is derived from construction and Core identity, the scope
path, challenge coordinate, challenge type/domain, coin-correlation law, and
draw ordinal. Initialization and binding frames carry application/session
material according to the admitted Core. Each retry is a distinct draw with a
bounded law and exact SamplingExhausted failure.

This is sufficient to name the object that Analysis must study. It is not
proof that the selected decoding is uniform, that retries preserve a theorem,
or that a deployment uses the intended ciphersuite and session lifecycle.

### 3.6 Exact nonclaims

The construction explicitly does not establish:

- collision resistance, injectivity, indifferentiability, entropy, uniformity,
  independence, random-oracle behavior, or side-channel properties;
- soundness, knowledge soundness, state-restoration/RBR, zero knowledge, or
  QROM security;
- commitment/opening or BCS adequacy;
- proof-serialization uniqueness or parser safety;
- concrete provider conformance; or
- production support.

This nonclaim is a positive architecture property. Removing it would make
structural admission unsoundly subsume the 2026 Plonky3 transition-binding
failure class.

## 4. Closed Statement correspondence audit

### 4.1 What is closed

PIR Interface admission computes every Statement BindingRef in the exact
admitted Core and requires the observed external Statement assignments to
have exactly that binding set. It also requires exact assignment for every
public and verifier-private Core input.

Relations then defines ExternalStatement with WholeSelectedSurface:

- every selected Interface Statement member is treated as one complete
  external-slot value;
- selected Statement-edge targets must name every and only the distinct K2
  Statement bindings named by those members; and
- target selectors must form an exact nonoverlapping cover of every selected
  binding value.

A missing selected member, extra edge, substituted binding, partial selector,
overlap, or route to an unselected member is a disagreement.

### 4.2 What is necessarily external

The closure domain is the admitted application model. Suppose an application
intends the public instance to be the pair (Y, policy), but constructs a Core
whose only Statement binding is Y and supplies no external manifest saying
that policy is required. PIR correctly binds every declared Statement, and
Relations correctly covers every selected binding, yet neither can invent
policy.

This is not a defect with a hidden semantic fix. It is the specification
boundary faced by every formal method. The consumer must provide an
authenticated expected Statement/interface manifest or a higher-level
application correspondence proposition. Once supplied, existing Interface
and Relations mechanisms can compare it exactly.

The freeze requirement is therefore:

> Retain closed-world Statement intake as an explicit application/consumer
> premise, and never describe exact Core-relative coverage as proof that the
> external application specification itself is complete.

## 5. Analysis audit

The live
[Cryptographic Property Profiles](../../../../analysis/cryptographic-properties.md)
contain a detailed classical adaptive AFK application. It is not merely a
paper citation. The profile fixes:

- adversary and quantifier order, including adaptive Statement output;
- exact selected PIR/Relations source views;
- exact theorem Statement boundary;
- a total, canonical, injective query encoding requirement;
- image and off-image random-oracle query behavior;
- one complete adaptive lazy random-function process law;
- query accounting, repeated-index consistency, and theorem-authorized
  programming/rerun operations;
- source special-soundness evidence;
- theorem source and applicability;
- sampler adequacy; and
- exact loss/target-property coordinates.

The profile also states that a concrete hash or duplex implementation does not
thereby realize the random-oracle process.

This is strong evidence that the Analysis meta-model can host reusable
Fiat--Shamir assurance profiles. The remaining limitation is scope:

- the current lane is one selected classical AFK/Schnorr family;
- generic encoding and concrete-transition qualification are not yet
  published as reusable FS profile components;
- BCS/state-restoration and RBR applications remain theorem-specific;
- the duplex-sponge sibling has no active theorem due to recorded source
  validation blockers and unsupported OIR intake; and
- QROM needs a separate adversary/query/theorem profile.

These are missing qualified results and reusable profiles, not missing
semantic owners.

## 6. BCS and Oracle audit

Canonical PIR separates:

1. a logical Oracle lifecycle;
2. a structural Oracle-commitment construction that elaborates a concrete
   commitment/opening Core;
3. same-Core Fiat--Shamir over the independently admitted concrete Core; and
4. Analysis properties and theorem transport.

The structural construction can establish deterministic bounded elaboration
and exact static correspondence. It does not establish commitment binding,
opening soundness, state-restoration or RBR properties, random-oracle
correspondence, or BCS quantitative loss.

This answers the “why not just formally verify the verifier with BCS?”
question:

- BCS is a compiler theorem, not verifier implementation verification;
- verifying the emitted verifier can prove conformance to its specification;
- source-property and theorem applicability remain separate;
- an omitted Statement or lossy codec can exist in the verified
  specification; and
- concrete random-oracle realization remains a model/correspondence premise.

The architecture can host all of these results without assigning them to one
kernel.

## 7. Duplex-sponge sibling audit

The
[Duplex-Sponge Fiat--Shamir Construction](../../../../pir/duplex-sponge-fiat-shamir.md)
correctly remains a sibling rather than an implementation detail of the
canonical-framed profile. Its semantics include a transform-owned salt, raw
message codecs, mutable absorb/squeeze state, exact decoder, and a different
proof-tuple boundary.

The page records the Analysis obligations from the Chiesa--Orru construction:
injective message encoders, decoder bias/fiber behavior, salt law, random
permutation and inverse-query models, exact query bounds, source
state-restoration/knowledge properties, theorem validation, and applicability.
It activates no theorem. OIR returns Unsupported until a sibling projection
owns proof-tuple parsing, salt placement, and wire/transcript codec
correspondence.

This is the correct fail-closed outcome. An inactive theorem or unsupported
endpoint is not evidence that the semantic construction should be collapsed
into the canonical family.

## 8. OIR audit

The bounded
[OIR Projection Contract](../../../../oir/projection-contract.md) supports
canonical-framed Fiat--Shamir only. It separates:

- source-side support and exact view extraction;
- independent source-blind target construction;
- LocalOirValid;
- source-relative ProjectionCorrect; and
- later Realization.

Because the bounded profile permits no semantic reordering, split/fusion, ABI
adaptation, or optimization, projection uses exact canonical graph equality.
The endpoint graph retains static construction, frames, DerivedPrefix,
namespace, retry, state, sampler, and failure laws.

This closes static substitution and omission under the selected profile. The
graph is intentionally not an execution trace. Runtime guard activity, draws,
receipts, state versions, decoded values, proof transport, and endpoint
results remain Stage 4B subjects. Any optimizer or nontrivial lowering must
select a new explicit refinement relation rather than weakening exact equality.

## 9. Realization audit

[Realization and Runtime](../../../../realization/README.md) selects the correct
lifecycle but remains a scaffold:

~~~text
AdmittedOir
  -> exact supplier binding
  -> effectful candidate production
  -> target-specific RealizesOir check
  -> admitted realization
  -> deployment binding and activation
  -> bound invocation and execution
~~~

It distinguishes Affirmative, Negative, Unsupported, MissingDependency,
CannotAnswer, KindMismatch, Refused, Malformed,
DeterministicLimitExceeded, and CheckerFailure. Only an exact affirmative
RealizesOir result can mint an admitted realization. Build success,
manifests, vectors, or ordinary conformance tests do not suffice.

For FS, Stage 4B still needs:

- exact proof serializer/parser and end-of-input law;
- explicit state-threaded transcript lowering;
- query-index preservation including session, instance, frame, namespace,
  and draw;
- concrete absorb/squeeze/advance/decode providers;
- retry and failure correspondence;
- target-specific translation validation, verified-producer correspondence,
  or an explicit trusted-producer residual; and
- deployment ciphersuite/session/resource binding.

## 10. Historical cross-lane finding reassessment

The separate cross-lane review checkout recorded three FS architecture
findings against an earlier target. This audit does not edit that review
state; the verification lane must confirm any formal disposition.

| Finding | Original pressure | Current reconstruction | Proposed review disposition |
|---|---|---|---|
| CLR-1 | No derived transcript obligation; prior required proof material could remain Wire-only | DerivedPrefix now comes from the full Core schedule; RequiredInfluence adds base, reduction, and module requirements; exact runtime equality and negative K2 cases reject omission while allowing irrelevant material that emits no required future influence | Proposed-resolved semantically; retain concrete-transition and theorem nonclaims |
| CLR-2 | PIR construction, theorem instance, and property transport might read separate copies of round structure | PIR is sole source authority; owner-issued views and exact profile imports feed Analysis; OIR consumes a complete source view and compares independent target structure. Downstream requests carry coordinates and capabilities, not authored round tables | Proposed-resolved for semantic declaration; realization must still preserve the issued contract |
| CLR-3 | Statement had no mandatory route into the first challenge prefix | Every declared Statement binding is a derived scope-opening frame; Interface admission equals the complete Core BindingRef set; Relations provides exact selected-surface coverage | Proposed-resolved relative to the admitted Core; retain explicit application-manifest premise for Statements omitted before Core formation |

The executable package includes the original falsifier shapes:

- omitted required frame and an exact positive prefix;
- a weak internally exact authored schedule rejected by an external manifest;
- reordered, duplicated, and substituted frames; and
- one exact logical prefix whose lossy concrete adapter still aliases.

The last case is important: resolving the old structural findings must not be
misreported as resolving the concrete primitive layer.

## 11. Gap register

Statuses:

- **Closed:** current owner and executable pressure cover the semantic issue.
- **Representable:** the owner can state the result, but no reusable or
  subject-specific affirmative qualification is available.
- **Unsupported:** the family is recognized and fails before partial use.
- **Stage 4B:** intentionally absent dynamic implementation contract.
- **External premise:** completeness is relative to supplied application data.

| Gap | Exact missing result | Current status | Owner | Freeze effect | Activation effect |
|---|---|---|---|---|---|
| G1 | Application-level closed Statement manifest beyond the admitted Core | External premise | Interface/Relations input plus consumer policy | Record boundary; no owner redesign | Mandatory for adaptive/strong-FS claim |
| G2 | Reusable total/canonical/injective logical query-encoding profile | Representable; instantiated in AFK lane | Analysis | Does not block if typed intake is preserved | Blocks every theorem application needing injectivity |
| G3 | Concrete frame-to-state transition binding, including radix, limbs, padding, and length | Representable; no generic affirmative result | Analysis for property, Realization for provider | Preserve PIR nonclaim; no structural freeze block | Blocks concrete-hash/sponge reliance |
| G4 | Reusable sampler adequacy with retry, bias, exhaustion, and query-loss accounting | Representable; AFK exact-total boundary exists | Analysis | No structural freeze block | Blocks theorem application unless exact-total special case applies |
| G5 | Adaptive oracle-process correspondence for each construction/primitive model | Representable; AFK classical ideal process specified | Analysis | No structural freeze block | Blocks ROM/ideal-permutation claim |
| G6 | Validated source property and exact theorem applicability for BCS/RBR/AFK/duplex family | Per-family partial; duplex theorem inactive | Analysis | Unsupported/CannotAnswer is acceptable at freeze | Blocks named security property |
| G7 | QROM adversary, theorem validation, applicability, and loss | Absent distinct profile | Analysis | Separate future regime; no classical freeze block | Blocks every QROM claim |
| G8 | Dynamic OIR execution and nontrivial lowering preservation | Stage 4B | OIR for dynamic semantics; Realization for lowering | Static contract must remain complete | Blocks executable endpoint activation |
| G9 | Concrete provider, serializer/parser, full-consumption, and RealizesOir result | Stage 4B | Realization | No semantic freeze block | Blocks admitted realization |
| G10 | Deployment ciphersuite, session lifecycle, resources, side channels, and threat-model policy | Stage 4B / deployment-specific | Realization and consumer policy | No semantic freeze block | Blocks production approval |

No row is ownerless. G1 cannot be inferred, G2--G7 are Analysis-qualified
questions, G8 is the dynamic OIR boundary, and G9--G10 are Realization and
consumer boundaries.

## 12. Freeze-blocker test

A Fiat--Shamir issue blocks semantic freeze only if one of the following is
true:

1. the frozen semantic model cannot distinguish two obligations that need
   independent outcomes;
2. an obligation has no owner or two owners claim the same meaning;
3. the selected identities erase a coordinate needed by a later property or
   conformance check;
4. unsupported work falls through to partial success; or
5. a current semantic claim is stronger than its evidence.

The audit found no such counterexample at the audited baseline. The model
distinguishes all ten assurance layers, preserves the necessary coordinates,
and records explicit nonclaims and Unsupported/CannotAnswer boundaries.

The following do not, by themselves, block semantic freeze:

- absence of an affirmative cryptographic theorem;
- absence of a concrete hash or sponge correspondence;
- unimplemented dynamic OIR or parser;
- no QROM profile; or
- a recognized unsupported duplex endpoint.

They block only the corresponding property or activation claim.

## 13. Evidence and validation ledger

| Evidence | Baseline result | Permitted conclusion |
|---|---|---|
| Focused FS assurance pressure evaluator | 33 of 33 finite tests passed | Selected finite layer distinctions and mutations behave as intended |
| Fast semantic aggregate | 6 of 6 gates passed in 11.805 seconds, including K2 83/83, FS pressure 33/33, and dependent Interface/Plan/Relations 50/50 | Every fast-tier component and the newly registered FS gate completed together |
| K1 executable foundations | 130 of 130 tests passed, exit 0 | Existing bounded Foundation behavior remains green |
| Indexed Core elaboration | 25 of 25 tests passed, exit 0 | Existing bounded elaboration behavior remains green |
| Plan continuation | 53 of 53 tests passed, exit 0 | Existing bounded Plan continuation behavior remains green |
| Duplex, native FRI, and retained Schnorr runners | Each completed with exit 0; emitted reports contain 8 duplex and 45 Schnorr classified cases | Their selected finite reports were reproduced; no theorem promotion follows |
| K3 integrated closure | 27 of 27 tests passed in 66.543 seconds, exit 0 | Existing bounded joined-boundary controls remain green |
| K3 OIR projection evaluator | 94 of 94 tests passed in 428.678 seconds, exit 0 | Existing bounded static projection controls remain green |
| K3 Analysis closure evaluator | 202 of 202 tests passed in 4,179.116 seconds, exit 0 | Existing bounded Analysis identity, qualification, theorem-source, applicability, and specialization controls remain green |
| Complete semantic gate set | All 15 full-tier components obtained final exit 0: six in one fast aggregate and the nine non-fast components directly | Equivalent component coverage to the full tier without redundantly rerunning the 70-minute Analysis process inside a second wrapper |
| Primary-source ledger | Exact downloaded hashes for papers/draft; live advisory locators recorded | Source snapshot and provenance only |

Passing rows are not theorem, security, compiler, parser, or deployment
evidence. The four-worker Analysis attempt was interrupted after fifteen
minutes because its runner buffered all worker output; it was not classified
as a failure. The observable single-process rerun above supplied the accepted
final result.

## 14. Audit nonclaims

This audit does not establish:

- correctness or security of any concrete hash, sponge, field adapter, proof
  system, or deployment;
- truth of a paper theorem or the absence of proof defects;
- source state-restoration, RBR, special soundness, extraction, or zero
  knowledge;
- classical ROM or QROM correspondence;
- completeness of an application specification not supplied to the model;
- dynamic OIR correctness, compiler refinement, parser safety, or
  RealizesOir; or
- closure of the private cross-lane review until its owning lane confirms the
  proposed dispositions.
