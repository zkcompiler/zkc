# Nova, HyperNova, CycleFold, and ProtoStar

> **Portfolio cluster:** committed folding, multi-folding, accumulation, and
> cycle-based recursion
> **Depth:** mixed T1/T2 source-grounded constructive mapping; each case states
> its achieved depth below
> **Authority:** Temporary research only. This page does not change durable
> semantics, import a theorem, or establish implementation support.

## 1. Result at a glance

These sources do not justify one universal `Accumulator` or
`FoldingProtocol` subject. They exhibit three materially different
organizations:

1. Nova directly folds two committed relaxed-R1CS instance/witness pairs;
2. HyperNova multi-folds running linearized-CCS and fresh CCS pairs, with
   CycleFold adding a second semantic accumulator for outsourced curve
   operations; and
3. ProtoStar compiles a special-sound protocol through commit-and-open and
   Fiat--Shamir, accumulates its relaxed verifier predicate, and retains a
   separate decider.

The existing flat `InteractiveCore`, typed claim/reduction graph, and
Relations `RelationTransform` fit their verifier-observable public evolution.
Nova and HyperNova expose one narrower missing lifecycle; CycleFold exposes it
only for the companion witness. In those cases the honest prover derives the
relevant private witness after the last genuine public prover decision. A
dummy message changes the source protocol; an opaque callback changes Core
authority. Corrected-cycle Nova and ProtoStar are important negative controls:
their source schedules contain later genuine prover decisions from which the
new private state can be exported. The shared candidate is therefore a
bounded, private Plan completion derivation only for source schedules that
truly end their prover-publication sequence before private output derivation.
The later architecture selection accepted that lifecycle extension and the
durable specifications now own it; this source record preserves the evidence
that led to the selection.

## 2. Frozen source ledger

The byte locks below were recomputed from the exact PDFs on `2026-08-31`.
Dates identify ePrint revisions, not first publication dates.

| Source | Frozen revision | PDF bytes | SHA-256 | Primary loci |
|---|---:|---:|---|---|
| [Nova: Recursive Zero-Knowledge Arguments from Folding Schemes](https://eprint.iacr.org/2021/370) | `2024-07-20` | 597,761 | `2a912c9715d0c8a6ae573addedb1d77643c5540e3968a95a9d82059dee0bf6e1` | Definitions 11--12, Constructions 1--3, Theorem 3, Sections 4.1--5 |
| [Revisiting the Nova Proof System on a Cycle of Curves](https://eprint.iacr.org/2023/969) | `2023-06-20` | 1,294,255 | `f2118e5a04bd226e367639b2e8c4128eca71f1c903af450452a82de57f8c48d8` | Sections 3--5, especially folding-key and augmented-circuit linkage |
| [HyperNova: Recursive Arguments for Customizable Constraint Systems](https://eprint.iacr.org/2023/573) | `2026-02-20` | 1,543,321 | `08fdc3b155a9b681baecb48aad26993f53c0cb08511c0771154bd5a349761572` | Construction 1, Theorem 1, Construction 5, Sections 6 and 9, Construction 7 |
| [ProtoStar: Generic Efficient Accumulation/Folding for Special-Sound Protocols](https://eprint.iacr.org/2023/620) | `2023-12-21` | 680,709 | `e93bc711df7bc2e733d446f1f273c5d2bc9d769da2f2e4643f2bc506e87d0509` | Definitions 5 and 8--9, Figures 3--5, Theorems 1--3, Sections 3.1--3.4 |

The 2023/969 paper is mandatory Nova intake, not optional implementation
commentary. It records a soundness vulnerability in the former cycle-based
organization and repairs the recursive linkage. The original Nova paper
remains authority for the abstract committed relaxed-R1CS fold; 2023/969 is
authority for the corrected two-cycle recursive organization.

No later revision or library implementation may silently replace these byte
locks. The source theorems remain external claims and are not validation
bases merely because this record maps their constructions.

## 3. Shared owner and identity graph

The following graph uses existing owner kinds symbolically. Each concrete case
substitutes its own types, algorithms, modules, dimensions, and schedules.

```text
exact algebra / commitment / hash modules
        |
        +--> RelationDefinitionId
        |      -> RelationInterfaceId
        |      -> RelationSemanticModelId
        |      -> public RelationInstanceId occurrences
        |      -> confidential witness occurrences
        |      -> RelationTransformId
        |
        +--> claim, reduction, and check contracts
                   |
                   v
              InteractiveCoreId
                   |
                   +--> FreshProtocolId
                   +--> target-strong-FS ProtocolId
                   |
                   +--> ProtocolInterfaceId
                   +--> ProverPlanId
                             |
                             +--> PlanWitnessSurfaceId

ProtocolId + RelationInterfaceId + RelationTransformId
        -> ProtocolRelationBindingId

PlanWitnessSurfaceId + RelationInterfaceId
        -> PlanWitnessBindingId

source manifests + exact questions + hypotheses + validation bases
        -> Analysis judgments
```

The Plan does not cite Relations. The Protocol-relation binding does not cite
the Interface, Plan, OIR, proof bytes, or an Analysis result. Confidential
witness occurrences have owner-local identity and are never content-addressed.
Equal public accumulator values at different steps remain different claim and
relation-instance occurrences. A recurrence edge relates them; value equality
does not collapse them.

For all cases:

- setup needed by the verifier is a typed `PublicParameter` binding or exact
  Core dependency;
- proving-only setup remains a Plan input and cannot enter a deliberately
  minimal verifier Core merely because the source calls both values `pp`;
- Core claims and reductions express public causal organization, not theorem
  truth;
- Relations gives the public input/output occurrence transform and separate
  witness correspondence;
- Analysis owns preservation, extraction, knowledge, zero knowledge,
  random-oracle applicability, induction, and composition; and
- Interface/OIR owns proof packaging, not causal message identity.

### 3.1 Interface and OIR projection ledger

Each admitted Fresh and FS Protocol receives its own Interface because the
challenge supplier and proof transport differ. The projection is nevertheless
occurrence-preserving:

| Member | Invocation/Statement presentation | Prover transport occurrences | Completion presentation |
|---|---|---|---|
| Nova fold | ordered `U_1,U_2` plus verifier setup | `T_bar` | reduction-derived `U_out` |
| corrected cycle step | transition coordinates, retained prior strict pair `u_i^(2)`, and both running pairs | both fold commitments in source order plus the retained strict-pair proof-state output | retained strict pair plus both evolved running instances |
| HyperNova | ordered `mu` LCCCS and `nu` CCS instances plus setup | every Sumcheck polynomial, then the exact `sigma/theta` record | one reduction-derived LCCCS instance |
| CycleFold | primary, companion, and fresh instances plus both setup profiles | primary Sumcheck publications and companion-fold publication in source order | primary and companion output instances |
| ProtoStar NARK | `pi` plus commitment setup | ordered commitment/opening package | NARK accept/reject |
| ProtoStar accumulation | `pi`, NARK public instance, old accumulator, and setup | ordered correction commitments, then the new public accumulator after `alpha` | new-accumulator claim plus accumulation accept/reject |
| ProtoStar decider | one accumulator public instance plus setup | private openings are Plan material, not public transport unless a wrapper proves them | decider accept/reject |

An OIR may serialize all FS prover publications into one proof byte string only
through a total checked projection whose fields retain these exact source
occurrences and order. Packaging does not turn several causal Messages into
one Core Message. Fresh verifier coins are transport actions but not proof-byte
fields. The FS sibling removes those external coin transports through its
separately admitted challenge interpretation; it does not remove the Challenge
occurrences.

The specialized prover projection is formable only after an affirmative
`PlanRealizes` over the complete Plan graph. In the pre-selection baseline,
Nova, HyperNova, and the companion output of CycleFold had no legal source
decision for the candidate completion export. The selected accepted-terminal
Plan continuation closes that semantic gap, subject to the distinct evidence
depths and open profile-publication gate recorded by the convergence page.
Corrected-cycle Nova has later genuine construction/publication
decisions after each fold, and ProtoStar has a genuine post-`alpha` output
decision. Their private outputs can therefore use ordinary decision-local
exports in the source-grounded mapping. The former failure is part of the
affected cases' `ConservativeExtension` result rather than an omitted
projection detail.

### 3.2 Analysis question split

At minimum, each member needs separate questions for:

```text
public transform agreement
forward relation refinement / fold preservation
honest Plan construction and private witness grounding
folding or accumulation completeness
knowledge soundness / extraction under an exact strategy class
zero knowledge or witness hiding under a separate experiment
Fresh-to-FS theorem applicability for the exact target construction
finite recurrence composition and, separately, family-level IVC induction
```

ProtoStar additionally separates NARK knowledge, accumulation knowledge,
decider correctness, and the imported accumulation-to-IVC theorem. Corrected
Nova additionally separates transition linkage and non-malleability.
HyperNova separates interactive multi-fold soundness from applicability to the
strengthened target FS construction. No positive edge in this list follows
from a source citation or an accepting run.

### 3.3 Exact adjacent-step recurrence

For every case that claims a direct adjacent-step continuation, the public and
private lanes are checked independently before a final conjunction. The public
lane is one affirmative `EquationGrounding` with exactly two
`ExactCausallyGenerated` run slots: the source output instance in run `i` and
the target input instance in run `i+1`. Its operands retain both exact run
objects and both exact `RelationInstance` occurrences.

The private lane begins when `IssueAcceptedPlanWitnessIngressSupply` consumes
one exact continuation output and one exact unfilled target `WitnessIngress`.
It returns one `ReadyPlanWitnessIngressSupply`, its live one-use capability,
and a `CausalPlanWitnessHandoffCapability`. After the target run is grounded,
`JoinCausalPlanWitnessHandoff` combines the source-output and target-input
private groundings with that capability to produce
`CheckedPlanWitnessHandoffCorrespondence`. Finally,
`JoinCausalPlanStepRecurrence` requires exact source/target run and instance
agreement between that private result and the public equation, producing one
`CheckedCausalPlanStepRecurrence` and live capability.

All of these are nonidentified process-local runtime objects. This establishes
one exact causal recurrence edge without equating occurrences. It does not by
itself establish fold preservation, satisfaction, or induction over a finite
or unbounded family. A value recovered from serialized storage may be supplied
as an ordinary fresh input, but a Realization receipt cannot recreate the live
direct-handoff capability and therefore cannot claim this causal edge.

## 4. Nova: one committed relaxed-R1CS fold

### 4.1 Exact finite member

Fix one field `F`, dimensions `m > l >= 1`, sparse R1CS matrices
`A,B,C in F^(m x m)`, and exact hiding additively homomorphic commitment
profiles for vectors of lengths `m` and `m-l-1`.

```text
NovaFoldMember(F,m,l,A,B,C,ComE,ComW) = {
  public instance U_i = {
    E_commit : ComEPoint,
    u        : F,
    W_commit : ComWPoint,
    x        : FixedSeq<F,l>
  }

  private witness W_i = {
    E       : FixedSeq<F,m>,
    r_E     : F,
    W       : FixedSeq<F,m-l-1>,
    r_W     : F
  }

  prover publication T_bar : ComEPoint
  verifier challenge r      : F
  output instance U         : same type as U_i
  output witness W_out      : same type as W_i
}
```

`U_i` is satisfied when both commitments open to the private vectors and
`(A Z_i) o (B Z_i) = u_i (C Z_i) + E_i`, where
`Z_i=(W_i,x_i,u_i)`. Commitment setup, group encodings, field arithmetic,
matrix evaluation, and commitment algorithms are exact dependencies. Hiding,
binding, and extractor premises are Analysis hypotheses.

### 4.2 Exact Fresh Core schedule

```text
initial Statement bindings: U_1, U_2
initial persistent claims:  C_1(U_1), C_2(U_2)

e0  Prover Message  T_bar = ComE(T, r_T)
e1  Verifier FreshChallenge r <- F

R_fold:
  inputs                 = [C_1, C_2]
  required_publications  = [(T_bar, next=r)]
  required_challenges    = [r]
  outputs                = [C_out(U)]

e2  successful completion terminal with public output U,
    disposing C_out explicitly
```

The public transform is exactly:

```text
E_commit = E_commit_1 + r*T_bar + r^2*E_commit_2
u        = u_1        + r*u_2
W_commit = W_commit_1 + r*W_commit_2
x        = x_1        + r*x_2
```

The source folding verifier derives rather than receives `U`; therefore the
exact source Core has no additional Boolean fold check or prover-supplied
output instance. Adding one would describe a different wrapper. The terminal
records successful completion of the fold and exports the reduction-derived
public instance; it does not check either private relaxed-R1CS witness.

### 4.3 Honest Plan and the final-Challenge gap

At `e0`, the Plan reads both input witnesses and fresh `r_T`, computes the
cross term

```text
T = A Z_1 o B Z_2 + A Z_2 o B Z_1
    - u_1 C Z_2 - u_2 C Z_1,
```

publishes `T_bar`, and retains `(T,r_T)` as private Plan state. After `e1`, it
must derive:

```text
E_out   = E_1   + r*T   + r^2*E_2
r_E_out = r_E_1 + r*r_T + r^2*r_E_2
W_out   = W_1   + r*W_2
r_W_out = r_W_1 + r*r_W_2.
```

No public prover message follows `r`. Current ordinary decision recipes run
only at a public `ProverDecisionPoint`; current Relations private transforms
are deterministic over relation witnesses and public parameters and cannot
recover fresh Plan-local `r_T`. Therefore neither owner can currently export
the exact evolved private witness without changing the source schedule or
smuggling Plan state through Relations.

The candidate T2 Plan graph adds no Core event:

```text
WitnessIngress(U_1 witness), WitnessIngress(U_2 witness)
    + RandomnessIngress(r_T)
    -> DecisionRecipe(e0: T_bar, retained_state=(T,r_T))
    -> CompletionRecipe(
         boundary = successful Core completion after r,
         reads = final ProverView + retained_state,
         emits = no verifier-visible value,
         exports = DerivedWitnessExport(W_out))
```

This is a candidate `ConservativeExtension`, not a durable definition on this
page.

### 4.4 Relations grounding

One `RelationTransform` has two input Interfaces, parameters
`[T_bar,r]`, and one output Interface. `ReductionMeaningBinding` orders input
occurrences exactly `[U_1 occurrence,U_2 occurrence]`, binds `T_bar` as the
publication whose next challenge is `r`, binds `r` as the required Challenge,
and maps the only output to the exact `ReductionOutput` claim occurrence.

At a qualified run, grounding requires:

```text
DerivedPublicOutput(transform,U_1_occ,U_2_occ,T_bar_occ,r_occ)
  = RelationInstanceValue(U_out_occ)

PlanCompletionExport(W_out_occ)
  is the confidential witness occurrence paired with U_out_occ
```

Forward satisfaction preservation is a separate
`RelationRefinementQuestion`; knowledge soundness and extraction are Analysis.
No structural binding asserts either.

### 4.5 Fiat--Shamir delta

Nova Construction 2 computes `r = rho(vk,U_1,U_2,T_bar)` and derives `vk`
from public parameters and the relation structure. This is compatible in shape
with the target's stronger typed framing, provided the exact target
construction absorbs every Statement field, all public setup/context fields,
the typed `T_bar` occurrence, domain and purpose headers, and length/type
framing before deriving `r`. The paper tuple is not by itself the target
framing profile, and hash instantiation is not theorem transport.

### 4.6 Classification

**Primary classification: `ConservativeExtension`, achieved depth T2.** The
flat Core and Relations transform are native; exact post-final-Challenge
private witness evolution requires one narrow Plan completion facility.

## 5. Corrected cycle-based Nova

### 5.1 Why this is a separate variant

The corrected source operates a pair of augmented R1CS systems over a curve
cycle. Each circuit performs its local computation, verifies/folds the
opposite-side committed instance, preserves the initial input, and advances
the step index. The former organization could establish local satisfaction
without establishing that the fresh occurrence had actually been incorporated
into the continuing running occurrence. The correction changes proof-state
and hash linkage; it is not a performance-only profile.

### 5.2 Exact non-base prover schedule

Fix exactly one transition index `i >= 1`, two fields/curves, two augmented
relations `R1CS^(1),R1CS^(2)`, and the corrected input proof state

```text
pi_i = (
  (u_i^(2), w_i^(2)),
  (U_i^(1), W_i^(1)),
  (U_i^(2), W_i^(2))
)
```

together with the source transition coordinates, auxiliary inputs, folding
keys, and `vk`. In particular, the corrected prover does **not** receive a
same-index strict pair `(u_i^(1),w_i^(1))`. The frozen Section 5.3 non-base
prover has this exact five-stage order:

```text
1. Fold the retained strict side-2 pair into the side-2 running pair:
     FoldP(pk, (u_i^(2),w_i^(2)), (U_i^(2),W_i^(2)))
       -> T_i^(2), (U_(i+1)^(2),W_(i+1)^(2)).

2. Construct the new strict side-1 pair (u_(i+1)^(1),w_(i+1)^(1)).
   Its relation witness includes U_i^(2), u_i^(2), and T_i^(2), and its
   second hash coordinate binds U_(i+1)^(2).

3. Fold that new side-1 pair into the prior side-1 running pair:
     FoldP(pk, (u_(i+1)^(1),w_(i+1)^(1)), (U_i^(1),W_i^(1)))
       -> T_i^(1), (U_(i+1)^(1),W_(i+1)^(1)).

4. Construct the new retained strict side-2 pair
   (u_(i+1)^(2),w_(i+1)^(2)). Its relation witness includes U_i^(1),
   u_(i+1)^(1), and T_i^(1), and its second hash coordinate binds
   U_(i+1)^(1).

5. Output the next proof state:
     pi_(i+1) = (
       (u_(i+1)^(2),w_(i+1)^(2)),
       (U_(i+1)^(1),W_(i+1)^(1)),
       (U_(i+1)^(2),W_(i+1)^(2))
     ).
```

The corresponding occurrence graph is therefore sequential rather than two
parallel folds over two same-index fresh pairs:

```text
u_i^(2) + U_i^(2) --fold f_2--> U_(i+1)^(2)
    --construct and hash-bind--> u_(i+1)^(1)

u_(i+1)^(1) + U_i^(1) --fold f_1--> U_(i+1)^(1)
    --construct and hash-bind--> retained u_(i+1)^(2)
```

Each output proof-state occurrence has an explicit recurrence correspondence
to the matching input occurrence of the next member. The edge preserves
causal occurrence identity; it does not equate two claims merely because their
public values compare equal.

This schedule changes the completion analysis. The side-2 running witness is
available before the later side-1 construction/fold decision, and the side-1
running witness is available before the genuine final construction of the
retained side-2 pair. The final construction also owns
`w_(i+1)^(2)`. Ordinary decision-local recipes can therefore retain and export
the three next-state witnesses; this source schedule does not independently
force terminal Plan completion. An exact target Core/Plan elaboration must
still choose the public occurrence boundary for the internally composed
noninteractive folds and close all identities, framing, and bounds. This page
does not yet provide that unique complete encoding.

### 5.3 Required negative mutation

Delete either true fold edge (`u_i^(2)` into `U_i^(2)`, or
`u_(i+1)^(1)` into `U_i^(1)`), or reintroduce the omitted independent
same-index `u_i^(1)` in place of the constructed-and-hash-linked
`u_(i+1)^(1)`. Local relation satisfaction may remain true while the intended
IVC transition is no longer formable. `ClaimReductionShape`, output grounding,
hash linkage, and the step-to-step occurrence correspondence must reject or
leave the Analysis goal unsupported; they must not infer inclusion from
component satisfaction.

The source further stresses that a Nova IVC proof can be malleable despite
knowledge soundness. Non-malleability is a separate Analysis/endpoint property,
not a subtype of folding correctness or knowledge soundness.

### 5.4 Classification

**Primary classification: `Native`, achieved depth T1 as a source-grounded
constructive mapping.** The corrected sequential claim/reduction organization,
hash linkage, recurrence, and ordinary decision-local private exports fit the
existing owners. Promotion to T2 requires one unique, completely enumerated
target Core/Plan encoding of the internally composed noninteractive folds.
The former unlinked organization is **structurally representable, at T1**, but
receives a qualified `Negative` disposition for the IVC-transition and theorem
claim: component satisfaction omits the causal fresh-to-running fold required
by that claim. Target admission must not repair the missing premise by
inference. This is a failed qualified proposition about that organization, not
a failure of the primary IR to express its components.

## 6. HyperNova multi-folding

### 6.1 Exact finite member

Fix finite `mu,nu >= 1`, one CCS structure, `mu` ordered LCCCS running
instances `U_1..U_mu`, `nu` ordered fresh CCS instances `u_1..u_nu`, a finite
`s=log_2(m)`-round Sumcheck profile for the cross-instance polynomial, and all
exact commitment/field algorithms.

```text
HyperNovaMember(mu,nu,s) = {
  inputs: FixedSeq<LCCCSInstance,mu>
          + FixedSeq<CCCSInstance,nu>
  private_inputs: matching ordered witness sequences
  gamma : F
  beta  : FixedSeq<F,s>
  sumcheck messages/challenges: exact finite alternating sequence
  sigma_theta : exact source evaluation publication record
  rho : F
  output: one LCCCSInstance and one private LCCCSWitness
}
```

The Core is one flat execution:

```text
bind all U_i and u_j as ordered Statements and initial claims
one verifier FreshChallenge occurrence outputs the record (gamma,beta),
  where gamma in F and beta in F^s
for q = 1..s:
    Prover Message sumcheck_poly_q
    Verifier Check degree/consistency_q
    Verifier Challenge r_q
Prover Message sigma_theta
Verifier Check final reduced equation
Verifier Challenge rho
Reduction R_multifold consumes every ordered input claim
Reduction R_multifold produces one LCCCS output claim
terminal
```

The completed Sumcheck challenge vector is the source's `r_x'`; it is not an
extra pre-Sumcheck verifier message. The required strict-T2 invariant would be
the complete source order, every published polynomial/evaluation before its
dependent coin, and one fully enumerated flat schedule. This record fixes that
architecture at T1, but does not enumerate enough of the finite member to
claim the strict-T2 invariant. Sumcheck is a nested mathematical reduction
organization, not a child Protocol executed at runtime.

### 6.2 Transform, Plan, and resources

One n-ary `RelationTransform` consumes the ordered `mu+nu` instance
occurrences and produces one LCCCS instance occurrence. Its exact parameter
sequence contains every transform-relevant source publication and Challenge,
including the complete Sumcheck transcript and final `rho`. The
`ReductionMeaningBinding` is total, order-preserving, and extra-free.

The honest Plan derives all Sumcheck publications at their ordinary public
decision points. After the final `rho`, it derives the new private LCCCS
witness, but emits no further public message. It therefore uses the same
candidate completion recipe as Nova. The finite member fixes `mu`, `nu`, `s`,
all message degrees, vector lengths, maximum rejection attempts, and portable
algorithm limits. Claims over unbounded CCS size, iteration count, or NIVC
depth are Analysis families, not one Core.

### 6.3 Source and target Fiat--Shamir profiles

HyperNova Construction 5 initializes `h_s = H(pp,s)` and advances coins as
`r_(i+1)=H(m_i,r_i)`; it does not bind the input instance sequence. The target
requires every Statement, including all running and fresh instances, to be
absorbed before the first dependent Challenge. Therefore four objects remain
distinct:

1. the paper-faithful interactive multi-fold protocol;
2. the exact source noninteractive transform;
3. a target-strong-FS sibling with typed absorption of all input instances;
4. a separate Analysis question asking whether any source theorem applies to
   that strengthened transform.

The target cannot label object 2 strong-FS, and object 4 cannot be affirmed by
structural similarity.

### 6.4 Classification

**Interactive and target-strong-FS HyperNova primary classification:
`ConservativeExtension`, achieved depth T1.** The source-grounded member is
sufficient to expose the Plan-completion pressure and to show that the target-
strong transcript sibling is structurally formable. Strict T2 still requires
one exact finite member with every message polynomial, equation, grounding,
Plan DAG, identity input, codec/framing choice, and resource bound enumerated.
The strengthened sibling's theorem basis remains open.

**Exact Construction-5 source-FS variant primary classification:
`ConservativeExtension`, achieved depth T1.** It is representable as a
separately named weaker transcript construction and has the same Plan-
completion pressure. A request to admit that exact source construction as the
target strong-binding profile receives an exact qualified policy `Negative`,
and source-to-strengthened theorem transport remains unsupported, because its
prefix omits the input Statements. Those dispositions do not make the source
construction unrepresentable.

### 6.5 Finite NIVC state

For a fixed finite function family of size `L`, a NIVC member carries an
ordered vector of `L` running accumulator occurrences and a program counter.
One step consumes the complete old vector plus one fresh claim and produces a
complete new vector: the selected lane is a fold output and every other lane
is a newly produced copy occurrence linked to its predecessor. Dynamic claim
selection is unnecessary. `L` and the one-step schedule are finite Core
bounds; arbitrary execution depth and induction are Analysis.

## 7. CycleFold

### 7.1 Semantic companion state

CycleFold changes the relation family to include both the primary LCCCS state
and a committed relaxed-R1CS state for the small curve-operation circuit. For
the frozen `mu=nu=1` representative:

```text
input relation family  R_1 = R_LCCCS x R_CRR1CS
fresh relation family  R_2 = R_CCCS

inputs:
  primary running LCCCS occurrence
  companion running CRR1CS occurrence
  fresh CCS occurrence

outputs:
  evolved primary LCCCS occurrence
  evolved companion CRR1CS occurrence
```

The verifier circuit takes the public I/O and committed witness instance for
the small native-field elliptic-curve circuit, checks its inputs against the
desired scalar-multiplication/addition inputs, consumes its claimed output,
and folds that circuit instance into the companion running instance.

### 7.2 Core and Relations mapping

The flat Core interleaves the primary HyperNova schedule with the exact Nova
fold used for the companion instance. It includes the companion publication,
Challenge, public output checks, and two output claims. One multi-output
Relations transform or two explicitly linked transforms binds every ordered
input, publication, Challenge, and output occurrence. The choice between
those two encodings is a later falsification question; neither may place the
companion accumulator in Plan/Realization, because it is verifier-observable
semantic state.

The two private outputs have different causal cut points. The primary LCCCS
witness `tilde_w_1 + rho*tilde_w_2` is fixed after the primary challenge
`rho` at source step 6. Genuine later prover publications occur at steps 7 and
9, so an
ordinary decision recipe can retain and export that witness. The companion
CRR1CS witness `(E1 + rho_star*T, W1 + rho_star*W2)` depends on the final
`rho_star` at step 10, and Construction 7 has no later public prover event.
Only that companion witness therefore requires Plan completion. A single
completion recipe may re-export the already retained primary witness together
with the companion witness for atomic downstream use, but it must not claim
that the primary witness newly depends on `rho_star`. Finite bounds include
Sumcheck rounds, companion-circuit dimensions, both commitment vector lengths,
and both challenge domains.

### 7.3 Classification

**Primary classification: `ConservativeExtension`, achieved depth T1 as a
source-grounded constructive mapping.** The existing multi-output
claim/reduction and Relations vocabulary can retain the companion accumulator
semantically. Plan completion is required only for the companion private
witness. A unique complete Core/Plan encoding, including the selected atomic
versus linked-transform representation, remains open before T2. Treating the
companion state as backend-only is a rejected semantic-loss workaround.

## 8. ProtoStar accumulation

### 8.1 Construction stages that must not collapse

For a fixed `(2k-1)`-move special-sound protocol with an algebraic verifier
checking `ell` degree-`d` equations, preserve this order:

```text
special-sound protocol
  -> commit-and-open protocol
  -> FS NARK under rho_NARK
  -> relaxed verifier-predicate accumulator
  -> accumulation under independent rho_acc
  -> separate decider
  -> optional external accumulation-to-IVC compiler
```

The source-grounded member schema fixes `k>=2`, `d>=2`, `ell>=1`, exact
message and commitment types, a binding homomorphic commitment profile, and
all field/hash codecs. For the smallest representative use `k=2,d=2` while
retaining the generic fixed-dimension schema. This page has not yet selected
and enumerated one unique fully closed target member from that schema.

### 8.2 Typed public and private objects

```text
NARK public instance:
  statement pi
  message commitments C_1..C_k

NARK private witness:
  prover messages m_1..m_k and openings

Accumulator public instance acc.x:
  pi', C'_1..C'_k, r'_1..r'_(k-1), E, mu

Accumulator private witness acc.w:
  m'_1..m'_k and exact openings required by the commitment profile

Accumulation proof:
  correction commitments E_1..E_(d-1)
```

The source presentation sometimes suppresses commitment randomness. An exact
target commitment-opening profile cannot invent it. If the frozen source does
not specify the randomness evolution needed by the selected hiding commitment
profile, that private-opening coordinate is T1/`Undetermined`; alternatively
select an exact deterministic or source-specified commitment profile. This
does not weaken the public accumulation mapping.

### 8.3 Separate Core schedules

The special-sound/FNARK Core is:

```text
bind Statement pi
for i = 1..k-1:
  Prover Message C_i
  Verifier Challenge r_i under rho_NARK in the FS sibling
Prover Message final package (C_k, openings required by commit-and-open)
Verifier checks openings and V_sps = 0
terminal
```

The accumulation Core is a distinct Protocol/application domain. Preserve the
source algorithm's causal order even if one endpoint packages both prover
outputs in one noninteractive byte string:

```text
bind Statements: pi, NARK public instance, old acc.x
initial claims: C_nark, C_old_acc

Prover Message pf = [E_j]_(j=1..d-1)
Verifier reconstructs r_i using rho_NARK from (pi,C_i)
Verifier Challenge alpha using
  rho_acc(old acc.x, pi, NARK public instance, pf)
Prover Message acc'.x = the new public accumulator instance
Verifier checks:
  public linear-combination coordinates of acc'.x
  E' = E + sum_j alpha^j E_j
Reduction consumes C_nark and C_old_acc, produces C_new_acc
terminal
```

`rho_NARK` and `rho_acc` are different transcript domains with different
Statements and purposes. They are not flattened into one transcript state.
Their relationship is a typed checked correspondence across the two admitted
Protocols.

The honest accumulation Plan computes the correction vectors and commitments
before `alpha`, retains their private openings, then after `alpha` computes
both the new public accumulator `acc'.x` and its private witness `acc'.w`.
Unlike Nova and HyperNova, the source accumulation prover explicitly outputs
`acc'.x`. The target therefore retains it as a genuine post-Challenge
record-valued Prover Message. The same ordinary decision recipe can publish
`acc'.x` and export `acc'.w`; no completion recipe is required. Replacing this
publication with a verifier-derived value is a possible checked refinement,
not the source-faithful primary mapping.

### 8.4 Relations and decider separation

The accumulation `RelationTransform` consumes the NARK-instance occurrence and
old-accumulator occurrence, binds every correction commitment plus `alpha`,
and produces the exact new-accumulator claim occurrence. Run grounding checks
the public equations against the post-Challenge `acc'.x` publication. A
separate confidential Plan-witness edge binds the ordinary decision export to
`acc'.w`.

The decider is a different Protocol or exact Relations satisfaction operation:

```text
for every i: C_i = Commit(m_i)
e = sum_(j=0)^d mu^(d-j) f_j^V(pi,m_1..m_k,r_1..r_(k-1))
E = Commit(e)
```

`Vacc` acceptance says that public accumulator evolution is consistent.
`D(acc)` acceptance says that one accumulator has a valid private opening and
relaxed verifier predicate. Original-relation acceptance additionally relies
on the commit-and-open/FS NARK and accumulation theorems. None implies another
by Core typing.

The BCLMS accumulation-to-IVC theorem cited by ProtoStar is an imported
compiler result and belongs to the later recursive-verifier case. Outsourcing
the decider changes continuation properties and is not an invisible endpoint
optimization.

### 8.5 Classification

**Primary classification: `Native`, achieved depth T1 for the public
accumulation member.** Flat Core, two Protocol domains, the post-`alpha`
accumulator publication, its decision-local private export, Relations
transform, and separate decider fit existing owners. Exact hiding-commitment
opening evolution is **`Undetermined` at T1** when the source omits randomness
coordinates; this is a subordinate profile result, not a second primary case
classification. T2 additionally requires one exact finite target member with
complete owner, identity, schedule, Plan, Interface/OIR, failure, and resource
tables rather than the generic fixed-dimension schema used here.

## 9. Complete qualified failure partition

The mappings retain owner-qualified outcomes rather than one Boolean reject.

| Boundary | Representative disposition |
|---|---|
| malformed dimensions, noncanonical field/group encoding, wrong sequence length, bad reference | `Malformed` |
| wrong owner kind, relation Interface, challenge type, transcript domain, or cross-regime value | `KindMismatch` |
| missing source PDF/preimage, module, profile, setup, transform, or exact algorithm | `MissingDependency` |
| source construction omits required opening/randomness or theorem premise | `CannotAnswer` or case-level `Undetermined` |
| exact source transcript is intentionally outside target strong-FS family | `Unsupported` |
| missing/extra/reordered input claim, publication, Challenge, output, recurrence edge, or witness edge | completed `Negative` with exact disagreement |
| failed public fold/accumulation/decider equation | Protocol `Reject` plus a negative run-grounding result where asked |
| failed challenge sampling | Protocol `Abort`, not reject or theorem failure |
| unavailable private witness/randomness or failure to produce a legal Plan move | `StrategyStopped` with a partial Core record and no terminal; a later completion-only failure leaves the accepted Core run intact but emits no Plan export |
| portable evaluation or finite transition limit exhausted | `DeterministicLimitExceeded` |
| evaluator/checker disagreement | `CheckerFailure` |
| source theorem cited without a valid validation basis | no Analysis judgment; citation remains inert |

An accepting Core record is neither relation satisfaction nor folding,
accumulation, IVC, soundness, knowledge, or zero-knowledge evidence.

## 10. Discriminating mutations

Each mutation distinguishes an architectural candidate rather than merely
making an algebraic equation false.

1. **Nova missing input binding:** omit `U_2` from the FS Statement prefix.
   Source-strong and target-strong profiles reject it.
2. **Nova missing retained randomness:** delete `r_T` before completion.
   Public folding still computes, but exact private opening evolution cannot
   complete.
3. **Artificial final message:** append the folded witness or a unit message
   after `r`. This creates a decision point but changes source interaction and
   proof presentation; reject as source correspondence.
4. **Relations leakage:** pass `r_T` as a public transform parameter. This
   changes confidentiality and owner authority; reject.
5. **Cycle repair deletion:** remove the fresh-to-running fold edge while
   preserving separate component satisfaction. IVC transition formation must
   fail.
6. **HyperNova input permutation:** swap two LCCCS inputs while preserving
   equal types. Ordered transform grounding must fail.
7. **HyperNova weak FS relabel:** admit Construction 5 as target strong-FS.
   Refuse because the Statement sequence is absent from the prefix.
8. **Sumcheck child execution:** replace the flat events with an ambient child
   Protocol callback. Refuse unresolved runtime authority.
9. **CycleFold backend erasure:** remove the companion CRR1CS claim and keep it
   only in Plan. Output-claim and verifier-observation coverage must fail.
10. **NIVC in-place lane:** reuse unchanged accumulator occurrence identities
    rather than producing linked copies. Occurrence/linearity checking fails.
11. **ProtoStar oracle merge:** derive `alpha` from the `rho_NARK` state without
    the independent accumulation domain. Exact source correspondence fails.
12. **ProtoStar early alpha:** sample `alpha` before correction commitments.
    Last-Challenge publication ordering fails.
13. **ProtoStar output moved before `alpha`:** make `acc'.x` an initial
    Statement or pre-`alpha` publication. Its value depends on `alpha`; Plan
    causality and source correspondence must reject the mutation.
14. **ProtoStar decider conflation:** treat `Vacc=true` as `D(acc')=true`.
    Owner/question kind mismatch or missing premise prevents the judgment.
15. **Equal-value collapse:** deduplicate old and new accumulator occurrences
    when their values happen to agree. Causal output grounding fails.
16. **Unbounded Core:** encode arbitrary IVC depth as a loop. Core formation
    refuses; depth belongs to a finite family plus Analysis induction.

## 11. Resource ledger

Every concrete member fixes, in identity or an exact admitted dependency:

- field and group types, modulus and canonical encodings;
- all matrix/circuit/CCS dimensions and sparsity bounds;
- input/output claim counts and exact occurrence order;
- message, challenge, polynomial, vector, and commitment lengths;
- Sumcheck round count and per-round degree;
- challenge decoding, rejection limits, and failure effects;
- portable algorithm evaluation limits and Core transition limits;
- Plan state size, private randomness count, and completion output type; and
- transcript framing, domain, purpose, and application separation.

One member does not claim a uniform bound over relation size, branching-family
size, IVC/NIVC depth, adversary queries, extractor time, recursive-circuit
size, or decider outsourcing. Those are indexed Analysis families with exact
hypotheses.

## 12. Classification table

| Case or exact variant | Primary classification | Depth | Reason |
|---|---|---:|---|
| Nova committed relaxed-R1CS fold | `ConservativeExtension` | T2 | Native public fold; missing private completion after final coin |
| corrected two-cycle Nova step | `Native` | T1 | Sequential fold/construct schedule supplies later ordinary decisions; unique complete target elaboration remains open |
| former unlinked cycle organization | `Native` as a structural organization; qualified IVC-transition `Negative` | T1 | Components are expressible, but component satisfaction omits the required fresh-to-running causal fold |
| HyperNova interactive / target-strong-FS multi-fold | `ConservativeExtension` | T1 | Native n-ary flat-reduction architecture and same Plan gap; exact finite encoding and theorem transport remain open |
| HyperNova Construction-5 exact source FS | `ConservativeExtension`; target-strong policy `Negative` | T1 | The weaker source transcript is expressible, but its prefix omits input Statements required by the target strong-binding profile |
| CycleFold `mu=nu=1` | `ConservativeExtension` | T1 | Only the companion witness has a terminal Plan gap; unique complete target elaboration remains open |
| ProtoStar public accumulation and separate decider | `Native` | T1 | Genuine post-`alpha` accumulator publication supplies an ordinary decision-local private export; exact target member remains open |
| ProtoStar unspecified hiding-opening evolution profile | `Undetermined` | T1 | Source-level randomness coordinates are insufficiently fixed |

The repeated `ConservativeExtension` result was evidence for comparing a single
owner-local Plan lifecycle law across materially different cases. The final
selection and durable absorption are recorded by `architecture-selection.md`
and `convergence-and-promotion.md`; this page remains their source-grounded
case analysis.

## 13. Nonclaims and synthesis disposition

This record establishes no completeness, soundness, knowledge soundness,
special soundness, extraction, zero knowledge, hiding, binding, random-oracle
applicability, standard-model security, IVC/NIVC induction, non-malleability,
recursive composition, implementation conformance, or performance result.
It does not select a concrete hash, curve, commitment, PCS, proving system,
backend, or proof-byte codec.

The package-level co-design and synthesis resolve the architecture questions
raised by this source record:

1. private continuation is legal only at an exact `Accept` terminal, never at
   Reject, Abort, interpretation failure, or strategy stop;
2. terminal reads use a closed constructor-wise guarantee predicate and may
   consume only explicitly retained state;
3. terminal exports enter `PlanWitnessSurface` through a distinct occurrence
   class and require a live confidential Plan-witness view for run grounding;
4. CycleFold retains both semantic outputs, while the choice between atomic
   and linked Relations transforms remains open for the T2 encoding;
5. ProtoStar remains Native for its public accumulation path, while its
   unspecified hiding-opening evolution remains T1 and unresolved;
6. target-strengthened HyperNova FS is structurally formable but receives no
   source theorem transport; and
7. verifier-in-circuit recursion is a finite Relations predicate with an
   acyclic setup order, while its concrete strict encoding remains profile
   work.

The selected shared lifecycle is recorded in
[`architecture-selection.md`](architecture-selection.md) and the exact
candidate mechanics in
[`plan-lifecycle-codesign.md`](plan-lifecycle-codesign.md). This page remains
the source-grounded comparative record rather than the durable owner.
