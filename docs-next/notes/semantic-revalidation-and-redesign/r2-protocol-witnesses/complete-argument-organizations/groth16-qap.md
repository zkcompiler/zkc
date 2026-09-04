# Groth16 over a Quadratic Arithmetic Program

> **Portfolio case:** Groth16/QAP preprocessing SNARK
> **Depth:** T2 constructive encoding
> **Result:** `Native`; a reusable minimal-verifier Plan lane is a separate
> deferred lifecycle candidate
> **Authority:** Source-grounded temporary research, not an implementation or
> theorem reproduction

## 1. Source lock

The primary sources are:

1. Jens Groth,
   [On the Size of Pairing-based Non-interactive Arguments](https://eprint.iacr.org/2016/260),
   archive revision `20160531:125532`, PDF SHA-256
   `118495898ae6931ec1908134955df3414c8b145743aec01446bfd66b7fdb311c`;
   and
2. Gennaro, Gentry, Parno, and Raykova,
   [Quadratic Span Programs and Succinct NIZKs without PCPs](https://eprint.iacr.org/2012/215),
   archive revision `20120618:223711`, PDF SHA-256
   `ae34d24bf5f345781224e49d87ea89cb71e33dc0c58e75bc5c4228aefef862b7`.

For encoding pressure only, the study compared arkworks `groth16` at commit
`8f0904a7d7a2c8945bf770bdd3c2081e0be1941a` and zkcrypto `bellman`
at commit `3a1c43b01a89d426842df39b432de979917951e6`.
Those implementations help separate key views, prepared verification, proof
field order, and public-input conventions. They do not replace the papers as
semantic sources.

## 2. Relation

For one bilinear group family and QAP, the public statement is
`(a_1,...,a_l)`, the private witness is `(a_(l+1),...,a_m)`, and `a_0=1` is
implicit. Satisfaction requires a bounded quotient polynomial `h(X)` such
that:

```text
(sum_i a_i u_i(X)) * (sum_i a_i v_i(X))
  = sum_i a_i w_i(X) + h(X) * t(X)
```

The exact polynomial sequences, statement/witness partition, coefficient
field, degree bounds, and implicit-one convention belong to
`RelationDefinition`. Circuit-to-QAP or R1CS-to-QAP compilation is a separate
correspondence claim; importing a relation does not prove that reduction.

### 2.1 Selected finite representative

The constructive subject is one exact finite member, not an implicit loop over
all circuits. Write its identity-bearing parameter record as:

```text
G16QAPMember = {
  pairing_suite: exact admitted bilinear-group module and field types,
  l: Natural,
  m: Natural,
  n: Natural,
  u: FixedSeq<m+1, Polynomial<F, degree < n>>,
  v: FixedSeq<m+1, Polynomial<F, degree < n>>,
  w: FixedSeq<m+1, Polynomial<F, degree < n>>,
  t: Polynomial<F, degree = n>,
  quotient_degree_bound: n-2,
  public_crs_type: finite canonical record type,
  proof_type: Record{A:G1,B:G2,C:G1}
}
```

Formation requires `0 <= l <= m`, `n >= 2`, the written sequence lengths and
degree bounds, and exact type agreement with the pairing suite. The selected
member fixes concrete canonical values for every field above before any owner
identity forms. `l`, `m`, `n`, polynomial coefficients, group profile, and CRS
schema are therefore static finite data, not runtime dimensions or evaluator
choices. The record represents an arbitrary exact finite QAP member; it does
not assert that one was correctly compiled from a circuit.

The corresponding relation Interface has exactly `l` public field elements
and `m-l` private field elements. The public `RelationInstance` supplies every
and only those `l` values. The prover may derive `h` as a recipe intermediate;
`h` is not silently added to the source relation witness or persistent state.

### 2.2 Typed owner and identity ledger

The finite inhabitant uses existing owners and keeps their identities
non-circular:

| Owner object | Exact identity dependency | What it owns |
|---|---|---|
| `RelationDefinition` | admitted QAP language plus the complete canonical `G16QAPMember` payload | QAP predicate and statement/witness partition |
| `RelationInterface` | exact `RelationDefinitionId` plus `l` public and `m-l` witness declarations | typed relation-facing occurrences |
| `RelationInstance` | exact `RelationInterfaceId` plus the total public-value map | one public statement; never witness or CRS |
| `InteractiveCore` | exact declaration modules, typed public-parameter/Statement inputs, pairing algorithm and finite occurrence graph | verifier-observable protocol skeleton |
| `Protocol` | exact `CoreId` plus `Fresh` | the sole challenge interpretation |
| `ProtocolInterface` | exact `ProtocolId`, statement/proof slots, codecs, transport and completion presentation | external invocation and proof package |
| `ProverPlan` | exact `ProtocolId`, two randomness requirements and the finite proof recipe | honest construction dataflow, not relation truth |
| `ProtocolRelationBinding` | exact `ProtocolId`, exact `RelationInterfaceId`, and `l` typed Statement occurrence edges | public-statement correspondence |
| `PlanWitnessBinding` | exact Plan witness-surface coordinates and exact relation witness occurrences | private witness ingress correspondence |

Symbolically, construction and dependency order are:

```text
D   = RelationDefinitionId(G16QAPMember)
RI  = RelationInterfaceId(D, Public[F;l], Witness[F;m-l])
RX  = RelationInstanceId(RI, total_statement_map)
C   = CoreId(statement_types[F;l], setup_input_type,
             proof_type, pairing_check, four_occurrences)
P   = ProtocolId(C, Fresh)
PI  = ProtocolInterfaceId(P, invocation_slots, statement_members,
                          proof_transport, codecs, completion)
PP  = ProverPlanId(P, witness_ingress, randomness[r,s], proof_recipe)
PRB = ProtocolRelationBindingId(P, {RI}, l_statement_edges)
PWS = PlanWitnessSurfaceId(PP's checked extracted witness surface)
PWB = PlanWitnessBindingId(PWS, RI, m-l_witness_edges)
```

`RX` is used by run-grounding and Analysis; it is deliberately absent from
`C`, `P`, `PI`, and `PP`. `PRB` depends on `P` and `RI`, never on Interface or
Plan. `PWB` depends on the normalized `PWS`, not on a relation back-reference
inside Plan. This preserves the existing cycle-free authority directions.

For one run, Interface assignment first supplies the exact `l` external
statement values and setup value to the Core invocation. `StatementCoverage`
checks the Interface presentation; the Relations run-grounding question then
compares every `PRB` edge against `RX` and the owner-issued Protocol run view.
`PlanRealizes` independently checks the sole proof recipe against the Core
decision view, and `PWB` independently checks the witness-surface edges. None
of these judgments implies another, relation satisfaction, or theorem
applicability.

Consequently a QAP change rotates `RelationDefinitionId` and its dependent
Relations subjects. A Core schedule or pairing-check change rotates `CoreId`
and then `ProtocolId`, Interface, Plan, and bindings. A proof codec change
rotates `ProtocolInterfaceId`, not `CoreId`. Runtime statement and CRS values
belong to invocation/run identities, not `CoreId`. In the setup-specialized
Plan control below, changing the embedded proving projection additionally
rotates `ProverPlanId`.

## 3. Setup and construction graph

Groth16 setup is relation-specific. Deployments commonly expose:

- a public proving key containing material used to construct proofs;
- a public verification key containing material read by the verifier; and
- setup trapdoor material that must not become a protocol or Plan input.

The formal source gives one public CRS to both prover and verifier. A bounded
source-faithful encoding can therefore expose that complete CRS as a Core
`PublicParameter`, and a setup-specialized Plan can embed a fixed value. P07 is
not blocked without new grammar.

The exact constructive graph has two native controls. Neither introduces a
setup-result root.

### 3.1 Full-CRS/Core control

This is the primary source-level organization. One finite canonical full CRS
value `sigma` is supplied as a Core `PublicParameter`. Its Statement-independent
verifier projection is computed by an exact admitted derived algorithm. At the
single prover decision, the Plan reads the already opened `sigma` binding and
uses its exact proving projection. Thus one invocation value is the common
origin visible to both uses:

```text
RelationDefinition(QAP) --ProtocolRelationBinding--> Statement bindings

CoreInvocation(statement, sigma)
        |                  |
        |                  +--> exact verifier projection --> pairing check
        |
        +--OpenedBinding---> ProverPlan
                               + witness through PlanWitnessBinding
                               + private randomness r,s
                               + exact proving projection of sigma
                               `--> proof {A,B,C}
```

This control is `Native`: it uses an existing public binding and an existing
Plan read, and preserves the paper's common public CRS. It may expose more
public material at the verifier boundary than a minimal implementation API,
but it invents neither a protocol message nor semantic authority.

### 3.2 Setup-specialized Plan control

The second native control fixes the proving projection as a Plan recipe
`Constant`, while Core receives only the finite verification projection as a
`PublicParameter`:

```text
RelationDefinition(QAP)
          |
          | setup-correspondence premise in Analysis/Evidence
          |
          +--------------------------+
                                     |
                         public proving material
                                     |
                                     v
Relation witness -----------> ProverPlan + private randomness r,s
                                     |
                                     v
                               proof {A,B,C}

statement + public verification key
                 |
                 v
          CoreInvocation ---> pairing check ---> verdict
```

The verification projection is a Core `PublicParameter` because it changes
verifier behavior. Embedding the fixed proving projection rotates
`ProverPlanId`; it is therefore suitable for a setup-specialized finite member,
not a reusable runtime-parametric prover API. The trapdoor is neither Core nor
Plan input.

For both controls, the following remain explicit grounding obligations rather
than new root objects:

1. the public CRS or PK/VK projections have the exact source-required types
   and lengths for the selected QAP;
2. the proving and verifying projections are derived from one setup for that
   exact `RelationDefinition`;
3. the verifier projection used by Core and proving projection used by Plan
   are the corresponding views of that setup; and
4. any prepared verifier representation is the result of an exact checked
   derivation from that projection.

The full-CRS control witnesses common origin structurally at the invocation
value level, but it still does not establish honest setup or relation
specialization. The setup-specialized control needs an Analysis/Evidence
premise for both common origin and specialization. In neither case may equal
labels, equal digests, or well-typed keys substitute for those propositions.

This is a lifecycle and substitution choice, not a claim that the paper
requires separate key APIs. The full-CRS/Core and setup-specialized Plan
controls are the selected native encodings. A reusable minimal-verifier Plan
that accepts a different proving projection at each invocation would use the
deferred `PublicProverParameterDecl`; that lifecycle convenience is not needed
for P07's primary classification.

This package does not add a universal setup-result root. A canonical key value
cannot prove honest setup, common origin, trapdoor destruction, or relation
specialization. Those propositions belong to scheme-specific Analysis profiles
and Evidence. A later portable setup constructor may be added when an actual
consumer needs to identify and check one; Groth16 expressibility does not by
itself justify that authority.

## 4. Exact Core

Groth16 is noninteractive by construction. The faithful Core has no verifier
challenge:

```text
root scope:
  bind exactly l Statement public inputs
  bind full CRS or verification projection as PublicParameter

  ProverMessage({ A : G1, B : G2, C : G1 })

  InvokeCheck(pairing_product_equation)

  guarded Accept requiring the check output true
  unconditional final Reject fallback
```

The pairing predicate is semantically:

```text
e(A,B)
  = e(alpha,beta)
    * e(IC(statement),gamma)
    * e(C,delta)
```

where `IC` is the exact verification-key linear combination including the
implicit constant term. A profile may rearrange this into one multi-pairing
equation with prepared or negated elements, but the rearrangement needs exact
typed correspondence. It is not another protocol.

One ProverMessage is source-faithful. Splitting `A`, `B`, and `C` into scheduled
messages would invent rounds with no verifier action between them.

The exact occurrence sequence contains four occurrences: one
`ProverMessage`, one `InvokeCheck`, one guarded `ReachTerminal(Accept)`, and one
unconditional `ReachTerminal(Reject)`. It contains zero Challenge,
VerifierMessage, Oracle, Claim, and Reduction occurrences. The check reads
only the `l` Statement values, the public setup binding or its exact verifier
projection, and the proof record. There is one prover decision point and no
persistent Plan state is required.

## 5. Challenge interpretation

The Core has one Fresh Protocol. Because there are no challenge occurrences,
the Fresh resolver is never called. The tag is vacuous but canonical; adding a
`Direct` or `Native` tag would create a behaviorally duplicate Protocol ID.

The earlier canonical-framed FS grammar could also form a construction with an
empty challenge-rule map. Such a resolver still initializes and absorbs
headers, bindings, and prover messages, adding resource and noncompletion
surface, but it transforms no challenge and its state cannot resolve one. That
work has no `ChallengeInterpretation` target and must not create an FS sibling.
Proof hashing for transport or audit belongs to Interface/OIR or Evidence.

The package therefore selects the shared admission law:

```text
canonical-framed TranscriptConstruction requires
  at least one Core Challenge occurrence
```

This is identity hygiene, not a cryptographic claim. It leaves zero-challenge
Cores and their Fresh Protocols valid.

## 6. Plan

The honest prover:

1. receives the relation witness and the public proving key;
2. samples private field elements `r` and `s` without a nonzero requirement;
3. constructs the QAP quotient under the exact source degree law; and
4. produces `A:G1`, `B:G2`, and `C:G1`.

The witness enters through the Relations-to-Plan witness binding. `r` and `s`
are Plan private randomness. The paper's formal full public CRS may enter Core
as a `PublicParameter`; Plan can read that admitted value through
`OpenedBinding`. A setup-specialized Plan may instead embed one fixed proving
projection as a recipe `Constant`, validly rotating `ProverPlanId`. Both are
native controls.

The constructive recipe is a finite acyclic graph with exact typed stages:

```text
Opened Statement + WitnessIngress
  -> QAP numerator and exact quotient h
Opened full CRS or embedded proving projection + r
  -> A:G1
Opened full CRS or embedded proving projection + s
  -> B:G2
all preceding values + r + s
  -> C:G1
{A,B,C}
  -> MessageValue at the sole ProverDecisionPoint
```

Each mathematically partial algebraic operation uses a total tagged result;
only its success payload may feed the proof record. No opaque host callback
supplies `h` or a proof. Failure to construct an exact quotient or to evaluate
within the admitted contract means the honest strategy supplies no legal move.
It is not verifier `Reject` and does not establish that the relation is
unsatisfied.

Requiring `r,s != 0`, deriving them from a transcript, or exposing them would
change the source. A future `PublicProverParameterDecl` would improve only the
reusable, minimal-verifier organization: it would declare the public proving
projection's runtime Plan role without putting that projection into Core or
hard-coding its value in the Plan identity. That lane is deferred to the next
Plan co-design and is not required for source expressibility.

## 7. Interface and OIR package

The semantic message is one typed record with roles `{A:G1,B:G2,C:G1}`.
Interface/OIR owns:

- the external proof slot and byte layout;
- canonical group encoding and subgroup checks;
- statement ordering and arity;
- conversion to the semantic record; and
- malformed-input refusal before Core execution.

The paper's textual tuple order and common library field order differ. That is
precisely why physical order cannot define semantic roles.

Malformed encodings, wrong groups, subgroup failures, and arity mismatches are
Interface/OIR failures. A well-formed proof with a false pairing equation
reaches the Core and yields `Reject`. Missing pairing support is `Unsupported`.

The commitment-opening verifier profile is inapplicable. Groth16 exposes no
verifier query and asserted opening answer; dummy claim fields would falsify
the source shape.

## 8. Construction, execution, and failure ledger

| Boundary | Exact condition | Outcome |
|---|---|---|
| Relation formation | malformed QAP dimensions, coefficient types, lengths, or degree bounds | `Malformed`, `KindMismatch`, or `Refused` before protocol use |
| Core/Plan admission | wrong algorithm ABI, unavailable read, wrong proof type, cyclic recipe, or non-total terminal shape | admission refusal |
| Invocation/Interface | missing or extra Statement/CRS slot, invalid proof framing, noncanonical point, wrong group, subgroup failure, or wrong arity | Interface/OIR `Malformed` or `Refused`; Core does not run |
| Capability | pairing/QAP primitive or evaluator profile unavailable | `Unsupported` |
| Honest construction | missing witness/material, exact division failure, randomness failure, or no legal recipe result | strategy `Stop`; no terminal result |
| Bounded evaluation | any admitted algorithm or codec exhausts its declared bound | `DeterministicLimitExceeded`; never Boolean false |
| Verification | every input is formed but the pairing predicate is false | Core `Reject` |
| Verification | pairing predicate is true | Core `Accept` at the guarded terminal |
| Setup/theorem evidence | specialization, common-origin, ceremony, or theorem premise absent | Analysis cannot affirm; Core result is unchanged |

Source `Setup` and `Prove` are probabilistic algorithms, not new interactive
phases. This ledger does not invent an `x`-outside-domain failure, nonzero
`r,s` restriction, ceremony status, or trapdoor-destruction result unless a
selected realization profile states one.

## 9. Finite intrinsic resource envelope

For the fixed member `(l,m,n)` every semantic carrier and algorithm has a
finite static bound:

- the relation has `m+1` entries in each of `u`, `v`, and `w`, `l` public
  scalars, `m-l` witness scalars, target degree `n`, and quotient degree at
  most `n-2`;
- Core has `4` occurrences, `1` prover decision, `0` challenges, `1` check,
  `2` terminals, and proof arity exactly `3` group elements;
- the mathematical verifier envelope is at most one `l+1`-term public-input
  multiscalar combination and four pairing terms before an exact admitted
  prepared/multi-pairing rewrite;
- Plan has exactly two scalar-randomness requirements and a finite recipe DAG
  whose polynomial, field, and group-operation limits are functions of the
  fixed `m` and `n`, never proof-supplied loop bounds; and
- the full CRS, projections, Statement, proof record, Interface slots, and all
  intermediate canonical values use finite K1 schemas with explicit sequence,
  byte, node, and nesting bounds.

The exact portable algorithms and codecs bind evaluation contracts whose
limits cover those fixed carriers. Pre-admission checks the contracts before
execution. Exceeding a limit is `DeterministicLimitExceeded` and cannot be
reclassified as rejection, invalid witness, or a larger dynamically admitted
member. These intrinsic bounds establish finite representability only; they do
not establish asymptotic succinctness or implementation cost.

## 10. Negative mutations

The T2 encoding distinguishes at least:

1. add an online verifier challenge or FS squeeze;
2. split the three proof elements into interactive rounds;
3. attach a commitment-opening profile using dummy queries or answers;
4. swap `B` and `C` or erase their group roles;
5. equate wire order with semantic proof roles;
6. omit, reorder, truncate, or extend public inputs;
7. omit the implicit `a_0=1` term;
8. expose witness, setup trapdoor, `r`, or `s`;
9. require nonzero `r,s` or derive them from transcript state;
10. in the candidate minimal-verifier organization, supply the separated
    prover-only projection through private Advice or an extra Core binding;
11. treat malformed/subgroup failure as a false pairing equation;
12. treat a false pairing equation as checker failure;
13. equate prepared and unprepared VK forms without checked derivation;
14. use different projections than the exact full CRS value in the full-CRS
    control;
15. combine an unrelated embedded proving projection and runtime verification
    projection in the setup-specialized control;
16. pair a CRS or VK and relation by label or asserted digest alone;
17. infer relation satisfaction, extraction, zero knowledge, or honest ceremony
    directly from `Accept`; or
18. claim Groth16 support from generic group or pairing primitives.

## 11. Classification and theorem boundary

The verifier-visible path is `Native`: existing messages, exact checks,
bindings, terminals, Interface projection, and Fresh execution suffice. The
fixed/source-level organization is also `Native`, which is the case's one
primary portfolio classification. Separately, the minimal-verifier, setup-
parametric architecture motivates a public prover-parameter class in Plan.
That is a conservative shared lifecycle candidate discovered by the case, not
an expressibility repair forced by the paper and not a second case
classification. Promotion is deferred to the next Plan co-design so dependent
profiles rotate at most once.

The source theorem is interpreted only under its exact model and setup
premises. This record establishes none of:

- standard-model or unrestricted knowledge soundness;
- honest ceremony or toxic-waste destruction;
- circuit/R1CS-to-QAP compiler correctness;
- implementation or serialization conformance;
- subgroup, side-channel, RNG, or curve security;
- batch verification, rerandomization, aggregation, or recursion; or
- repository implementation support.

An accepting Core execution remains distinct from relation satisfaction and
from activation of any Groth16 property judgment.
