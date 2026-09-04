# Bulletproofs Range and Inner-Product Arguments

> **Portfolio case:** Bulletproofs inner-product/range-proof path
> **Depth:** T2 constructive encoding
> **Result:** `Native`
> **Authority:** Source-grounded temporary research, not an implementation or
> security claim

## 1. Source lock

The semantic source is Bünz et al.,
[Bulletproofs: Short Proofs for Confidential Transactions and More](https://eprint.iacr.org/2017/1066),
final ePrint revision dated `2022-04-14`, PDF SHA-256
`2204cf02c3818543adcdd4325b5d4ca205e43d428701300214f198d19e86de61`.

The final revision matters: its Fiat--Shamir discussion includes the public
statement in the transcript and records the earlier omission as an error.

Implementation-profile pressure uses Dalek Bulletproofs commit
`be67b6d5f5ad1c1f54d5511b52e6d645a1313d07`. The paper remains semantic
authority; the implementation comparison exposes generator derivation,
transcript labels, challenge decoding, proof layout, and randomized verifier
aggregation choices.

## 2. Setup and relation

Two setup classes stay distinct:

1. scalar Pedersen bases `B` and `B_blind`; and
2. ordered vector/IPA bases `G_1..G_N`, `H_1..H_N`, and auxiliary base `U`.

The exact public values or a transparent derivation profile are protocol
setup. Independence and absence of known discrete-log relations are Analysis
premises, not Core-admission facts.

The pinned Dalek profile derives `B_blind` by hashing the compressed Ristretto
basepoint with SHA3-512. Its vector bases come from SHAKE256
`"GeneratorsChain"` streams labeled by `"G" || LE32(party_index)` and
`"H" || LE32(party_index)`; aggregation concatenates each party's first `n`
generators. Those choices are exact setup-profile content. They are not the
paper's generic hash-to-group recommendation and do not establish generator
independence by construction.

For `m` ordered commitments and `n` bits, the relation is:

```text
public:
  setup, V_1..V_m, n

private witness:
  (v_1,gamma_1)..(v_m,gamma_m)

predicate:
  V_j = B^v_j * B_blind^gamma_j
  and 0 <= v_j < 2^n
```

The canonical IPA path fixes `N=n*m` as a power of two. Internal vectors,
polynomials, masks, and fold state are Plan state, not extra relation witness.

## 3. Exact finite constructive ledger

### 3.1 One closed member schema

The T2 witness is one exact finite member, not a symbolic loop inside Core:

```text
BPRangeMember(P_group,n,m) requires:
  n,m >= 1
  N = n*m
  N = 2^k for one exact natural k

  Scalar       = P_group.scalar_type
  NonzeroScalar = the exact nonzero challenge domain over Scalar
  GroupElement = P_group.group_element_type

  ScalarPedersenSetup = {B:GroupElement, B_blind:GroupElement}
  IPASetup = {
    G: FixedSeq<GroupElement,N>,
    H: FixedSeq<GroupElement,N>,
    U: GroupElement
  }
  RangeStatement = {
    scalar_setup: ScalarPedersenSetup,
    commitments: FixedSeq<GroupElement,m>,
    n: ExactNatural<n>,
    m: ExactNatural<m>
  }
  RangeWitness = FixedSeq<{v:Scalar,gamma:Scalar},m>

  M_AS       = {A:GroupElement,S:GroupElement}
  M_T        = {T_1:GroupElement,T_2:GroupElement}
  M_response = {t_hat:Scalar,tau_x:Scalar,mu:Scalar}
  M_fold_i   = {L_i:GroupElement,R_i:GroupElement} for i in 1..k
  M_final    = {a:Scalar,b:Scalar}

  y,z,x,w,u_1..u_k : NonzeroScalar
```

The paper profile uses `NonzeroScalar`. A Dalek-compatible scalar-decoding
profile is a different member because it includes zero. Exact group encoding,
subgroup rules, field arithmetic, multiexponentiation, basis folding,
`delta(y,z)`, and the two Boolean check algorithms are authenticated module or
portable-algorithm dependencies; none is an opaque verifier callback.

The relation predicate is over `RangeStatement` and `RangeWitness`. `IPASetup`
is a public protocol parameter, not an extra range witness. The complete
Statement binding retains the ordered commitments and both shape values even
when `m` is also recoverable from the sequence type. This supports the exact
paper/Dalek transcript profiles without relying on `CoreId` as an implicit
replacement for an absorbed field.

### 3.2 Owner objects and acyclic identity dependencies

The following are symbolic constructors for the exact existing owner IDs, not
new portable kinds:

```text
BPArgumentModuleId
  -> claim contracts RangeClaim and IPAClaim(d)
  -> reduction contracts RangeToIPA(N) and IPAFold(d -> d/2)
  -> exact algebra/check algorithm and ValueType dependencies

RangeRelationDefinitionId
  = RelationsId(exact definition-language payload for the typed scalar
                commitment/range predicate)
RangeRelationInterfaceId
  = RelationsId(RangeRelationDefinitionId,
                public and witness occurrence declarations)
RangeRelationSemanticModelId
  = RelationsId(RangeRelationDefinitionId, RangeRelationInterfaceId,
                exact satisfaction evaluator and explicit assumptions)
RangeRelationInstanceId
  = RelationsId(RangeRelationInterfaceId, exact RangeStatement value)
RangePrivateWitnessAssignment
  = one owner-local, nonportable occurrence over
    (RangeRelationInstanceId, exact RangeWitness secret values)

CoreId
  = PIRId(BPArgumentModuleId, public inputs, bindings, values,
          claims, reductions, checks, terminals, total occurrence sequence)

FreshProtocolId = PIRId(CoreId, Fresh)
TranscriptConstructionId
  = PIRFSId(CoreId, exact framing, codecs, domain separation,
            challenge decoder/sampler, bounds)
FSProtocolId = PIRFSId(CoreId, FiatShamir(TranscriptConstructionId))

ProtocolInterfaceId(P)
  = PIRInterfaceId(P, invocation slots, Statement members,
                   transport and completion entries)
ProverPlanId(P)
  = PIRPlanId(P, private material, randomness, state, decision recipes)
PlanWitnessSurfaceId(P)
  = PIR-owned source-ID-free extraction of the exact WitnessIngress entries

ProtocolRelationBindingId(P)
  = RelationsId(P, RangeRelationInterfaceId,
                Statement edges, claim meanings, reduction meanings)
PlanWitnessBindingId(P)
  = RelationsId(PlanWitnessSurfaceId(P), RangeRelationInterfaceId,
                witness occurrence edges)
```

There is one `ProtocolInterfaceId`, `ProverPlanId`, and
`ProtocolRelationBindingId` for each selected Fresh or FS Protocol. The Plan
contains no Relations ID. The base Protocol relation binding contains no
`ProtocolInterfaceId`, Plan, OIR, run, or checked-result ID. The
`PlanWitnessBinding` names the source-ID-free witness surface rather than the
full Plan. These directions preserve the existing cycle break.

Proof bytes and their artifact identity are downstream Interface/OIR objects;
they do not enter `CoreId` or either `ProtocolId`. Analysis goals, semantic
bases, theorem-source validation, and judgments likewise remain separately
identified descendants rather than Core fields.

### 3.3 Exact Core and reduction graph

The flat Core contains the following complete claim graph:

```text
C_range : Linear RangeClaim
  source = InitialClaim(the exact root RangeStatement binding)

R_0 : RangeToIPA(N)
  inputs              = [C_range]
  side inputs         = [setup,A,S,T_1,T_2,t_hat,tau_x,mu]
  required challenges = [y,z,x,w]
  required publications = [
    (M_AS,       next=y),
    (M_T,        next=x),
    (M_response, next=w)
  ]
  outputs = [C_ipa_0 : Linear IPAClaim(N)]

for i = 1..k:
  R_i : IPAFold(N/2^(i-1) -> N/2^i)
    inputs              = [C_ipa_(i-1)]
    side inputs         = [the exact current folded public IPA state,
                           L_i,R_i]
    required challenges = [u_i]
    required publications = [(M_fold_i,next=u_i)]
    outputs = [C_ipa_i : Linear IPAClaim(N/2^i)]

Check_range = exact aggregated polynomial/Pedersen equation
Check_ipa   = exact final unrolled IPA residual over C_ipa_k and M_final

Accept:
  requires Check_range=true and Check_ipa=true
  explicitly disposes C_ipa_k
Reject:
  finite fallback with explicit remaining-claim disposition
```

Thus there are exactly `k+2` claims and `k+1` reductions. The K2 reductions
record structural claim evolution and Last-Challenge publication order; they
do not execute or establish the range-to-IPA or fold theorems. Relations gives
the declarations occurrence-level meanings. Analysis alone may state that
the two checks plus those reductions imply the original range relation.

The source phrase “invoke an inner-product argument” is therefore preserved
without a runtime child Protocol. A reusable authoring template may elaborate
this graph, but authentication sees only the resulting flat Core and one
continuous transcript.

### 3.4 Interface, Plan, and Relations closure

For either exact Protocol `P`, the complete non-Analysis closure is:

```text
ProtocolInterface(P):
  external invocation slots cover every and only the public inputs;
  Statement members expose the exact RangeStatement binding;
  transport entries preserve each typed Core message/challenge occurrence;
  completion entries distinguish Accept, Reject, and FS interpretation
    failure where applicable.

ProverPlan(P):
  WitnessIngress = exactly (v_j,gamma_j) for j=1..m;
  private randomness = alpha,rho,tau_1,tau_2,s_L[1..N],s_R[1..N];
  persistent/private state = bit vectors, l/r/t polynomial state,
    folded bases, folded witnesses, and prior masks;
  one exact decision recipe for every M_AS, M_T, M_response,
    M_fold_i, and M_final decision point;
  each recipe reads only earlier opened bindings, observed challenges,
    prior own moves, witness material, randomness, and explicit state.

ProtocolRelationBinding(P):
  Statement edges map scalar bases, ordered V_j, n, and m;
  claim meanings map C_range and every C_ipa_i;
  reduction meanings map R_0 and every R_i, including the exact side-input,
    challenge, publication, and relation-transform parameter positions.

PlanWitnessBinding(P):
  maps each relation witness occurrence (v_j,gamma_j) to its exact
    source-ID-free WitnessIngress occurrence;
  has no edge for masks, advice, polynomial state, or fold state.
```

The FS and Fresh bindings are distinct because they name distinct
`ProtocolId`s even though their relation Interface and Core are shared. OIR
may package the prover publications into the record in Section 6 only after
preserving these occurrence and transport coordinates.

## 4. Representative schedule

For exact `N=2^k`:

```text
0. bind Statement V_1..V_m,n and public setup

1. ProverMessage(A,S)
2. Challenge(y)
3. Challenge(z)

4. ProverMessage(T_1,T_2)
5. Challenge(x)

6. ProverMessage(t_hat,tau_x,mu)
7. Challenge(w)

8. ApplyReduction RangeToIPA:
     RangeStatementClaim -> IPAClaim(N)

for i = 1..k:
  ProverMessage(L_i,R_i)
  Challenge(u_i)
  ApplyReduction IPAFold_i:
    IPAClaim(N/2^(i-1)) -> IPAClaim(N/2^i)

9. ProverMessage(a,b)
10. InvokeCheck(polynomial equation)
11. InvokeCheck(final IPA residual)
12. Accept iff both checks are true and the final claim is disposed;
    otherwise Reject
```

Required publication/challenge links are exact:

```text
A,S                 < y
T_1,T_2             < x
t_hat,tau_x,mu      < w
each L_i,R_i        < its u_i
```

`y` and `z` are distinct consecutive challenge occurrences. In Fresh they are
independent under their declared coin laws. Under canonical FS, `z` uses the
state after `y`, matching the source schedule rather than pretending both are
one tuple draw.

## 5. Algebraic checks

The range-polynomial check has the shape:

```text
B^t_hat * B_blind^tau_x
  = B^delta(y,z)
    * product_j V_j^(z^(j+1))
    * T_1^x
    * T_2^(x^2)
```

The improved inner-product relation folds vector bases, commitment state, and
witness coordinates under each `u_i`. After the final round, the verifier
checks the exact unrolled residual:

```text
P_initial * product_i L_i^(u_i^2) R_i^(u_i^-2)
  = G^(a*s) * H^(b*s^-1) * (U^w)^(a*b)
```

The exact finite-field/group algorithms and basis-folding profile are owner-
local module content. Core owns the Boolean checks and their data dependencies;
Analysis owns what those equations establish.

### 5.1 Generator, Statement, witness, and run grounding obligations

Structural inhabitance requires all of the following distinct checks; no one
row implies another:

| Grounding question | Exact obligation | Not established |
|---|---|---|
| relation public to Statement | the relation's scalar bases, each ordered `V_j`, `n`, and `m` select the identical typed root Statement occurrences | that any `V_j` has a valid opening |
| whole public coverage | every and only range-relation public occurrence is covered, and every Statement occurrence is separately covered | setup honesty or relation satisfaction |
| IPA public setup | the Core invocation supplies exactly `N` ordered `G_i`, exactly `N` ordered `H_i`, and one `U` under the selected public-parameter profile | independence or unknown discrete logs |
| transparent derivation, if selected | an exact deterministic grounding equation recomputes the ordered bases from the declared seed, labels, and indices | random-oracle quality or collision resistance |
| witness ingress | each `(v_j,gamma_j)` relation occurrence maps to the corresponding typed Plan witness entry | that Plan computation is honest or accepting |
| claim/reduction shape | every range/IPA claim and reduction meaning resolves to the exact K2 source, transform, side inputs, challenges, and complete publication requirements | reduction soundness, completeness, or witness evolution |
| invocation/run grounding | the values used by one completed invocation equal the selected relation and setup occurrences at their exact coordinates | a universal protocol theorem |

The relation predicate itself owns `V_j = B^v_j B_blind^gamma_j` and the range
condition. `A,S,T_1,T_2,L_i,R_i` are protocol publications, not extra relation
public inputs. Internal `a_L,a_R,l,r,t` and their masks are Plan state, not
additional witness occurrences. A multiparty dealer or party partition may
ground an honest producer realization, but it does not change the single
logical Prover or the range relation seen by this Core.

## 6. Proof package and causal order

For `k=log2(N)`, the external proof contains:

```text
A, S, T_1, T_2,
t_hat, tau_x, mu,
(L_1,R_1)..(L_k,R_k),
a, b
```

or `2k+4` group elements and five scalars. Interface/OIR owns the byte record
and codecs. Core owns the causal decomposition into publications around
challenges. Modeling the whole proof blob as one message before all challenges
would destroy Fiat--Shamir meaning.

The corrected source requires the Statement `{V,n}` in initialization. An
application context may add its own exact SessionContext, but neither a label
nor proof bytes substitute for Statement binding.

## 7. Commitment-profile decision

The selected v0 encoding does not attach `CommitmentOpeningUse`.

- Pedersen values, vector commitments, and IPA round elements are mathematical
  commitments but not verifier queries with asserted answers and opening
  evidence.
- The IPA residual is a group relation, not a polynomial opening.
- The outer degree-two polynomial equation can be algebraically factored as a
  small Pedersen polynomial opening, but doing so supplies no missing source
  meaning.

A future exact Pedersen polynomial-opening profile is warranted only if
several independent consumers need that exact verifier boundary. It must not
reclassify the entire Bulletproofs argument as a PCS.

## 8. Finite unrolling and family meaning

Each exact `(setup,n,m)` has a finite, statically known schedule and proof
arity. Flat unrolling is therefore faithful. It does not establish:

- uniform construction for every size;
- polynomial-time prover/verifier behavior;
- logarithmic communication as an asymptotic law; or
- one security theorem for all members.

Those belong to an `AnalysisAsymptoticProtocolFamilyDefinition` with explicit
size and security-parameter schedules, uniform constructors, resource laws,
and pointwise correspondence from a mathematical family member to the exact
admitted finite Core.

### 8.1 Intrinsic finite bounds for the selected member

For one fixed `N=2^k`, the Core/Plan profile derives rather than authors the
following closed structural bounds:

```text
prover message occurrences = k + 4
challenge occurrences      = k + 4
claims                     = k + 2
reduction applications     = k + 1
Boolean checks              = 2
terminal occurrences        = 2
initial scope openings       = 1  // semantic boundary, not an OccurrenceDecl
total Core occurrences      = 3*k + 13

proof group elements        = 2*k + 4
proof scalars               = 5
statement commitments       = m
IPA setup group elements    = 2*N + 1
honest-Plan random scalars  = 2*N + 4
maximum final IPA MSM arity <= 2*N + 2*k + 2
```

The exact canonical byte bounds are derived from the selected fixed-sequence
types and group/scalar codecs. The exact deterministic step bound is the sum
of the authenticated evaluation-contract bounds for every reached derivation,
challenge interpretation, Plan recipe node, and the two check invocations;
no asymptotic notation or caller-supplied “feasible” flag can replace that
sum. The canonical FS profile additionally multiplies its exact per-challenge
maximum draw bound by `k+4`; exhausting that bound produces its typed
interpretation-failure completion rather than a Core `Reject`.

These are finite inhabitance bounds. The formulas `2*k+9` proof elements and
`k=log2(N)` may later support an Analysis communication law only after a
uniform family constructor and exact pointwise correspondence are separately
established.

## 9. Source/implementation deviations

The pinned Dalek transcript is exactly:

```text
"rangeproof v1", n, m,
ordered V_j, A, S, y, z, T_1, T_2, x,
t_x, t_x_blinding, e_blinding, w,
"ipp v1", N,
then L_i, R_i, u_i for i=1..k.
```

Here `t_x_blinding` is `tau_x` and `e_blinding` is `mu`. The verifier permits
an identity `V_j` but rejects identity `A,S,T_1,T_2,L_i,R_i`; it supports
`n` in `{8,16,32,64}` and requires sufficient generator and party capacity.
These are implementation-profile formation/decoding choices, not additions to
the paper relation.

Two deeper Dalek choices must not silently inherit the paper theorem:

1. the paper samples challenges in the nonzero field, while Dalek maps wide
   transcript bytes with `Scalar::from_bytes_mod_order_wide` without rejecting
   zero; and
2. Dalek samples verifier-private randomness to combine the two verification
   equations, adding an approximately `1/p` failure term.

The semantic Core retains the two deterministic equations. A randomized
combination belongs to a distinct realization verifier profile with an exact
equivalence and quantitative-loss obligation. It is not a reason to add
verifier-private influence to a public-coin Core.

## 10. Failure partition

| Condition | Result |
|---|---|
| ill-formed fixed member, non-power-of-two `N`, unresolved reference, invalid proof codec, noncanonical scalar, point, arity, or length | `Malformed` before the proposition/run exists |
| well-typed object from a different semantic profile, group, challenge domain, or reference kind | `KindMismatch` |
| unsupported group/hash/MSM profile | `Unsupported` |
| supported object violating setup capacity, generator count/order, exact `N`, schedule, coverage, or proof-shape admission law | `Refused` |
| canonical FS nonzero sampler exhausts its exact draw bound | typed FS interpretation-failure completion; no Core terminal |
| strategy cannot propose a legal active move or a Plan recipe cannot complete | `StrategyStopped`/qualified noncompletion; no terminal |
| either exact equation is false | Core `Reject` |
| evaluator budget exhausted | `DeterministicLimitExceeded` |
| authenticated checker/evaluator disagrees with its selected semantic law | `CheckerFailure` |
| theorem, generator-independence, setup, or property evidence absent | Analysis `CannotAnswer` or `Unsupported`; not Core failure |

Fresh challenge sampling failure is governed by its selected public-coin law.
Dalek's zero-inclusive wide reduction has no retry failure, but that fact does
not make it an instance of the paper's nonzero challenge profile. An ordinary
false cryptographic equation is never relabeled malformed merely because a
library reports one undifferentiated verification error.

## 11. Negative mutations

The constructive encoding distinguishes at least:

1. omit `{V,n}` from FS initialization;
2. reorder, duplicate, or remove one `V_j`;
3. draw `y` before `A,S`;
4. draw `x` before `T_1,T_2`;
5. draw `w` before `t_hat,tau_x,mu`;
6. draw `u_i` before its `L_i,R_i`;
7. reuse one ChallengeRef for `y,z` or two IPA rounds;
8. accept zero under a nonzero-challenge source profile;
9. use wrong `N`, non-power-of-two `N`, or insufficient generators;
10. omit, swap, or duplicate an IPA round pair;
11. alias generator sequences declared independent;
12. package all fields as one pre-challenge message;
13. model aggregation as `m` independent proofs rather than one dimension
    `N=n*m` argument;
14. hide multiparty dealer/party construction in verifier Core;
15. combine checks with unmodeled verifier-private randomness;
16. treat the non-ZK IPA as inheriting the range argument's ZK property; or
17. infer ROM/QROM, knowledge, malicious-verifier ZK, or relation satisfaction
    from structural execution.

## 12. Theorem boundary, classification, and nonclaims

The source results are retained as theorem-source targets, not imported facts:

| Source result | Exact source scope | T2 status |
|---|---|---|
| Theorem 1 | the interactive IPA has perfect completeness and statistical witness-extended emulation, extracting either a valid witness or a nontrivial discrete-log relation among the bases | structurally representable; no property judgment activated |
| Theorem 3 | the interactive aggregated range proof has perfect completeness, perfect honest-verifier zero knowledge, and computational witness-extended emulation | structurally representable; exact premises and proof authority absent |
| Section 4.4 | corrected statement-bound Fiat--Shamir discussion claims a noninteractive ROM transformation and cites later multi-round work | exact theorem applicability, random-oracle experiment correspondence, challenge-distribution match, and quantitative transport remain unanswered |

The IPA is explicitly not zero knowledge. The outer range construction's
blinding and theorem cannot be inherited by the IPA claim in isolation. The
multiparty producer protocol does not add malicious-dealer or malicious-party
security to Theorem 3. The Dalek verifier combiner requires its own
approximately `1/p` loss-bearing realization theorem rather than the
deterministic source verifier's identity.

The result is `Native`. Existing Core messages, challenges, reductions,
checks, terminals, flat finite execution, Interface projection, Plan recipes,
Relations grounding, and Analysis family ingress are sufficient. No runtime
subprotocol, commitment profile, new shared root, or evaluator is needed.

This T2 record does not establish generator independence, discrete-log
hardness, Pedersen properties, honest setup, IPA zero knowledge, exact
multi-round FS applicability, ROM/QROM security, malicious multiparty
construction security, randomized-batch equivalence, implementation
conformance, arbitrary dynamic dimensions, backend support, or performance.

Passing this record also does not establish whole-family existence,
uniformity, asymptotic complexity, relation satisfaction from acceptance, or
that the pinned Dalek implementation corresponds to the paper member. Each is
a separately identified Relations, Analysis, Realization, or Evidence
question.

## 13. Durable action and reversal conditions

No durable semantic change is requested. The selected result should remain a
T2 research record; it does not justify a new evaluator or T3 fixture. A future
Bulletproofs Analysis package may add owner-local experiment/property/theorem
profiles without changing this Core. A checked IPA authoring template is
appropriate only after repeated use; it must elaborate to the same flat body
and carry no runtime child authority. A Pedersen coefficient-opening profile
is likewise optional and is not a dependency of this classification.

Reopen `Native` only if later source-faithful pressure demonstrates one of:

1. continuous transcript meaning cannot survive checked flat elaboration;
2. an essential source member selects an unbounded or runtime IPA depth that
   cannot be authenticated as a finite Core;
3. range-to-IPA theorem composition cannot name the exact checks and claim
   graph without duplicating semantic authority;
4. Analysis cannot relate a uniform variable-size family to these exact
   finite members through pointwise correspondence;
5. repeated Pedersen polynomial arguments expose one necessary shared public
   opening boundary that ordinary typed checks cannot preserve; or
6. a verifier-relevant multiparty or child-execution state becomes part of
   protocol meaning rather than producer realization.

None occurs in the reviewed final-paper range/IPA path. If one later occurs,
retain this successful bounded member, classify the new variant separately,
and replay only the completed cases sharing the reopened composition,
commitment, family, or authority boundary.
