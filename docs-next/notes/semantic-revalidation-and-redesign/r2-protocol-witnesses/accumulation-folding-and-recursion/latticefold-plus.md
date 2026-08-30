# LatticeFold+ Folding over Module Commitments

> **Portfolio case:** `V04` LatticeFold+
> **Depth:** T1 source-grounded constructive mapping
> **Result:** `Native`
> **Authority:** Source-grounded temporary research, not an implementation,
> theorem-validation, performance, or security claim

## 1. Result in one paragraph

The selected LatticeFold+ member is expressible without a new accumulator,
folding, recursive-proof, lattice, or child-execution subject. One flat finite
Core owns the verifier-observable interaction. Its two structural reductions
first turn three ordered instances of the generalized committed linear
relation into one higher-norm instance and then decompose that instance into
two ordinary-norm accumulator instances. Plan owns the finite algebra that
constructs range witnesses, helper commitments, Sumcheck messages, the folded
private witness, and the final two private accumulator witnesses. Relations
owns the exact input, intermediate, and output instance/witness occurrences
and the two private transforms. Authenticated modules own ring arithmetic,
Ajtai commitments, gadget decomposition, monomial encodings, and finite
Sumcheck checks. No generic commitment-opening use is present: the private
openings are relation witnesses, while the verifier checks algebraic
commitment relations without receiving an opening-evidence package.

This case is also a negative control for a Plan-completion extension. The
folded witness is available before the genuine decomposition prover decision,
and both final private accumulator witnesses are derivable at that decision.
Inventing a post-completion callback for this member would erase an existing
causal owner rather than expose a missing lifecycle boundary.

## 2. Exact source lock and source boundary

The sole semantic source is Boneh and Chen,
[LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding for Succinct
Proof Systems](https://eprint.iacr.org/2025/247). The IACR metadata identifies
the current document as the last of three revisions, dated `2025-08-10`. The
PDF title page says `August 9, 2025`; these are two presentations of the same
frozen intake, not two selected revisions. Its PDF SHA-256 is:

```text
48f40d28f42978236d7fcaa335022d124df76061ef48ccbd400127e7eb130ea1
```

The revision note says that it adds a more detailed specification for small-
modulus support. This record selects the main construction in Sections 3--5
and records the Appendix B variant only as a separately selectable profile. It
does not silently combine the base construction, the communication
optimization in Remark 4.7, the small-`n` adaptation in Remark 4.8, the
small-modulus tensor-ring construction in Appendix B, or the illustrative
parameter row. Each changes message shape, algorithms, dimensions, or
challenge arithmetic and therefore would form a different finite member.

The paper supplies an interactive reduction-of-knowledge construction and
theorems under explicit algebraic, challenge-set, binding, and knowledge-error
conditions. It discusses Fiat--Shamir cost but does not specify a transcript
codec, hash, domain-separation scheme, challenge sampler, proof byte format,
or random-oracle theorem. Consequently:

- the source theorem can be considered for the exact Fresh member only after
  independent theorem-source validation;
- a canonical strong-Fiat--Shamir sibling is target-formable only after an
  exact transcript construction is supplied; and
- the paper by itself establishes no correspondence or theorem transport to
  that sibling.

No secondary summary, implementation, benchmark, or later protocol is used to
fill a missing semantic step.

## 3. What the source construction is

LatticeFold+ is a folding reduction, not a complete zero-knowledge proof
system and not a final recursive argument. In the selected three-input member,
it treats one online instance and two accumulated instances uniformly as
three ordered input occurrences and returns two new accumulated instances:

```text
Rcomp = Rlin,B
Racc  = (Rlin,B)^2

Rcomp x Racc = (Rlin,B)^3
  --fold--> Rlin,(B^2)
  --decompose--> (Rlin,B)^2 = Racc
```

The first arrow raises the private witness norm bound from `B` to `B^2`. The
second arrow decomposes the higher-norm witness into two lower-norm witnesses,
which permits the same accumulator relation to be used again. “Fold” here
means a reduction of knowledge that preserves a later knowledge obligation;
it does not mean that the Core has already proved both input relations or that
the returned accumulators are final proofs.

The paper also sketches an R1CS/CCS-to-linearization reduction. This record
fixes the folding member at `Rlin,B`; an application may prepend the separately
modeled R1CS or CCS linearization. Doing so adds claims, messages, Sumcheck
rounds, and a relation transform to the same flat Core. It does not change the
LatticeFold+ owner selection made here.

## 4. One exact finite member schema

### 4.1 Closed member parameters

`LFPlusThreeToTwoMember` is a constructor for one exact finite member. Every
argument below is an authenticated value or dependency, not a runtime family
variable:

```text
LFPlusThreeToTwoMember = {
  lambda: ExactNatural,
  q: ExactOddPrime,
  d: ExactPowerOfTwo,
  d_prime: ExactNatural = d / 2,
  n: ExactPowerOfTwo,
  kappa: ExactNatural,
  k: ExactNatural,
  ell: ExactNatural = ceil(log_(d_prime)(q)),
  L: ExactNatural = 3,
  nlin: ExactNatural,

  ring: Rq = Zq[X] / (X^d + 1),
  sumcheck_domain: ExactCanonicalFiniteSet C,
  folding_domain: ExactCanonicalFiniteSet Sbar,
  B: ExactNatural = d_prime^k,

  commitment_matrix: A in Rq^(kappa x n),
  linear_maps:
    FixedSeq<Matrix<Rq,n,n>,nlin>,

  ring_algorithms,
  tensor_algorithms,
  challenge_samplers,
  commitment_algorithms,
  gadget_decomposition_algorithms,
  monomial_algorithms,
  sumcheck_algorithms,
  exact evaluation contracts,
  exact finite resource bounds
}
```

Formation requires the source's base-construction shape conditions, including
the exact padding convention for `split`, a challenge carrier on which every
used inverse is defined, and enough space to encode the decomposed commitment.
The simple Section 4.4 profile takes `n = kappa*d^2*k*ell`; a padded larger-`n`
profile must identify its exact injection and zero padding. The source-theorem
applicability question, separately, includes:

```text
q > 2
d >= 4
k, kappa, nlin >= 1
d, k, kappa, ell, and n are powers of two in the selected base profile
every used folding-domain value is a unit in Rq
n = kappa*d^2*k*ell
```

```text
|Sbar| = |C| >= 2^lambda
Sbar is the selected strong sampling set
C is the selected Sumcheck challenge set

Sbar_operator_norm * 3 * (d_prime + 1 + B + d*k) <= B^2
```

The exact carrier and arithmetic-module formation checks are structural.
“Strong sampling,” the displayed norm inequality as a sufficient completeness
premise, relaxed binding, and their cryptographic or asymptotic adequacy are
not accepted from labels and remain Analysis inputs. The source's illustrative
row (`L=3`, 128-bit `q`, `d=64`, `n=2^21`, `k=2`, `kappa=9`) does not name the
exact prime, matrices, challenge sets, codecs, or algorithms and is therefore
not itself this admitted member.

All written index ranges in the remainder are compile-time finite expansions.
The Core contains no symbolic loop and invokes no runtime child protocol.

### 4.2 Exact generalized committed linear relation

For the fixed member, the relation index is:

```text
i_lin = (A, linear_maps[0..nlin-1], all fixed ring dimensions)
com_A(f) = A * f in Rq^kappa
MC = C x C
Mq = Rq x Rq
```

One public instance and private witness are:

```text
x = (cm_f in Rq^kappa,
     r in MC^(log2(n)),
     v in Mq^nlin)
w = f in Rq^n
```

They satisfy `Rlin,B` exactly when:

```text
norm_infinity(f) < B
cm_f = A * f
for every j in 0..nlin-1:
  inner_product(linear_maps[j] * f, tensor(r)) = v[j]
```

The setup/index value is represented as a typed public parameter occurrence,
not mislabeled as an application Statement. The relation-definition schema
fixes its types, dimensions, predicate, and algorithm dependencies; each
relation instance carries the exact setup/index value used in that invocation.
Each of the three ordered `x` values is a distinct Statement occurrence. The
Relations instance therefore retains the source distinction: its public
occurrence graph contains setup/index and per-input instance coordinates, and
its protocol binding maps them to public-parameter and Statement coordinates
respectively.

### 4.3 Linear and double commitments

The linear commitment is the exact total map `com_A(a)=A*a`. For a matrix it
is applied column-wise. Binding is not part of this denotation.

For a matrix `M in Rq^(n x m)`, `m>1`, the selected double commitment is:

```text
D       = com_A(M) in Rq^(kappa x m)
D_gad   = GadgetDecompose_(d_prime,ell)(D)
D_flat  = flatten(coefficients(D_gad))
tau_M   = zero_pad(D_flat, n), with norm_infinity(tau_M) < d_prime

split(D) = tau_M
pow(split(D)) = D
dcom_A(M) = com_A(split(com_A(M)))
```

`split` is injective on the selected commitment-matrix carrier. `pow` is a
left inverse on its image and is explicitly not injective on its whole input
carrier. A target that silently assumes `pow` is injective changes the
relation and invalidates the source argument.

A double-commitment private opening is the pair `(tau,M)` satisfying:

```text
pow(tau) = com_A(M)
com_A(tau) = CM
the exact source-relative low-norm opening conditions hold
```

Neither `tau` nor `M` is transmitted as an opening proof in the folding Core.
They remain private witness/Plan state.

## 5. Exact algebraic anatomy

### 5.1 Monomial and range encodings

Let `Mset` be the paper's signed monomial set in `Rq`. For a low-range integer
coefficient `a`, `exp(a)` is the corresponding monomial. The algebraic
monomial test uses, for a sampled `beta`, the identity:

```text
ev_a(beta)^2 = ev_a(beta^2)
```

The batched monomial protocol commits to a matrix `M`, samples the exact
`c`, `beta`, and random-combination challenges, and reduces the tests for all
selected columns to one statically expanded degree-three Sumcheck. It then
checks the source equation corresponding to Equation (12). Its output retains
the exact multilinear evaluation occurrence `M^T tensor(r)`; a Boolean “range
passed” is not an adequate substitute.

For `B=d_prime^k`, decompose the coefficient matrix of `f`:

```text
D_f = GadgetDecompose_(d_prime,k)(coefficients(f))
      in Zq^(n x d*k)
M_f in EXP(D_f) subset Mset^(n x d*k)

tau_D = split(com_A(M_f))
m_tau in EXP(tau_D) subset Mset^n

CM_f   = dcom_A(M_f) = com_A(tau_D)
cmm_tau = com_A(m_tau)
```

The range subprotocol performs one batched monomial check for `M_f` and
`m_tau`, receives their evaluation data plus the prover's coefficient
evaluation `v` and scalar evaluation `a`, and checks:

```text
psi = sum_(j=1..d_prime-1) j * (X^(-j) + X^j)

constant_term(psi * b) = a
constant_term(
  psi * (u_0 + d_prime*u_1 + ... + d_prime^(k-1)*u_(k-1))
) = v
```

These are the exact algebraic range implications selected from Construction
4.4. The helper commitments, monomial claims, evaluation occurrences, and
constant-term checks remain separate. One generic “range proof” value would
lose both failure location and the relation-transform outputs needed later.

### 5.2 Commitment transformation

For each input ordinal `i`, after the range subprotocol has fixed the helper
commitments and evaluation occurrences, the verifier supplies:

```text
s_i  in Sbar^3
s'_i in Sbar^(d*k)
```

The prover derives and publishes:

```text
h_i = M_f_i * s'_i in Rq^n
cm_h_i = com_A(h_i)
```

The order is essential: `CM_f_i` is published before `s'_i`, while `cm_h_i`
is published after it. The double commitment fixes the hidden `M_f_i`; the
later publication is the challenged linear combination. Moving both after
`s'_i` destroys the source's extraction argument, while moving `cm_h_i`
before `s'_i` changes the protocol being modeled.

The verifier next samples two independent vectors:

```text
c_i^(0), c_i^(1) in C^(log2(kappa))
```

The parties run two independent, lockstep, finite Sumchecks over the same
batch. The batch contains the four Equation (18) claims:

```text
[tau_D_i, m_tau_i, f_i, h_i]^T * tensor(r_i_range)
  = (e_i[0], e_i[1], e_i[2],
     inner_product(e_i[3..3+d*k), s'_i))
```

and the two Equation (20) claims, one for each `z in {0,1}`:

```text
t_i^(z) = tensor(c_i^(z))
          tensor_product s'_i
          tensor_product (1,d_prime,...,d_prime^(ell-1))
          tensor_product (1,X,...,X^(d-1))

inner_product(tau_D_i, t_i^(z))
  = inner_product(tensor(c_i^(z)), cm_h_i)
```

The two executions reduce to the paired evaluation point
`r_o in (C x C)^(log2(n))` and paired evaluations `e_o`. The paper's
knowledge analysis explicitly relies on two independent Sumcheck challenge
vectors and says it is unclear whether one would suffice. The selected Core
therefore has two joint-group members at every such round; no profile may
collapse them into one draw and retain this source-theorem candidate.

The verifier and honest Plan derive:

```text
cm_g_i = s_i[0] * CM_f_i
         + s_i[1] * cmm_tau_i
         + s_i[2] * cm_f_i
         + cm_h_i

g_i = s_i[0] * tau_D_i
      + s_i[1] * m_tau_i
      + s_i[2] * f_i
      + h_i
```

The adapted linear-relation protocol adds one Sumcheck claim for every exact
`linear_maps[j]` check and reduces the original point `r_i` to the common
output point `r_o`. All three executions are batched in input-ordinal order.
Their output occurrences are then combined:

```text
cm_g = cm_g_0 + cm_g_1 + cm_g_2
v_o[j] = v_o_0[j] + v_o_1[j] + v_o_2[j]
g = g_0 + g_1 + g_2

x_wide = (cm_g, r_o, v_o)
w_wide = g
```

This is one occurrence of `Rlin,(B^2)`, not three interchangeable occurrences
and not yet the output accumulator relation.

### 5.3 Final decomposition

The honest Plan deterministically decomposes `g` into two lower-norm columns:

```text
F = [F_0,F_1] in Rq^(n x 2)
g = F_0 + B * F_1
norm_infinity(F_0), norm_infinity(F_1) < B

C = com_A(F) = [C_0,C_1]
for every j:
  v_o[j] = v_0[j] + B*v_1[j]
```

The prover publishes `(C_0,C_1,v_0,v_1)`. The verifier checks:

```text
C_0 + B*C_1 = cm_g
for every j: v_0[j] + B*v_1[j] = v_o[j]
```

The output occurrences are:

```text
x_out_0 = (C_0, r_o, v_0),  w_out_0 = F_0
x_out_1 = (C_1, r_o, v_1),  w_out_1 = F_1
```

They are two distinct occurrences of `Rlin,B`, even if selected values happen
to be equal.

## 6. Flat Core schedule

The paper specifies several protocols through construction composition and
parallel batching rather than one byte-level schedule. The target selects the
following deterministic elaboration rule:

1. input ordinals are ascending;
2. fields inside a record-valued publication use the source's written order;
3. parallel Sumchecks run lockstep by round and parallel ordinal;
4. every random combiner is drawn after all claims it combines are fixed;
5. a Sumcheck round is expanded to one typed prover polynomial message, one
   typed verifier Challenge, and the exact round check;
6. final evaluations are one typed prover message followed by exact Boolean
   checks; and
7. every source “run in parallel and compress” is fully expanded before Core
   authentication.

That rule forms this representative total occurrence order:

```text
0.  open root scope; bind exact setup/index PublicParameter and x_0,x_1,x_2

1.  ProverMessage range helpers for input 0,1,2:
      (CM_f_i,cmm_tau_i and exact monomial/range helper claims)

2.  Challenges for the batched monomial checks:
      c, beta, exact random combiners, and all degree-3 Sumcheck rounds
3.  ProverMessage exact monomial final evaluations
4.  InvokeCheck monomial equations and range Equation (12) checks
5.  ProverMessage range evaluations (v_i,a_i)
6.  InvokeCheck both constant-term range equations for every input

7.  Challenges (s_i,s'_i) for each input, in input order
8.  ProverMessage (cm_h_0,cm_h_1,cm_h_2)
9.  Challenges c_i^(0),c_i^(1) and exact batch combiners

10. for each statically enumerated lockstep Sumcheck round:
      ProverMessage paired round polynomials
      joint Challenge pair for the two independent executions
      InvokeCheck round consistency
11. ProverMessage paired final evaluations
12. InvokeCheck all adapted Equations (18), (20), (22), and (29)

13. ApplyReduction FoldThree:
      C_in_0,C_in_1,C_in_2 -> C_wide

14. ProverMessage (C_0,C_1,v_0,v_1)
15. InvokeCheck decomposition commitment and evaluation equations
16. ApplyReduction DecomposeWide:
      C_wide -> C_out_0,C_out_1

17. Accept with exact output public values, or Reject at the first failed
    check with all live claims explicitly disposed
```

An implementation may aggregate same-phase fields into a record or split them
into several wire records only through an exact Interface/OIR projection that
preserves each Core occurrence and predecessor relation. It may not move a
field across a Challenge.

The Core claim graph is exactly:

```text
C_in_0, C_in_1, C_in_2 : Linear<Rlin,B>
  source = three distinct InitialClaim Statement bindings

FoldThree:
  inputs = [C_in_0,C_in_1,C_in_2]
  side inputs = complete setup and helper-publication coordinates
  required challenges = every exact range, batching, folding, and Sumcheck draw
  required publications = every helper/message occurrence paired with its
                          least later dependent Challenge, or None after the
                          last Challenge
  output = C_wide : Linear<Rlin,(B^2)>

DecomposeWide:
  input = C_wide
  side inputs = [C_0,C_1,v_0,v_1,B]
  required challenges = []
  required publications = [decomposition message with next_challenge=None]
  outputs = [C_out_0,C_out_1] : two Linear<Rlin,B> occurrences
```

The reductions record structural relation evolution. They do not establish a
reduction-of-knowledge theorem, completeness, or knowledge soundness.

## 7. Fresh and strong-Fiat--Shamir Protocols

The source-faithful Protocol uses Fresh challenge interpretation. Every
Challenge has the exact finite domain and correlation law selected by the
member. The two parallel commitment-transformation Sumchecks use a joint draw
whose two projections are independent; folding and Sumcheck domains remain
different types even when their cardinalities coincide.

An optional target strong-Fiat--Shamir Protocol may share the same `CoreId`
only after an exact canonical transcript construction is supplied. Its derived
prefix must include, without an authored omit switch:

- the Core, construction, and application-domain headers;
- the complete setup/index public-parameter binding;
- all three ordered input Statement bindings, including both previous
  accumulator occurrences;
- every prior helper commitment, Sumcheck polynomial, evaluation, and
  decomposition publication that precedes a later Challenge;
- exact occurrence, type, scope, guard, and joint-draw coordinates; and
- every previous Challenge draw in the continuous transcript state.

No input instance, commitment, or Sumcheck message is Wire-only. The source
does not select codecs, byte framing, a permutation/hash, domain strings, or a
challenge decoder, so this record selects no particular construction ID and
imports no Fiat--Shamir theorem. Omitting either accumulated input is a weak
binding mutation even though the interactive Fresh protocol remains defined.

## 8. Typed owners and acyclic identities

### 8.1 Owner table

| Object or fact | Owner | Exact role |
|---|---|---|
| ring, tensor, gadget, `split`, `pow`, `EXP`, constant-term, and matrix algorithms | authenticated semantic modules | total finite denotations and exact ABIs |
| `com_A`, matrix commitment, and double-commitment construction | authenticated semantic modules | algebraic construction, not binding security |
| input, helper, wide, and output relations and private transforms | Relations | typed predicates, occurrence-local instances, and witness evolution |
| public schedule, messages, Challenges, checks, claims, reductions, terminals | Core | one finite verifier-observable execution |
| Fresh or canonical-FS challenge interpretation | Protocol | exact source of Challenge values and qualified interpretation failures |
| all helper and output construction | Plan | finite honest-prover dataflow only |
| invocation, transport, completion, and proof-package slots | Interface and OIR | external presentation without changing causality |
| binding, knowledge error, theorem applicability, zero knowledge, PQ security, and asymptotics | Analysis | qualified properties under explicit hypotheses |
| source digest, checked theorem artifact, runs, measurements, and correspondence artifacts | Evidence | provenance and validation records, never semantic truth by presence |

### 8.2 Symbolic identity graph

The exact ID dependencies are acyclic:

```text
LFPlusModuleIds
  -> relation-language and algorithm dependencies

RlinDefinitionId(B, exact dimension/type schema and module dependencies)
  -> RlinInterfaceId
  -> input/wide/output RelationInstanceIds
  -> private witness occurrences

CoreId
  = PIRId(modules, typed setup and bindings, complete occurrence schedule,
          checks, claims, FoldThree, DecomposeWide, terminals)

FreshProtocolId
  = PIRId(CoreId, Fresh)

TranscriptConstructionId
  = PIRFSId(CoreId, exact canonical construction)       // only if supplied
CanonicalFSProtocolId
  = PIRFSId(CoreId, TranscriptConstructionId)

ProtocolInterfaceId(P)
  = PIRInterfaceId(P, invocation, Statement, transport, completion)

ProverPlanId(P)
  = PIRPlanId(P, private ingress, randomness, state, decision recipes,
              derived witness exports)

PlanWitnessSurfaceId(P)
  = source-ID-free extraction of only witness ingress and exports

ProtocolRelationBindingId(P)
  = RelationsId(P, relation Interfaces, occurrence edges,
                claim/reduction meanings, grounding equations)

PlanWitnessBindingId(P)
  = RelationsId(PlanWitnessSurfaceId(P), relation witness occurrences)
```

The Plan contains no Relations ID. The base Protocol relation binding contains
no Plan, Interface, OIR, run, or Analysis result. A private witness occurrence
does not enter a semantic content ID through its value. Analysis goals and
validation bases are identified descendants, not Core fields.

## 9. Plan graph and lifecycle finding

### 9.1 Exact Plan ingress and state

For either Protocol `P`, one realizing Plan declares:

```text
WitnessIngress:
  f_0, f_1, f_2

Private randomness:
  none beyond values already modeled as verifier Challenges for the source
  construction; any zero-knowledge wrapper would add a separate profile

Persistent/private state:
  coefficient decompositions D_f_i
  monomial matrices M_f_i
  tau_D_i and m_tau_i
  h_i, g_i, and combined g
  all Sumcheck prover tables and partial evaluations
  F_0,F_1 and their evaluation vectors
```

There is one exact decision recipe for every active prover message in Section
6. Each recipe reads only the fixed public setup, earlier opened Statement
values, earlier Challenges, prior own moves, declared witness ingress, and
typed private state. Every algorithm is an exact admitted total algorithm with
a finite evaluation contract; no host callback or “run the paper prover” node
exists.

### 9.2 No public-prover-only parameter pressure

The commitment matrix, ring parameters, linear maps, and challenge domains are
used by verifier checks or define the exact relation and therefore are honest
Core public parameters or authenticated semantic dependencies. The selected
source has no separately identified public proving parameter that is needed by
Plan but deliberately absent from verifier semantics. This case neither
requires nor refutes a typed public-prover-parameter lane.

### 9.3 Negative control for completion recipes

The last private outputs do not appear from nowhere at successful completion:

- each `g_i` is derivable immediately after the genuine `s_i,s'_i` Challenge
  and `cm_h_i` decision;
- combined `g` is available before the decomposition publication; and
- `F_0,F_1` are computed by the recipe for that genuine final prover message.

The Plan may export `F_0` and `F_1` as derived witnesses from the decomposition
decision's local recipe. Relations then binds those source-ID-free exports to
the two output relation-witness occurrences. No private work after the final
Core Challenge lacks a decision owner in this member.

Therefore LatticeFold+ must not be cited as positive evidence for a general
post-Challenge or post-completion callback. Adding an artificial terminal
message or completion recipe would duplicate an existing decision and change
identity without increasing expressibility.

## 10. Relations and exact occurrence grounding

### 10.1 Relation objects

The selected relation package contains:

1. `Rlin,B`, `Rlin,(B^2)`, their three-input ordered product, and the two-output
   accumulator product;
2. the exact helper predicates corresponding to `Rm,in`, `Rm,out`, `Rrg,B`,
   `Rdcom`, and the commitment-transformation output relation;
3. `FoldThreeTransform`, from three ordered `Rlin,B` private occurrences and
   exact public transcript parameters to one `Rlin,(B^2)` occurrence; and
4. `DecomposeWideTransform`, from one `Rlin,(B^2)` private occurrence plus the
   published decomposition parameters to two ordered `Rlin,B` occurrences.

The helper relations make range and double-commitment obligations reviewable,
but only the two named Core reductions advance live top-level claims. Analysis
may validate directional refinement or reduction-of-knowledge theorems; their
presence in Relations does not prove them.

### 10.2 Input grounding

For input ordinal `i in {0,1,2}`, the exact equations are:

```text
RelationInstance_i.index.setup == Core PublicParameter setup occurrence
RelationInstance_i.public.cm_f == Statement_i.cm_f
RelationInstance_i.public.r    == Statement_i.r
RelationInstance_i.public.v    == Statement_i.v
RelationWitness_i.f            == Plan WitnessIngress f_i
```

These are occurrence equations, not a value-based merge. Input `0` is the
online occurrence and inputs `1,2` are the two prior-accumulator occurrences
under the selected application convention. Reordering equal-valued inputs
changes the product occurrence and all dependent identity bodies.

### 10.3 Intermediate and output grounding

The run-grounded wide instance is:

```text
Wide.public.cm_f == derived cm_g occurrence
Wide.public.r    == paired final Sumcheck Challenge occurrence r_o
Wide.public.v    == derived v_o occurrence
Wide.witness.f   == Plan private state g
```

The output instances are grounded to the decomposition publication and the
same exact `r_o` occurrence:

```text
Out_0.public = (C_0, r_o, v_0)
Out_1.public = (C_1, r_o, v_1)
Out_0.witness = exported F_0
Out_1.witness = exported F_1
```

The grounding equations additionally check the exact commitment and
evaluation decompositions from Section 5.3. A successful check does not prove
that the private outputs satisfy their relations; occurrence-local
satisfaction is a separate Relations question.

### 10.4 Bridge to the next invocation

The next folding run has two new accumulator-input Statement occurrences.
They do not share IDs with `Out_0` and `Out_1`. Because both private outputs
are retained decision-site Plan exports, the selected direct semantic path
uses the same Plan-owned one-use handoff as the other folding cases:

```text
run_t.Out_k
  -- IssueAcceptedPlanWitnessIngressSupply, one use -->
run_(t+1).AccumulatorWitnessIngress_k

JoinCausalPlanWitnessHandoff(source private grounding,
                             target private grounding,
                             CausalPlanWitnessHandoffCapability)
  --> CheckedPlanWitnessHandoffCorrespondence_k
```

Each issue consumes one exact output right and one exact unfilled ingress and
returns `ReadyPlanWitnessIngressSupply`, its live one-use capability, and a
`CausalPlanWitnessHandoffCapability`. It preserves `k in {0,1}` and cannot
swap, duplicate, merge, or equate the two occurrences.

Separately, one affirmative public `EquationGrounding` per lane uses two
`ExactCausallyGenerated` run slots and retains the exact source/target run
objects and relation instances. `JoinCausalPlanStepRecurrence` conjoins the
public equation with the checked private handoff only when those source and
target objects agree exactly. The result is one nonidentified
`CheckedCausalPlanStepRecurrence` plus a live process-local capability. This
is the selected finite adjacent-step recurrence, not an Interface completion
transport and not a Realization theorem.

Serialization, persistence, buffer identity, restart recovery, and delivery
provenance remain Realization concerns. A checked codec or storage receipt may
support value correspondence, but it cannot mint or reconstruct the live
one-use Plan handoff capability. Unbounded recurrence is an Analysis family
over repeated finite members, not a loop inside this Core.

## 11. Commitment-profile disposition

The selected member uses three different notions that must not be collapsed:

| Source object | Target placement | Generic commitment-opening use? |
|---|---|---|
| `cm_f=A*f` inside `Rlin` | relation predicate plus exact construction module | No; `f` is private relation witness |
| `CM_f=com(split(com(M_f)))` | helper relation and double-commitment construction module | No; `(tau_D,M_f)` is not sent as opening evidence |
| `cmm_tau`, `cm_h`, and decomposition `C` | Core messages, algebraic checks, and relation-transform parameters | No; verifier checks linear equations and Sumchecks |

Creating a commitment-opening profile with a dummy query, dummy answer, or the
entire folding transcript as undifferentiated “evidence” would misstate the
source verification relation. The exact-used profile set is therefore empty
for generic commitment-opening verification in this Core.

The authenticated module still supplies exact commitment construction and
matrix-operation algorithms. Relations may use its commitment-construction
contract only to ground an exact helper publication for which both the
relation material and Core publication occurrence are available. The initial
Statement commitment equation remains part of relation satisfaction; it is
not rewritten as a publication grounding. Binding, relaxed binding, hiding,
extraction, and Module-SIS reductions remain Analysis hypotheses or theorem
conclusions. A later final proof system that actually opens an Ajtai commitment
may select a separate exact opening-verifier profile; it is not retroactively
part of this folding member.

## 12. Interface and OIR projection

The Protocol Interface has:

- one public setup/index input slot;
- three ordered input-instance slots, all presented as Statement members;
- one transport coordinate for every typed prover publication and every
  Challenge occurrence;
- completion outputs for the two ordered accumulator instances; and
- a qualified Reject completion for either Protocol and, only for a selected
  canonical-Fiat--Shamir sibling, its interpretation-failure completion.

OIR may serialize all prover publications into one proof record and both
output accumulators into one result record. Its projection must retain the
source Core occurrence of every field, exact codecs, order, active/inactive
meaning, and all transcript-relevant framing. “The LatticeFold+ proof” is an
endpoint package, not a Core message and not a new semantic root.

The paper supplies no canonical proof bytes. Any byte layout is an independent
Interface/OIR profile and no source serialization-conformance claim is made.

## 13. Complete qualified failure partition

### 13.1 Formation and admission failures

The exact owner returns its ordinary qualified outcome for:

- malformed dimensions, noncanonical matrices or sets, bad dense ordinals,
  wrong sequence lengths, or ill-typed ring elements;
- unsupported ring, gadget, monomial, Sumcheck, commitment, or sampler
  declarations;
- missing algorithm, evaluation-contract, module, relation, transcript, or
  codec preimages;
- wrong semantic regime, subject kind, Protocol, relation Interface, or
  retained evaluator authority;
- failure of exact power-of-two, padding, `split`-capacity, challenge-domain,
  schedule, or ABI predicates;
- a Core claim/reduction graph that omits, duplicates, reorders, or aliases an
  input, intermediate, or output occurrence;
- a reduction that omits a helper publication, Challenge, or publication-to-
  next-Challenge dependency;
- a Plan with a missing decision recipe, future read, wrong move type,
  unavailable operand, incomplete state transition, or mismatched witness
  export;
- a relation binding with incomplete index/Statement/witness grounding or an
  output recipe that loses an occurrence; and
- deterministic authentication, admission, or portable-evaluation bound
  exhaustion.

None yields a partially admitted member.

### 13.2 Protocol execution rejection

An exact formed run rejects at the corresponding typed check when:

1. a Sumcheck round polynomial has the wrong degree, wrong claimed sum, or
   inconsistent next evaluation;
2. a monomial identity or its Equation (12) batched check fails;
3. either constant-term range equation fails;
4. an Equation (18), (20), (22), or adapted linear Equation (29) check fails;
5. a commitment/evaluation fold is inconsistent;
6. `C_0+B*C_1 != cm_g`;
7. any `v_0[j]+B*v_1[j] != v_o[j]`; or
8. a selected module check returns false.

Fresh challenge resolution and canonical-FS interpretation have their own
qualified noncompletion branches. A malformed proof value, sampler rejection,
codec rejection, exhausted retry bound, or evaluation failure is not an
ordinary cryptographic Reject unless the owning semantics explicitly makes it
one.

### 13.3 Analysis failures and non-results

The following never become Core Reject reasons merely by being absent or
false:

- Module-SIS or relaxed-binding assumptions;
- strong-sampling and knowledge-error asymptotics beyond exact finite checks;
- source theorem applicability or source-to-target correspondence;
- knowledge extraction, reduction composition, or adversary bounds;
- zero knowledge, hiding, witness indistinguishability, or blinding;
- post-quantum security or whole-system quantum closure;
- Fiat--Shamir applicability in ROM or QROM;
- implementation conformance, cost, proof size, or performance; and
- correctness of an unbounded IVC recurrence or final decider.

These receive qualified Analysis or Evidence outcomes, not invented Boolean
fields on the Core or Protocol.

## 14. Finite resources and family-level limits

For one exact member, the owner derives finite intrinsic bounds from:

```text
L=3, n, kappa, d, k, ell, nlin,
log2(n), log2(kappa),
the exact numbers and degrees of batched Sumchecks,
the two independent parallel Sumcheck executions,
all message and Challenge carrier maxima,
all algorithm evaluation contracts,
all transcript frame and squeeze bounds,
and all Plan node/state counts.
```

The source's unoptimized main member has exactly three per-input helper
families, `3*d*k` folding-domain coordinates for the `s'` vectors, nine
folding-domain coordinates for the `s` triples, and two independent Challenge
coordinates at every final parallel-Sumcheck round. The precise total Core
occurrence count and canonical ordinal order remain to be derived after
selecting one exact batching elaboration. Until then this record does not
identify one unique Core body and remains T1.

The paper's Theorem 5.3 gives asymptotic and estimated concrete costs under
additional conditions. Those formulas are Analysis facts about a family and
do not enlarge one member's Core bounds. The claimed sub-200KB or approximate
hash counts use illustrative parameters and optimizations and are not Evidence
of an implementation run.

No finite member proves that arbitrary-depth folding terminates, stays within
security bounds, or yields a succinct final proof. Those are separately
quantified family/composition questions.

## 15. Falsifying mutations

The following mutations distinguish the selected architecture from attractive
but unsound or semantically lossy encodings:

| Mutation | Required result | What it tests |
|---|---|---|
| merge equal-valued input instances | refuse or change identity | occurrences are causal, not value interned |
| omit either prior accumulator from a canonical-FS prefix | refuse | strong input-state binding |
| publish `CM_f` only after `s'` | different protocol; no theorem transport | double commitment fixes `M_f` before challenge |
| require `cm_h` before `s'` | different protocol | challenged linear-combination order |
| treat `pow` as injective | refuse wrong module law | source explicitly says it is not |
| remove the monomial check | no range reduction | algebraic range proof is not a type annotation |
| remove either constant-term equation | no range reduction | both `tau_D` and `f` ranges are linked |
| collapse two parallel Sumchecks to one | different member; theorem unresolved | source extraction uses independence |
| erase helper evaluations after a Boolean check | refuse reduction meaning | later transforms consume exact occurrences |
| model double commitment as linearly homomorphic | refuse | transformation exists because it is not |
| attach a dummy generic opening profile | refuse exact-used/profile shape | no opening evidence is verified |
| turn helper subprotocols into runtime child Cores | reject architecture | one verifier interaction is one flat Core |
| identify `C_wide` with either output claim | refuse | norm-bound and arity change across decomposition |
| identify output accumulators with next-run inputs | refuse | the one-use handoff preserves exact causality while source and target occurrences remain distinct |
| derive `F_0,F_1` from a completion callback | unnecessary/different Plan | a genuine final prover decision owns them |
| classify Module-SIS or PQ security in Core admission | reject authority | properties belong to Analysis |
| omit exact dimensions or resource bounds | refuse member formation | a family sketch is not a finite Core |

The native result survives all of these mutations without adding a new root.

## 16. Theorem and security boundary

The source's main Theorem 5.1 composes Theorem 5.2 and Lemma 5.1 to obtain a
reduction of knowledge from `Rcomp x Racc` to `Racc`, under its stated
challenge-set, norm, and relaxed-binding hypotheses. A future Analysis result
may ask whether the exact Fresh Core, relation transforms, and source theorem
are in correspondence. It must bind at least:

- this exact PDF digest and theorem coordinates;
- the exact finite ring, commitment, challenge-set, and dimension values;
- every helper relation and construction variant selected here;
- the two-independent-Sumcheck schedule;
- the exact knowledge-error expressions and composition order; and
- validation evidence for every imported assumption and inferred source-to-
  target equation.

For the selected `L=3` member, that theorem question includes
`|Sbar| >= 2^lambda`, the displayed Section 4 inequality
`Sbar_operator_norm*3*(d_prime+1+B+d*k) <= B^2`, and the exact
`(2*B^2,Sbar-Sbar)` binding proposition for `com_A`. These are Analysis
hypotheses even when their finite arithmetic components are decidable.

The intake also retains the paper's exact error ledger rather than replacing
it with “negligible.” In the paper's notation:

```text
epsilon_mon,m
  = (2*d + m + 4*log(n)) / |C| + epsilon_bind

epsilon'_rg
  = epsilon_mon,1 + epsilon_bind + log(n)/|C|

epsilon_rg
  = epsilon_mon,d*k+1 + epsilon_bind + log(n)/|C|

epsilon_sum = (2*log(n)/|C|)^2
mu = 3 + d*k

epsilon_cm,k
  = (mu + d*k)/|Sbar|
    + 3*epsilon_bind + epsilon'_rg + epsilon_rg + 2*epsilon_sum
    + mu*(log(kappa)^2 + (2*log(n))^2)/|C|

epsilon_mlin,B,L <= L * epsilon_lin,k
epsilon_lin,k = epsilon_cm,k
```

The final decomposition has no additional knowledge error in Lemma 5.1. The
meaning of each logarithm, challenge cardinality, binding error, and selected
optimization remains tied to the frozen source notation; Analysis must reject
an attempted substitution whose instantiated bound does not match it.

Structural admission establishes none of those conclusions.

The paper describes the construction as plausibly post-quantum because its
binding route is based on Module-SIS rather than discrete logarithms. This is
not a protocol flag. A post-quantum judgment must separately analyze the
selected Module-SIS parameters, commitment and extraction reductions,
Sumcheck and folding challenges, any Fiat--Shamir transform and QROM theorem,
the outer recursive verifier, the final compression/decider proof, signatures
or hashes used by the application, and the whole composition path. This record
creates no such judgment.

The construction is not zero knowledge as modeled. Any masking, hiding, or ZK
wrapper adds exact messages, randomness, relations, and theorem premises and
therefore forms a distinct Protocol/Plan package.

## 17. Classification, achieved depth, and reopening conditions

The primary classification is `Native`, at T1:

- the frozen source, selected `L=3` member schema, and construction variants
  are explicit;
- the algebraic, commitment, range, Sumcheck, folding, and decomposition
  anatomy is reconstructed far enough to test the proposed owner and lifecycle
  choices;
- owners, occurrences, claims, reductions, Plan state, Relations objects,
  failures, resources, and mutations have source-grounded constructive
  mappings; and
- one unique fully expanded Core body, including the selected batching
  elaboration and exact occurrence ordinals, remains open for T2; while
- source theorems, Fiat--Shamir, zero knowledge, performance, and PQ security
  remain outside structural claims.

This result does not promote a shared grammar change. Existing typed modules,
flat Core occurrences, claims/reductions, Plan recipes and state, relation
transforms, witness exports, grounding equations, and downstream projections
are sufficient.

Reopen the classification if an exact source-faithful member shows any of the
following:

1. the two independent parallel Sumchecks cannot be represented with the
   existing Challenge-correlation and finite occurrence rules;
2. the private output witnesses cannot be exported from the real
   decomposition decision without a future or cross-recipe read;
3. relation-instance recipes cannot preserve all three input, one wide, and
   two output occurrences with exact setup grounding;
4. a source-valid commitment check requires an evidence shape that is neither
   a relation predicate nor an existing exact verifier profile;
5. the next-invocation causal bridge requires occurrence identity rather than
   checked value transport; or
6. an exact theorem correspondence requires a source transcript order that
   cannot be flattened without semantic loss.

Promote the evidence depth to T2 only after selecting one batching elaboration
and closing the complete owner/identity dependency tables, exact Core schedule
and ordinals, challenge interpretation, Plan graph, Interface/OIR projection,
Relations grounding, failure partition, and finite intrinsic bounds for that
single member.

Absent such a counterexample, LatticeFold+ strengthens the case for the
existing factorization: algebraic novelty belongs in exact modules and
Relations, while verifier-observable causality remains one flat Core.
