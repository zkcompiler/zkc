# WHIR Constructive Semantic Encoding

> **Kind:** Temporary constructive holdout record
> **State:** Complete against frozen commit
> `63c48b22c7aac56d9af3ab460e4ea135a87039f3`
> **Depth:** Complete typed abstract trace and owner graph; not executable
> protocol support
> **Result:** Structural `Native`; whole case `ProfileOrModule` because the
> exact round-by-round property and theorem application are not published
> **Authority:** None

## 1. Question and answer

The question is whether one source-faithful member of WHIR Construction 5.1
can inhabit the frozen semantic architecture without:

- converting an Oracle to an opaque callback;
- exposing a verifier query before the source permits it;
- pretending a proof-sent Oracle is an initial statement Oracle;
- collapsing claim transformation into a Boolean check;
- treating Plan generation as relation truth;
- applying Fiat--Shamir directly to unauthenticated logical access; or
- importing Theorem 5.2 as a nominal citation.

The answer is yes at the structural level. Existing Core, Oracle, Plan,
Relations, checked construction, and identity laws suffice. One exact
source-pinned Analysis property/theorem profile is still needed to represent
the paper's round-by-round conclusion, so the whole case is
`ProfileOrModule`.

## 2. Exact finite member

The constructive member uses the source parameters locked in the companion
anatomy:

```text
field                    F_17
initial domain           L_0 = [1,2,4,8,16,15,13,9]
first folded domain      L_1 = [1,4,16,13]
grouped input domain     D_0 = L_0^(2) = [1,4,16,13]
grouped proof domain     D_1 = L_1^(2) = [1,16]
variables                m_0=2, m_1=1, m_2=0
folding widths           k_0=1, k_1=1
initial weight/target    w_hat_0(Z,X_1,X_2)=Z, sigma_0=0
Sumcheck degree bound    degree < 3
shift sample shape       one OOD point plus one shifted point
final sample shape       two shifted-domain points, with replacement
```

All types and algorithms below are exact admitted Foundation/PIR module
content. The shorthand names do not create a universal field or polynomial
kind:

```text
F          = exact canonical F_17 field value type
Poly3      = coefficient record for univariate polynomials of degree < 3 over F
PairF      = fixed record [F,F] in coefficient order [constant,linear]
FinalPoly  = zero-variable multilinear polynomial record over F
ShiftCoin  = record {shifted_index:D_0, gamma:F}
FinalCoin  = fixed sequence [D_1,D_1]
```

The exact portable algorithms include field arithmetic, `pow`, Boolean-cube
equality weights, `Poly3` evaluation, grouped-symbol evaluation, weight
evolution, each verifier check, and each Plan recipe. Their dependency bodies,
ABIs, evaluator contracts, and failure rows are part of the normal owner
profiles; none is a host callback.

## 3. Core objects

### 3.1 Public statement and initial claim

The root scope has one Statement binding `member` with a finite record:

```text
WHIRMemberStatement = {
  field_profile,
  L_0, L_1, D_0, D_1,
  m_0, m_1, m_2,
  k_0, k_1,
  w_hat_0,
  sigma_0,
  grouped_encoding_profile,
  exact Oracle declaration coordinates
}
```

Static fields may be Core constants rather than repeated runtime fields; the
constructive subject fixes one exact choice either way. The Statement binding
is the source of linear claim `C_initial` under the constrained-code claim
contract. It names the public instance; it does not contain the private Oracle
carrier or honest multilinear polynomial.

### 3.2 Logical Oracles

Two immutable Oracles are declared:

```text
O_0 = OracleDecl {
  origin: InitialOracle,
  index_type: D_0,
  element_type: PairF,
  maximum_entries: 4,
  publication_mode: LogicalAccess(exact_indices=D_0)
}

O_1 = OracleDecl {
  origin: ProverOracle,
  index_type: D_1,
  element_type: PairF,
  maximum_entries: 2,
  publication_mode: LogicalAccess(exact_indices=D_1)
}
```

`O_0[y]` contains the coefficients of
`p_0,y(A)=Fold(f_0,A)(y)`. `O_1[y]` contains the coefficients of
`p_1,y(A)=Fold(f_1,A)(y)`. One answer plus the relevant `alpha` therefore
determines the folded value at `y`.

The Core publishes only each logical-access fixation marker. It never
publishes a carrier, digest, commitment, or lookup-absence tag. Query admission
uses the exact finite domain law, and an out-of-domain index is refused rather
than answered as absent.

### 3.3 Fresh challenge declarations

The Protocol has a `PublicEnvironment`. Its challenges are:

| Challenge | Type | Source role |
|---|---|---|
| `alpha_0` | `F` | initial fold/Sumcheck coin |
| `z_ood` | `F` | OOD scalar; the exact point is derived by `pow` |
| `shift` | `ShiftCoin` | one joint source message containing shifted-domain index and `gamma` |
| `alpha_1` | `F` | main-loop fold/Sumcheck coin |
| `final_samples` | `FinalCoin` | two final shifted-domain samples |

Using record/vector challenges for `shift` and `final_samples` preserves the
source's joint verifier messages and their product-distribution contract. It
does not silently replace a joint draw with unrelated host RNG calls. All
draws use `Fresh`; source distribution truth remains a separately qualified
obligation rather than an authored Boolean.

## 4. Complete ordered occurrence trace

The following is the complete successful-path order. Derived values are exact
value nodes and do not create additional messages.

| Ordinal | Occurrence | Public result and dependency |
|---:|---|---|
| 0 | publish `O_0` | activates initial logical access; no value output |
| 1 | prover message `h_0` | one `Poly3`, derived by honest Plan from `f_hat_0` |
| 2 | challenge `alpha_0` | sampled only after `h_0` |
| 3 | publish `O_1` | proof Oracle carrier supplied by the prover strategy after `alpha_0` |
| 4 | challenge `z_ood` | sampled only after `O_1` fixation |
| 5 | prover message `y_ood` | exact `f_hat_1(pow(z_ood,1))` in the honest Plan |
| 6 | challenge `shift` | returns `(z_shift,gamma)` only after `y_ood` |
| 7 | prover message `h_1` | one `Poly3` for evolved weight `w_hat_1` |
| 8 | challenge `alpha_1` | sampled only after `h_1` |
| 9 | prover message `f_final` | one `FinalPoly`, the fully folded polynomial |
| 10 | challenge `final_samples` | returns `(r_0,r_1)` after `f_final` |
| 11 | query `O_0` at `z_shift` | public decision-phase query |
| 12 | answer `O_0` | `PairF`; derive `g_0(z_shift)=eval(pair,alpha_0)` |
| 13 | query `O_1` at `r_0` | public decision-phase query |
| 14 | answer `O_1` | derive `g_1(r_0)=eval(pair,alpha_1)` |
| 15 | query `O_1` at `r_1` | separate occurrence even if `r_0=r_1` |
| 16 | answer `O_1` | derive `g_1(r_1)=eval(pair,alpha_1)` |
| 17 | initial Sumcheck check | `h_0(0)+h_0(1)=sigma_0` |
| 18 | main-loop Sumcheck check | equation below |
| 19 | final consistency at `r_0` | `f_final()=g_1(r_0)` |
| 20 | final consistency at `r_1` | `f_final()=g_1(r_1)` |
| 21 | final weighted-sum check | equation below |
| 22 | apply `R_fold` | guarded by applicable successful checks; creates `C_folded` |
| 23 | apply `R_final` | guarded by every final check; consumes `C_folded` |
| 24 | reach `Accept` | requires all checks, saturated reductions, and no live linear claim |
| 25 | reach fallback `Reject` | unconditional final terminal when the accepting path is inactive |

The main-loop check is exactly:

```text
h_1(0) + h_1(1)
  = h_0(alpha_0)
  + gamma * y_ood
  + gamma^2 * g_0(z_shift)
```

The evolved weight is:

```text
w_hat_1(Z,X) =
    w_hat_0(Z,alpha_0,X)
  + Z * (gamma * eq(pow(z_ood,1),X)
       + gamma^2 * eq(pow(z_shift,1),X))
```

The final check is:

```text
w_hat_1(f_final(), alpha_1) = h_1(alpha_1)
```

All Oracle queries remain after the last prover publication. This preserves
source non-anticipation: neither `h_1` nor `f_final` can read the selected
indices or answers through the Plan view. A verifier implementation may later
reorder hidden pure computation, but it cannot change the Core occurrence
order or public observation semantics.

## 5. Claims and reductions

The linear claim graph is:

```text
C_initial --R_fold--> C_folded --R_final--> no live claim
```

`R_fold` consumes the initial constrained-code claim. Its exact structural
role set includes:

```text
required challenges:
  alpha_0, z_ood, shift

required publications and least following challenge:
  h_0   -> alpha_0
  O_1   -> z_ood
  y_ood -> shift

side inputs:
  h_0, y_ood, alpha_0, z_ood, z_shift, gamma,
  O_0 answer at z_shift, and the main-loop check result
```

Its Relations meaning derives the exact public descriptor for
`CRS[F,L_1,m_1,w_hat_1,sigma_1]`, where:

```text
sigma_1 = h_0(alpha_0)
        + gamma * y_ood
        + gamma^2 * g_0(z_shift)
```

The reduction is scheduled in the decision phase after the needed Oracle
answer exists. Delaying this structural claim creation does not expose the
query to an earlier prover decision or change the source transcript. The
claim is bookkeeping for the verified relation transition, not a value the
prover reads while constructing `h_1`.

`R_final` consumes `C_folded`, has no output claim, and is guarded by the main,
final-consistency, and final-weight checks. Its role set includes:

```text
required challenges:
  alpha_1, final_samples

required publications and least following challenge:
  h_1       -> alpha_1
  f_final   -> final_samples
```

These publication/challenge records make the strong transcript dependencies
structural. A later checked Fiat--Shamir construction must include `h_0`
before `alpha_0`, `O_1` before `z_ood`, `y_ood` before `shift`, `h_1` before
`alpha_1`, and `f_final` before `final_samples`. Cumulative state then carries
earlier publications to every later challenge.

The reductions do not prove proximity preservation. Their owner-local
Relations recipes establish exact structural claim/instance derivation; an
Analysis relation or theorem must separately establish satisfaction or
soundness preservation.

## 6. Relations ownership and grounding

### 6.1 Initial Oracle statement

The initial relation Interface has:

- public fields for the exact member descriptor and `sigma_0`;
- one `OracleStatement` whose material type is `OracleCarrierType(O_0)` and
  whose access law is the exact grouped encoding; and
- private witness `f_hat_0` for the honest-prover relation, when that witness
  is requested rather than merely a proximity language instance.

Its `ProtocolRelationBinding` uses `LogicalOracleTarget(O_0)`. This is legal
because `O_0` is exactly `InitialOracle + LogicalAccess`. The binding maps the
publication occurrence and every selected public query/answer pair. Exact
whole-carrier agreement is asked only through the causal confidential
initial-Oracle view; the public run view never exposes the carrier.

The `RelationInstance` owns public member values and the Oracle public binding
descriptor. A fresh `OracleMaterialAssignment` owns the private grouped
carrier. The Core's initial-Oracle supply and the relation assignment must be
the same occurrence under the causal material-agreement question. Equal
carriers, equal bytes, or equal digests from another occurrence do not pass.

### 6.2 Proof-sent folded Oracle

`O_1` cannot use `LogicalOracleTarget`: that arm intentionally admits only an
initial Oracle. Reclassifying `O_1` would erase the source fact that it is a
prover publication after `alpha_0`.

Instead the output claim uses a WHIR folded-code relation Interface with:

- public fields for `L_1`, `m_1`, `w_hat_1`, and `sigma_1`; and
- one private witness occurrence whose type is `OracleCarrierType(O_1)`.

The Plan exports the exact carrier used to supply `O_1` at the same decision
site. A `PlanWitnessBinding` maps that `DerivedWitnessExport` to the folded-code
relation witness. Therefore the relation witness and the ProverOracle move are
one recipe value occurrence, not two values compared by label or digest.

Public `O_1` queries and answers remain Core run facts and are inputs to the
final checks. Their correspondence to the private carrier follows from the
Core Oracle engine and the causally generated Plan run. The witness binding
does not publish the carrier and does not turn the proof Oracle into a
relation-owned execution object.

### 6.3 Claim meaning graph

The binding contains two topologically ordered meanings:

```text
M_initial:
  source = C_initial
  relation instance = initial constrained-code instance

M_folded:
  source = ReductionOutput(R_fold,0)
  recipe input = M_initial
  transform parameters = exact R_fold side inputs, challenges,
                         publications, and O_0 answer
  relation instance = folded constrained-code instance
```

`R_final` consumes `M_folded` and has no relation-instance output. Its
applicability question can ask whether the complete final-check conjunction
discharges the selected claim. That question remains distinct from theorem
truth and from the terminal verdict.

## 7. Honest ProverPlan

The Plan has one `WitnessIngress` for `f_hat_0`. A Relations witness binding
attaches it to the initial relation witness. All other secret state is either
explicit Plan state or derived recipe material; there is no ambient polynomial
registry.

The decision recipes are:

| Decision | Exact allowed reads | Output recipe |
|---|---|---|
| `h_0` | `f_hat_0`, static member | derive initial Sumcheck polynomial |
| publish `O_1` | `f_hat_0`, observed `alpha_0` | fold one variable, form exact grouped carrier, use it both as Oracle move and derived witness export |
| `y_ood` | retained folded polynomial, observed `z_ood` | evaluate `f_hat_1` at derived OOD point |
| `h_1` | folded polynomial, `h_0`, `alpha_0`, `z_ood`, `y_ood`, `shift` | derive evolved weight and next Sumcheck polynomial |
| `f_final` | folded polynomial, `alpha_1` | fold final variable and return typed zero-variable polynomial |

The Plan cannot read `final_samples` or any Oracle query/answer at an earlier
decision because they do not exist in the owner-issued decision view. The
Core strategy interface therefore enforces the source non-anticipation shape
rather than trusting the recipe author.

At the `O_1` decision, the carrier node is referenced by both:

```text
ProverMoveBinding = Oracle(O_1, carrier_node)
DerivedWitnessExport("folded-oracle-1") = OracleValue(carrier_node)
```

`PlanRealizes` checks that the move has exactly
`OracleCarrierType(O_1)`, that every read is owner-available, and that the
export root is the identical site-local value. `PlanWitnessSurface` then
exposes only the typed export key and occurrence class. Relations' live
extraction authority retains the private source coordinate.

This establishes honest construction dataflow only. It does not establish
that the recipe algorithms implement the paper, that `f_hat_0` is satisfying,
or that the generated carrier is close to the claimed code.

## 8. Identity and authority graph

The durable dependency direction is acyclic:

```text
Foundation value/algorithm/module profiles
                |
                v
        InteractiveCore --------> Fresh Protocol
                |                       |
                |                       +--> ProtocolInterface
                |                       +--> ProverPlan
                |                               |
                |                               +--> PlanWitnessSurface
                |
Relations definitions/interfaces/instances
                |
                +--> ProtocolRelationBinding <--- Protocol
                +--> PlanWitnessBinding <--- PlanWitnessSurface
                +--> Claim/Reduction meanings

Analysis property/theorem profiles consume qualified owner views;
they do not enter Protocol or Relations identity.
```

The identity consequences are:

- changing a domain, field type, grouped coefficient order, occurrence,
  challenge type, check algorithm, or reduction role rotates `CoreId` and its
  dependent Protocol, Interface, Plan, and relation bindings;
- changing only Fresh to checked Fiat--Shamir preserves `CoreId` and creates a
  different `ProtocolId`;
- changing an honest recipe while preserving the verifier interaction rotates
  `ProverPlanId`, not `CoreId`;
- changing the relation predicate or claim transform rotates the corresponding
  Relations identities, not `CoreId`;
- runtime Oracle carriers, messages, challenges, and statement values belong
  to invocation/run and relation-instance occurrences, not `CoreId`; and
- a later theorem source or proof rotates Analysis subjects, not the protocol.

Process-local admission, run, Plan generation, confidential Oracle view, and
source-view capabilities remain nonserializable authority. Their values and
digests cannot mint replacements.

## 9. Optional commitment and Fiat--Shamir route

Construction 5.1 itself ends at the Fresh logical-Oracle Core. A transparent
noninteractive argument follows a separate checked path:

```text
Fresh logical-Oracle Core
  --checked Oracle-commitment construction-->
Fresh commitment/opening Core
  --checked canonical or duplex transcript construction-->
Fiat--Shamir commitment/opening Protocol
```

The first construction replaces logical access with exact commitment,
opening, authentication, and query-answer machinery for both initial and
proof Oracles. Its static elaboration preserves every source occurrence and
creates construction-owned publications needed by the transcript. The second
construction derives challenge influence from the complete reduction role
sets above.

Direct Fiat--Shamir over `O_0` or `O_1` logical access is refused as support:
the logical fixation marker contains no carrier-derived binding, and the
verifier's later queries cannot authenticate a prover-controlled Oracle in a
noninteractive proof. A nominal hash label or implementation Merkle tree does
not repair that semantic gap.

Even the checked two-step construction establishes only structural
correspondence. BCS applicability, binding, round-by-round restoration, ROM or
QROM security, salting, proof-of-work placement, and quantitative loss remain
Analysis properties with exact theorem premises.

## 10. Failure and terminal semantics

The successful path reaches `Accept` only when every check is true, both
linear reductions are saturated, and no claim remains live. The unconditional
final terminal is `Reject`; a false check deactivates the guarded reductions
and accepting terminal.

The following are not ordinary protocol rejection and retain their qualified
operation outcomes:

- malformed field, polynomial, Oracle, or domain values;
- missing or wrong initial-Oracle supply authority;
- a prover strategy that stops or supplies the wrong message/Oracle type;
- an unsupported exact algorithm or evaluator;
- deterministic resource-limit exhaustion;
- an illegal Oracle index or wrong query/answer occurrence; and
- failed checked construction or replay authority.

No operational failure is converted to a false theorem, a successful Reject
trace, or a partial relation result.

## 11. Resource accounting

The exact member is inside every frozen finite bound:

| Resource | Exact amount or bound |
|---|---:|
| Initial grouped Oracle entries | 4 |
| Proof grouped Oracle entries | 2 |
| Maximum entries per Oracle | 4 and 2, both below `2^14` |
| Public Oracle queries | 3 |
| Public Oracle answers | 3 |
| Prover publications | 5 (`h_0`, `O_1`, `y_ood`, `h_1`, `f_final`) |
| Fresh challenge messages | 5 |
| Boolean verifier checks | 5 |
| Linear claim reductions | 2 |
| Sumcheck polynomial coefficients | 6 total |
| Final polynomial coefficients | 1 |

Domain predicates and lookups use the frozen exact finite scans and their
preflighted step bounds. All arithmetic algorithms have finite typed terms or
exact module dependencies. Guards are ordinary exact Boolean algorithms; no
decision-diagram expansion is introduced.

General WHIR families may require Oracles far larger than `2^14`. The current
constructive member does not prove family-wide capacity. Larger explicit or
algorithmic carriers belong to the separately queued Oracle-resource research
package unless another holdout demonstrates that the finite cap contradicts
the intended v0 scope.

## 12. Exact nonclaims

This constructive mapping establishes none of the following:

- a theorem that the grouped encoding is equivalent for every WHIR parameter;
- implementation support for WHIR;
- source-code or proof-byte compatibility with the official repository;
- theorem applicability or round-by-round soundness for the `F_17` member;
- completeness, proximity, knowledge, zero knowledge, ROM, or QROM security;
- a secure commitment or Fiat--Shamir compiler;
- production parameter adequacy; or
- support for unbounded or dynamically generated Oracle domains.

