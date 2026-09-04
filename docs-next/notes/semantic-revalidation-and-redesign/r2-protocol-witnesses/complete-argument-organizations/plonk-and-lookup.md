# PLONK with One Plookup Argument

> **Portfolio case:** PLONK with permutation and one lookup argument
> **Depth:** T2 constructive encoding
> **Result:** `ProfileOrModule`; the shared model is sufficient, with one
> public prover-parameter lifecycle candidate routed forward
> **Authority:** Source-grounded temporary research, not a conformance or
> security claim

## 1. Source lock and selected interpretation

The semantic sources are:

1. Gabizon, Williamson, and Ciobotaru,
   [PLONK](https://eprint.iacr.org/2019/953), archive revision
   `20250717:105152`, PDF SHA-256
   `9dc9f64d973e81a9255fbf0c6c75aa647ca277027848c49b61311124af9830ac`;
2. Gabizon and Williamson,
   [Plookup](https://eprint.iacr.org/2020/315), archive revision
   `20201120:152004`, PDF SHA-256
   `787c31eaf4d072849c2d66595ca244ccdbec00e1f3a29325200326826460301a`; and
3. Maller et al., [PlonKup](https://eprint.iacr.org/2022/086), archive
   revision `20220312:180406`, PDF SHA-256
   `bb65371cd681cbdca2cd74fa1d14caa7b0e7a55b8805943b55bbba32ac918572`,
   used only as integration pressure.

Original PLONK fixes the arithmetic/permutation protocol and its KZG-compiled
Fiat--Shamir organization. Original Plookup fixes the lookup polynomial
protocol. Plookup by itself is not a complete SNARK: it delegates commitment,
quotient, opening, and Fiat--Shamir compilation to an enclosing system.

PlonKup is not adopted literally. Its displayed integrated protocol contains
identity-bearing inconsistencies, including an unused challenge, an undefined
challenge name, one quotient exponent mismatch, inconsistent batching order,
and a relation display containing challenge-dependent derived material. The
selected target is therefore an explicitly reconciled PLONK + Plookup profile,
not literal PlonKup conformance.

## 2. Owner graph

```text
RelationDefinition
  fixed circuit, public-input rows, copy permutation, and table
          |
          v
InteractiveCore
  exact publications, challenges, checks, claims, and terminal
          |
          +-- TranscriptConstruction: exact Fresh/FS interpretation
          +-- KZG verifier profile: exact two-point opening check
          |
          v
ProtocolInterface / OIR
  external group/scalar proof record and codecs

ProverPlan
  wires, blinding, sorting, grand products, quotient, openings
  + optional separated proving material through the PublicProverParameter candidate

Relations
  Statement/witness/claim/reduction and commitment grounding

Analysis / Evidence
  preprocessing correspondence, setup trust, completeness,
  soundness/knowledge, Fiat--Shamir, zero knowledge, and losses
```

No `Argument`, `LookupArgument`, polynomial object, or proof-package root is
introduced.

## 3. Fixed relation and setup

For fixed circuit `C` and lookup table `T`, the base relation is:

```text
R_C,T(public_input u, witness wires w) iff
  public rows route exactly to u
  and every arithmetic gate equation holds
  and every copy-permutation edge preserves its wire value
  and every lookup-enabled wire tuple belongs to T
```

The relation does not contain transcript challenges, compressed tuples,
sorted helper columns, grand products, quotient polynomials, evaluations, or
opening proofs. Those are proof-construction and verifier material.

Three source setup roles remain distinct; a fourth row records only the
optional minimal-verifier Plan candidate:

| Role | Owner and lifecycle |
|---|---|
| verifier SRS capabilities | Core runtime `PublicParameter`, through the exact KZG setup roles |
| circuit verification key | separate Core `PublicParameter` |
| common preprocessed input selected by the source | Core public binding and canonical transcript influence |
| an additional prover-only projection in the minimal-verifier target | candidate Plan public prover parameter, not an extra transcript binding |

The source's common preprocessed input must remain transcript-bound. The Plan
lane is used only for a separately identified prover-only projection; it may
not remove common setup from Fiat--Shamir influence. A source-level profile
that keeps the whole common setup as a Core parameter remains expressible.

The raw circuit, table, and permutation stay in `RelationDefinition`.
Correspondence between that definition, circuit preprocessing, verification
key, and prover material is a named Analysis/Evidence premise. Successful Core
verification does not establish it.

## 4. Representative complete schedule

Use disambiguated target names while retaining source-name correspondence:

| Order | Core occurrence | Role |
|---:|---|---|
| init | bind verifier SRS, circuit VK, and Statement `u` | setup and public input |
| 1 | `ProverMessage(A,B,C)` | wire commitments |
| 2 | challenge `rho_lookup` | lookup tuple compression |
| 3 | `ProverMessage(F,H1,H2)` | compressed query and sorted-sequence commitments |
| 4 | joint challenge tuple `(beta,gamma,delta,epsilon)` | permutation and lookup products |
| 5 | `ProverMessage(Z_perm,Z_lookup)` | grand-product commitments |
| 6 | challenge `alpha` | quotient combination |
| 7 | `ProverMessage(Q_lo,Q_mid,Q_hi)` | split quotient commitments |
| 8 | challenge `zeta_eval` | evaluation point |
| 9 | `ProverMessage(evaluation_record)` | twelve asserted evaluations |
| 10 | challenge `v` | same-point claim aggregation |
| 11 | `ProverMessage(W_zeta,W_shifted)` | two opening proofs |
| 12 | challenge `eta` | independent-proof equation aggregation |
| 13 | exact algebraic reconstruction check | quotient and linearization |
| 14 | exact two-point KZG check | ordered opening claims and evidence |
| 15 | `Accept` iff both checks are true; otherwise `Reject` | terminal |

The four-member challenge tuple is either one exact joint-law draw or four
explicit independent members of a source-defined joint group. Four decoded
hash outputs are not assumed independent merely because they occupy different
fields.

All root bindings and every prover publication before a later challenge are
automatically in the canonical framed transcript. `eta` occurs after both
opening proofs. Moving it earlier is the exact Last-Challenge failure this case
is meant to expose.

## 5. Proof package

One representative external package has thirteen group elements:

```text
A, B, C,
F, H1, H2,
Z_perm, Z_lookup,
Q_lo, Q_mid, Q_hi,
W_zeta, W_shifted
```

and twelve field elements:

```text
a(zeta), b(zeta), c(zeta),
sigma1(zeta), sigma2(zeta),
f(zeta), t(zeta), t(omega*zeta),
Z_perm(omega*zeta), Z_lookup(omega*zeta),
H1(omega*zeta), H2(zeta)
```

This is an Interface/OIR record projected from typed Core publications. It is
not one pre-challenge Core message. OIR may choose a physical field order only
under an exact invertible projection to these semantic roles.

## 6. Quotient and claim structure

The exact algebraic profile retains independently weighted terms for:

- arithmetic gates and public-input routing;
- permutation recurrence and boundary `Z_perm(1)=1`;
- lookup-enabled wire-to-compressed-query linkage;
- lookup recurrence and boundary `Z_lookup(1)=1`;
- vanishing-polynomial division; and
- exact three-chunk quotient recombination.

The verifier derives its linearization commitment from the fixed VK
commitments, both product commitments, all quotient chunks, challenges, and
asserted evaluations. A successful reconstruction is a verifier check, not a
relation-satisfaction theorem.

Claims and reductions should expose meaningful logical boundaries only. There
is no benefit in inventing one reduction per round. A later owner-local
Relations module may record transformations such as tuple membership to random
compression to lookup identities to quotient evaluation, while Analysis owns
their theorem meaning.

## 7. Exact KZG verifier use

One PLONK-specific two-point profile is selected instead of composing several
loosely related generic profiles.

At `zeta_eval`, the ordered claims are:

```text
r(zeta)=0,
a(zeta), b(zeta), c(zeta),
sigma1(zeta), sigma2(zeta),
f(zeta), t(zeta), H2(zeta)
```

with weights `1,v,...,v^8`.

At `omega*zeta_eval`, the ordered claims are:

```text
Z_perm(omega*zeta),
t(omega*zeta),
Z_lookup(omega*zeta),
H1(omega*zeta)
```

with weights `1,v,v^2,v^3`.

The evidence is `(W_zeta,W_shifted)`, and verification context includes both
`v` and `eta`. The required schedule is:

```text
all commitments and evaluations
    < v
    < both opening proofs
    < eta
    < final KZG check
```

Using a same-point-only profile would erase the second point and the later
proof-equation aggregation. Treating either opening proof as an asserted answer
would erase the claim/evidence distinction.

## 8. Failure partition

| Condition | Result |
|---|---|
| malformed bytes, noncanonical field/point, wrong record arity | Interface/OIR `Malformed`; no Core run |
| missing verifier SRS or VK | `MissingDependency` or `Refused` |
| unsupported field/group/pairing primitive | `Unsupported` |
| canonical FS sampling exhaustion | `InterpretationFailed` |
| honest prover denominator or construction failure | Plan/strategy `Stop`; no terminal |
| algebraic identity false | Core `Reject` |
| KZG predicate false | Core `Reject` |
| deterministic evaluator bound exhausted | `DeterministicLimitExceeded` |
| preprocessing/setup premise missing | Analysis cannot activate; not Core rejection |

The noninteractive package contains no public abort message. Honest generation
failure therefore remains operational noncompletion; converting it into
`Reject` would change the source protocol.

## 9. Negative mutations

The constructive encoding distinguishes at least these changes:

1. omit or delay Statement or VK binding;
2. draw `rho_lookup` before `A,B,C`;
3. publish `F,H1,H2` before `rho_lookup`;
4. draw product challenges before `F,H1,H2`;
5. draw `alpha` before both grand-product commitments;
6. draw `zeta_eval` before every quotient chunk;
7. draw `v` before the full evaluation record;
8. draw `eta` before either opening proof;
9. omit, duplicate, or reorder one opening claim;
10. swap two claims while retaining their old powers of `v`;
11. replace the two-point profile by a same-point profile;
12. omit a permutation or lookup boundary term;
13. omit the lookup-enabled wire-to-`f` linkage;
14. change the inactive-row sentinel;
15. change a quotient recombination exponent;
16. omit the shifted-point opening;
17. reuse challenges across permutation and lookup without a theorem premise;
18. pair a VK with another relation definition or SRS and retain theorem
    applicability; or
19. infer relation satisfaction, knowledge, zero knowledge, setup trust, or
    Fiat--Shamir security from an accepting execution.

## 10. Constructive T2 ledger

This section closes the constructive-accounting requirement without claiming a
concrete byte fixture. One representative member fixes the following finite
parameters once and for all:

```text
MemberParams = {
  field F0 and exact canonical field type,
  groups G1_0, G2_0, GT_0, pairing e0, and canonical point types,
  n0 > 1, omega0 of exact order n0, and 0 <= ell0 < n0,
  disjoint cosets H0, k1*H0, k2*H0,
  three n0-row witness columns and one fixed three-column n0-row table,
  six selector columns including qK and one permutation of 3*n0 positions,
  maximum polynomial degrees and exact KZG setup shape listed below,
  one exact transcript construction, challenge decoder, and retry bound,
  one exact circuit/preprocessing profile and proof-field codec profile
}
```

`F0`, `G1_0`, `n0`, `omega0`, `C0`, `T0`, `SRS0`, `VK0`, and the algorithm
references below are symbolic names in this document, but each denotes one
exact canonical finite value or identity within this member. They are not
universally quantified placeholders, ambient registry names, or values chosen
after admission. Concrete octets and measured provider behavior are deferred
to T3. Runtime challenges, witness values, blinders, and proof messages vary
within the already fixed finite types and bounds.

### 10.1 Owner objects and symbolic identity dependencies

| Object | Exact owner and identity inputs |
|---|---|
| algebraic module set | Foundation; field/group/pairing types, canonical operations, polynomial-vector operations, and their evaluation contracts |
| `RelationDefinition(C0,T0)` | Relations; public-row routing, selectors, permutation, table, and the gate/copy/lookup predicate |
| `RelationInterface(C0,T0)` | Relations; the exact `ell0`-element public-input type and `(3*n0-ell0)`-element private wire-suffix type over that definition |
| KZG verifier profile | PIR commitment-opening owner; static algebraic parameters, setup-role types, thirteen ordered claim roles, two challenge-context roles, evidence type, exact algorithms, schedule graph, and intrinsic bounds |
| `InteractiveCore` | PIR; imported module IDs, three root-binding declarations, typed round records, nine challenge declarations, derived values, two checks, initial claim, two terminals, and the exact occurrence order in Section 4 |
| Fresh `Protocol` | PIR; the exact `CoreId` plus the Fresh interpretation |
| `TranscriptConstruction` and FS `Protocol` | PIR; exact `CoreId`, framing, application domain, initial state, challenge algorithms/retry bounds, then that construction identity with the same `CoreId` |
| `CommitmentOpeningUse` | PIR; exact `CoreId`, KZG-profile ID, SRS binding, thirteen claim coordinates, `(v,eta)` context coordinates, two-proof evidence coordinate, both check coordinates, and exact bounds |
| `ProverPlan` | PIR Plan owner; exact FS `ProtocolId`, private wire-suffix ingress, public Statement read, advice/blinding classes, finite randomness requirements, persistent polynomial state, six decision recipes, and exact portable algorithm dependencies |
| `ProtocolInterface` | PIR Interface owner; exact FS `ProtocolId`, public Statement field, thirteen group fields, twelve scalar fields, and their role/codec projection |
| OIR projection | OIR; exact admitted Interface plus the selected verifier or Plan-realized prover view, never a second protocol or proof identity |
| `ProtocolRelationBinding` | Relations; exact `ProtocolId`, relation Interface, Statement edge, initial-claim meaning, and any admitted transform meanings |
| `PlanWitnessSurface` and witness binding | PIR then Relations; exact protocol and one structured private wire-suffix ingress entry, followed by its occurrence-exact relation-witness edge |
| source/preprocessing/property records | Evidence and Analysis; the three source pins, reconciliation manifest, `(C0,T0,SRS0,VK0)` preprocessing proposition, setup premise, and property questions |

Runtime `SRS0`, `VK0`, and `u0` assignments change the invocation identity, not
the generic Core or verifier-profile identity. `C0` and `T0` remain fixed by
the relation and preprocessing profile selected for this member. Source PDF
hashes and source-correspondence records do not enter `CoreId` merely because
they justify its design. The proof record is a run/OIR value and has no new
semantic root identity.

The active T2 member uses the source-conservative route: all common setup that
the source transcript binds is available through the root Core parameters.
Additional prover material is either an exact Plan constant in this finite
member or an exact projection of that already bound setup. The reusable
`PublicProverParameterDecl` lifecycle remains a later candidate and is not a
hidden dependency of this construction.

### 10.2 Closed construction graph

```text
Foundation algebraic modules
  -> RelationDefinition(C0,T0) -> RelationInterface(C0,T0)
  -> KZGVerifierProfile
  -> InteractiveCore

InteractiveCore + Fresh interpretation
  -> FreshProtocol

InteractiveCore + TranscriptConstruction
  -> FSProtocol

InteractiveCore + KZGVerifierProfile
  -> CommitmentOpeningUse

FSProtocol
  -> ProverPlan -> affirmative PlanRealizes -> Plan-specialized prover view
  -> ProtocolInterface -> verifier OIR projection
  -> ProtocolInterface + PlanRealizes -> prover OIR projection

FSProtocol + RelationInterface
  -> ProtocolRelationBinding

ProverPlan -> PlanWitnessSurface
PlanWitnessSurface + RelationInterface
  -> PlanWitnessBinding

exact invocation + run + relation assignments
  -> grounding/correspondence questions
  -> separately applicable Analysis questions
```

The PLONK arithmetic, copy-permutation, Plookup, quotient, and PCS portions are
owner-local modules inside one Core. Composition is their exact interleaving
and shared derived-value graph from Sections 4--7; it is not a composition of
independently executing child Cores. In particular, `rho_lookup` links wires to
the lookup query, `alpha` combines all quotient terms, and `(v,eta)` jointly
determine the one final two-point opening predicate.

The Plan has exactly six decision recipes, one for each grouped prover message
in Section 4. Each recipe reads only the admitted current `ProverView`, earlier
Plan state, fixed private material, and randomness available by that boundary.
Its nodes use fixed-size coefficient vectors rather than an open polynomial
object. `PlanRealizes` checks structural coverage and causal reads; it does not
prove honest-generation completeness or any algebraic theorem.

### 10.3 Grounding and correspondence obligations

The complete member names, but does not conflate, these obligations:

1. the Statement edge maps the exact root binding `u0` to every and only public
   occurrence of `RelationInterface(C0,T0)` required by the selected coverage
   question;
2. one occurrence-exact witness edge maps the Plan's structured private
   wire-suffix ingress to the relation witness; the Plan combines it with the
   public Statement to derive the three full wire columns. Blinding randomness,
   sorting advice, and quotient/opening state are not relation witness;
3. the initial Core claim receives the exact relation meaning, while tuple
   compression and quotient/evaluation meanings, if retained, cite exact
   package-local transforms and their challenge/publication coordinates;
4. the commitment-opening use maps every linearization/evaluation commitment,
   point, asserted answer, and both proof elements to the exact coordinates in
   Section 7; the claim-group and opening checks are required by every accepting
   terminal;
5. a separately checked preprocessing proposition relates `(C0,T0,SRS0)` to
   `VK0` and to any Plan-only proving projection. Equal types, matching names,
   or successful verification do not discharge it; and
6. run-grounded acceptance, relation satisfaction, completeness, soundness,
   knowledge, setup trust, and Fiat--Shamir applicability remain different
   questions with independently supplied premises.

Ordinary blinded proof commitments are realized by Plan recipes, not forced
through `CommitmentGrounding`: their preimages contain Plan randomness and
derived polynomial state that are intentionally not relation witness. The KZG
use establishes the exact verifier predicate only; binding, extraction, and
knowledge remain Analysis obligations. A circuit-VK commitment may be checked
against preprocessing evidence, but that does not turn the verification key
into Statement or universal SRS.

### 10.4 Failure closure

Section 8's cases partition into four non-overlapping owner boundaries:

| Boundary | Closed result class |
|---|---|
| malformed carrier, wrong kind/ABI, missing dependency, unsupported primitive, or refused authority | qualified formation/admission failure; no admitted use or semantic run |
| challenge sampling failure, strategy stop, unavailable capability, or deterministic resource exhaustion | interpretation or operational noncompletion; no Core terminal |
| both exact checks true, or at least one exact check false | Core `Accept` or fallback `Reject` respectively |
| missing/false preprocessing or theorem premise | correspondence/Analysis noncompletion or Negative; never retroactively changes the Core verdict |

No decoder error, division failure, provider exception, or exhausted limit is
encoded as a false algebraic or KZG check. No partial admitted object or partial
semantic verdict is retained.

### 10.5 Finite intrinsic bounds

For fixed `n0` the representative member has these intrinsic cardinalities:

| Surface | Exact bound |
|---|---:|
| root public bindings | `3`: verifier SRS, circuit VK/common preprocessing, Statement |
| public / private wire cells | `ell0 / (3*n0-ell0)`; together they form the `3*n0` wire assignment |
| table cells | `3*n0` |
| grouped prover-message occurrences | `6` |
| group-element proof fields | `13` |
| scalar proof fields | `12` |
| Challenge declarations | `9`: one lookup compression, four product members, and `alpha,zeta_eval,v,eta` |
| check occurrences | `2` |
| terminal declarations | `2`: `Accept` and unconditional fallback `Reject` |
| KZG opening claims | `13`: nine at `zeta_eval`, four at `omega0*zeta_eval` |
| KZG context values / evidence fields | `2 / 2` |

The counts have two explicit provenance classes. The selected reconciled source
profile supplies six round outputs; its complete-proof listing supplies thirteen
group elements and twelve scalars; its two opening numerators supply nine
same-point terms (`r` plus eight opened polynomials) and four shifted-point
terms; and its declared challenge schedule supplies nine occurrences after the
displayed but unused `theta` is removed by the reconciliation manifest. The
three root bindings, two separately identified checks, and two terminals are
instead exact carrier choices of this finite Core member. They are not asserted
as universal PLONK cardinalities. In particular, changing the reconciliation,
linearization, proof packaging, or KZG batching profile requires a new member
and recomputation of these counts.

The source-selected polynomial-vector bounds are fixed as follows:

```text
deg(qM), deg(qL), deg(qR), deg(qO), deg(qC), deg(qK) < n0
deg(T1), deg(T2), deg(T3), deg(t), deg(sigma1), deg(sigma2),
  deg(sigma3), deg(public_input_polynomial) < n0
deg(a), deg(b), deg(c), deg(f) < n0 + 2
deg(H1), deg(Z_perm), deg(Z_lookup) < n0 + 3
deg(H2), deg(W_zeta), deg(W_shifted) < n0 + 2
deg(r) < n0 + 3
deg(Q) < 3*n0 + 5
deg(Q_lo), deg(Q_mid), deg(Q_hi) <= n0 + 1
universal G1 SRS powers: tau^0 through tau^(n0+5)
verifier G2 basis: the exact generator/hidden-point elements required by the
  selected two-point profile
```

These degree and SRS formulas are the bounds printed by the selected integrated
source anatomy for its wire, query, sorted-helper, product, quotient-chunk, and
opening polynomials. They are retained as part of this profile's explicit
reconciliation, not inferred from generic Plookup and not generalized to every
PLONKish argument. If a later reconciliation changes a quotient term, blinding
degree, sentinel convention, or chunking rule, these formulas rotate with the
profile rather than remaining ambient architecture constants.

Every record, coefficient vector, sort input, product scan, FFT/domain
operation, multiscalar multiplication, and pairing request therefore has one
finite type-derived input bound. Let `R_c` be the exact admitted maximum draw
count of challenge `c`; transcript squeezing performs at most
`sum_c R_c` attempts over the nine declarations. The construction profile fixes
the maximum frame size, and the KZG profile/use stores exact bounds for its three
packers, claim-group check, opening check, and setup assignment. The Plan stores
the exact per-recipe node count, state width, randomness count, and evaluation
contracts. Admission derives their finite sum and rejects an insufficient or
inconsistent declared bound.

These are intrinsic bounds for this one member. They are not measured runtime,
asymptotic complexity, a uniform constructor for every `n`, or evidence that a
current provider implements the algorithms.

## 11. Classification and nonclaims

The shared architecture is sufficient. Owner-local additions are still
substantial: a fixed circuit/table relation language, exact finite-field/group
algorithms, the protocol module, source-reconciliation manifest, two-point KZG
profile, Plan, Interface, OIR package, Relations bindings, and Analysis
questions.

The result is `ProfileOrModule`, not implementation support. It establishes no
completeness, soundness, knowledge, setup trust, binding/extraction, challenge-
sharing theorem, ROM/QROM result, zero knowledge, codec conformance, backend
support, or performance claim.

The current `plonk-kzg-boundary.mlir` fixture preserves part of the original
PLONK challenge schedule and ends with explicit verifier residuals. It is useful
implementation pressure only: it contains no Plookup integration and no
complete final KZG verifier.
