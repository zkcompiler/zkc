# Circle STARKs Boundary Analysis

> **Kind:** Temporary source reconstruction, frozen-target pressure test, and
> adjudication record
> **State:** Complete
> **Frozen target:** `63c48b22c7aac56d9af3ab460e4ea135a87039f3`
> **Decision:** `ProfileOrModule`; no shared semantic profile rotates
> **Authority:** None

## 1. Question and assigned depth

This holdout asks whether the frozen semantic model can represent the protocol
in *Circle STARKs* without silently assuming that every evaluation code is an
ordinary univariate Reed--Solomon code over a multiplicative subgroup.

The assigned depth is **boundary analysis**, not a constructive fixture. It
must reconstruct the source distinctions, locate their exact semantic owners,
and exhibit any first failed mapping. It need not instantiate the paper's
parameters or establish the paper's theorems.

The primary classification is **`ProfileOrModule`**. Circle-specific domains,
function spaces, projections, folding algorithms, and AIR predicates require
exact owner-local modules and profiles. The shared Protocol, Plan, Relations,
commitment, transcript, and identity grammar does not require an extension.

This result is conditional on the declared finite-v0 carrier boundary. It is
not evidence that practical Circle STARK traces fit the current constitutional
size limits.

## 2. Source lock and evidence boundary

The primary source is:

- Ulrich Haboeck, David Levit, and Shahar Papini, *Circle STARKs*, IACR
  ePrint 2024/278, exact PDF recorded in `source-ledger.json`.

The source was read for its circle domains and function spaces, Circle FRI,
batching, AIR protocol, theorem premises, knowledge-soundness statement, and
zero-knowledge variants. The Stwo repository was consulted only as
supplemental evidence that the construction has a realization using M31,
circle FFTs, FRI, commitments, and Fiat--Shamir. It is not semantic authority
for the paper and is not evidence of theorem truth or production security.

Source theorem statements are kept separate from the protocol reconstruction:

- Protocol 1 is Circle FRI;
- Protocol 2 is Batch Circle FRI;
- Protocol 3 is the Circle IOP for AIR;
- Theorem 6 is the Batch Circle FRI soundness statement;
- Theorems 7 and 8 state AIR soundness and knowledge soundness under the
  paper's exact premises; and
- Remark 19 postpones the random-oracle SNARK transformation rather than
  specifying one.

No theorem is activated by this boundary analysis.

## 3. Source-native anatomy

### 3.1 Algebra and evaluation domains

The protocol is built over the circle

```text
C(F_p) = { (x,y) in F_p^2 : x^2 + y^2 = 1 }.
```

For the selected primes, the group of circle points has smooth order. Standard
position cosets and twin-cosets provide recursively related evaluation
domains. The folding map is induced by a two-to-one projection of circle
points; its fibres and twiddle factors are part of the protocol's algebra, not
host indexing conventions.

The function space is the quotient algebra
`F_p[x,y] / (x^2 + y^2 - 1)` and the paper's nested circle function spaces,
rather than an ordinary univariate polynomial space. The associated circle
codes are generalized Reed--Solomon codes.

There is a one-dimensional gap between the image of the circle FFT basis and
the full function space used in the code. The protocol exposes the missing
coefficient as a scalar; the gap is not an implementation accident.

### 3.2 Circle FRI

At a source-faithful level, Circle FRI contains:

1. an initial Oracle purporting to be an evaluation of a function in a circle
   code;
2. a prover publication of the dimension-gap scalar;
3. repeated fresh verifier coefficients;
4. repeated prover Oracles obtained by a source-defined two-to-one fold;
5. a final low-dimensional function sent explicitly; and
6. a decision phase that samples source-domain positions, opens the required
   fibres, checks each fold equation, and checks the final object.

The source's batching protocol first samples a coefficient and combines a
typed batch of functions, then runs the same Circle FRI machinery on the
combined function. The batch-combination equation remains a verifier check; it
is not an implicit host operation.

### 3.3 Circle IOP for AIR

The AIR protocol contains:

- trace columns evaluated on a standard-position trace domain;
- local and next-row constraint expressions, with periodic selectors;
- trace Oracles over a larger, disjoint evaluation domain;
- a fresh batching coefficient for the constraints;
- a derived quotient, decomposed into lower-dimensional pieces plus the
  dimension-gap scalar;
- a fresh out-of-domain circle point over an extension field;
- claimed evaluations at that point and at its successor;
- DEEP quotient functions; and
- a batched Circle FRI reduction followed by an identity check at the sampled
  point.

The source therefore has all of the following as distinct objects: an AIR
statement, witness trace, trace codewords, quotient codewords, public
challenges, out-of-domain evaluations, logical Oracle queries, reduction
claims, and final checks.

### 3.4 Variants that must not collapse

The paper discusses both randomized/zero-knowledge-oriented constructions and
an optimized variant in Appendix C whose evaluation-domain choice is
explicitly non-zero-knowledge. These are different protocol and Analysis
subjects. A profile may not attach a zero-knowledge conclusion to the
non-zero-knowledge variant because their high-level trace shapes look similar.

The verifier's field-membership abort condition is also operationally
meaningful. A query answer outside the declared field does not become a field
element through a decoder convention; the run must refuse or abort at the
typed boundary selected by the exact construction.

## 4. Mapping into frozen owners

### 4.1 Foundation modules own the algebra

No shared `Field`, `Polynomial`, `EvaluationDomain`, or `Codeword` kind is
needed. Exact semantic modules can own:

- the base field and selected extension field;
- circle-point and twin-coset value types;
- finite domain enumeration and membership;
- successor and projection maps;
- fibre enumeration and twiddle factors;
- circle-function and codeword carriers;
- circle FFT and inverse algorithms;
- vanishing-function, quotient, decomposition, fold, and DEEP-quotient
  algorithms; and
- exact failure values for partial source operations.

These algorithms are authenticated semantic dependencies. They cannot be
ambient library callbacks, prose formulas, or implementation-only hooks.
Changing the domain law or folding algorithm rotates its owner-local identity
and every dependent profile, not an unrelated Core.

### 4.2 Interactive Core owns verifier-observable interaction

Each trace, quotient, and folded codeword published as a logical Oracle is an
exact `InitialOracle` or `ProverOracle` according to source origin. Its
`index_type` is the exact circle-domain point or domain-index type; its
`element_type` is the exact field or extension-field value type. Logical
queries and answers remain occurrence-sensitive.

The dimension-gap scalar is an ordinary typed prover Message. Batching
coefficients, fold coefficients, the out-of-domain point, and query positions
are distinct fresh Challenge occurrences with exact source-defined sampling
domains. AIR identities, fold equations, batch equations, and final-codeword
checks are verifier checks.

The initial AIR claim and each quotient, DEEP, and Circle FRI subclaim can be
represented as explicit typed claims connected by reductions. Their exact
mathematical meanings are Relations-owned; their public occurrence and
transition roles are Core-owned.

### 4.3 Prover Plan owns honest construction

The Plan computes trace encodings, quotient decomposition, gap scalars, folded
Oracles, out-of-domain evaluations, DEEP quotients, and the final low-degree
object. Every recipe reads only the public and private values available at its
source site.

Proof-sent codeword Oracles remain `ProverOracle`s. When a Relations profile
needs the exact private function or codeword as a witness, the Plan can export
the same site-local carrier through `DerivedWitnessExport`. It must not
recompute an extensionally equal object after execution or relabel a
proof-sent Oracle as initial material.

This owner split also preserves non-anticipation: query positions remain in
the verifier decision phase and are not exposed to earlier prover recipes.

### 4.4 Relations owns AIR and code correspondence

Owner-local Relations definitions can express:

- AIR satisfaction over the selected trace domain;
- trace-to-codeword correspondence;
- circle-code membership and proximity claims;
- quotient and dimension-gap decomposition;
- batch linear-combination relations;
- DEEP quotient identities;
- circle-fold claim transforms; and
- exact logical-access laws over fibres and successor points.

The relation definition imports the exact circle algebra modules. It does not
gain field semantics from a generic relation evaluator, and the shared
Relations grammar does not inspect circle coordinates.

Lossy or probabilistic implications, including proximity soundness and
constraint batching error, are not value bridges. They belong to Analysis with
their exact error terms and premises.

### 4.5 Commitment and Fiat--Shamir remain checked constructions

The paper's logical IOP is not itself a commitment scheme or a noninteractive
argument. A concrete route first elaborates each logical Oracle through a
checked Oracle-commitment/opening construction. A checked transcript
construction may then interpret the public coins.

The transcript must bind every required statement value, Oracle commitment,
prover scalar, claimed evaluation, and opening/publication occurrence before
the challenge that depends on it. The paper's postponement of its random-oracle
transformation means this analysis does not select a concrete transcript
profile or claim random-oracle security.

### 4.6 Analysis owns theorem applicability and properties

Exact Circle FRI and Circle AIR Analysis profiles are absent from the frozen
publication. A complete profile would have to distinguish at least:

- the exact Batch Circle FRI experiment and correlated-agreement premises;
- the AIR soundness theorem and its complete error expression;
- the knowledge-soundness theorem and extraction premises;
- the randomized zero-knowledge-oriented protocol;
- the explicitly non-zero-knowledge optimized variant; and
- any later commitment and random-oracle compiler theorem.

The paper citation, a Stwo test, or structural protocol admission cannot answer
any of these properties.

## 5. First failed and tempting mappings

The frozen attempt did not encounter a shared grammatical obstruction. It did
expose several tempting mappings that are semantically invalid.

### 5.1 Force circle codewords through an ordinary polynomial profile

**Attempt.** Reuse a multiplicative-subgroup univariate polynomial module by
renaming circle points as indices.

**Failure.** This erases the quotient-algebra function space, twin-coset
structure, two-to-one projections, twiddle factors, and dimension gap.

**Disposition.** Exact circle modules and Relations profiles. This is the
intended module-extension path, not a shared-model repair.

### 5.2 Hide the gap scalar inside a fold evaluator

**Attempt.** Let the implementation silently normalize from the full circle
function space into the FFT-image subspace.

**Failure.** The source publishes the scalar, and later checks depend on its
value. Hiding it changes the transcript and the verifier's observations.

**Disposition.** Preserve it as a typed prover Message and an explicit
decomposition relation.

### 5.3 Treat DEEP quotient codewords as ungrounded virtual callbacks

**Attempt.** Give a logical Oracle a host callback that computes requested
values from prior Oracles and claimed evaluations.

**Failure.** Ambient callbacks have no authenticated semantics, Plan causality,
or exact relation witness. They also obscure whether the prover committed to
the whole derived codeword before seeing queries.

**Disposition.** At this boundary, represent source-published derived
codewords as real ProverOracles produced by exact Plan algorithms. A later
resource package may study nonmaterialized realization without changing the
logical publication.

### 5.4 Infer zero knowledge from randomization

**Attempt.** Attach one zero-knowledge property to every Circle AIR profile
because a randomized trace construction exists in the paper.

**Failure.** The optimized Appendix C variant is explicitly non-zero-knowledge,
and the full property depends on exact leakage, commitment, and compiler
premises.

**Disposition.** Separate Protocol and Analysis identities; leave all results
unevaluated until an exact theorem path exists.

### 5.5 Treat practical domains as admitted finite values

**Attempt.** Generalize from a finite source-shaped member to all practical
trace and codeword sizes.

**Failure.** Frozen Oracle and Foundation sequence limits are explicit and may
exclude practical instances.

**Disposition.** Intentional finite-v0 boundary. Large and algorithmic carriers
remain a separate cross-family research question.

## 6. Falsification matrix

| Mutation | Required result |
|---|---|
| Replace a twin-coset domain by an equal-size multiplicative subgroup | exact module/profile identity mismatch |
| Change circle projection or fibre order while retaining the old module ID | module authentication or law admission refuses |
| Omit the dimension-gap scalar | message/claim/reduction coverage is incomplete |
| Absorb the gap scalar only after the next fold challenge | checked transcript construction refuses required influence |
| Let a fold recipe read a later query position | Plan non-anticipation check is negative |
| Reclassify a proof-sent folded codeword as InitialOracle | origin and causal grounding refuse |
| Deduplicate two equal fibre-query occurrences | logical occurrence correspondence is negative |
| Accept an answer outside the declared field | exact value admission or operational field-membership check refuses |
| Swap the sampled point and its successor | exact typed coordinate/check disagreement |
| Drop one quotient component while keeping the same AIR claim | relation/reduction adequacy is negative |
| Treat the batch coefficient as an implementation RNG call | challenge construction is absent or unsupported |
| Map AIR satisfaction to a successful Plan execution | no implication exists; property remains unanswered |
| Reuse the optimized non-ZK protocol ID with a ZK theorem profile | applicability or identity check refuses |
| Attach Theorem 7 or 8 using only a citation | theorem applicability/truth remains `NotEvaluated` |
| Apply Fiat--Shamir directly to uncommitted logical Oracles | unsupported argument route |
| Exceed the frozen Oracle or Foundation carrier maximum | formation/admission refuses |

These controls distinguish typed refusal, ordinary verifier rejection,
correspondence failure, unsupported construction, and unevaluated Analysis.

## 7. Boundary adjudication

| Pressure | Frozen result | Owner |
|---|---|---|
| Circle point and twin-coset domains | owner-local exact types and laws | Foundation module |
| Bivariate quotient function space | owner-local algebra | Foundation module |
| Dimension-gap coefficient | explicit prover Message and relation | Core + Relations |
| Circle fold and batch fold | exact algorithms and claim transforms | Foundation + Relations |
| Trace, quotient, and folded Oracles | exact logical publications | Core |
| Honest encodings and derived codewords | source-site recipes/exports | Plan |
| AIR predicate and trace grounding | exact relation definitions | Relations |
| DEEP samples and quotient checks | challenges, messages, checks, reductions | Core + Relations |
| Commitment/opening route | separate checked construction | PIR construction |
| Fiat--Shamir route | separate checked construction | PIR construction |
| Soundness, knowledge soundness, and ZK | source-pinned property/theorem profiles | Analysis |
| Practical codeword size | outside finite-v0 member support | future resource package |

No pressure requires Core to know what a field, circle point, polynomial, AIR,
or code is. Adding such shared algebraic kinds would duplicate module and
Relations authority and make the core less general.

## 8. Classification and nonclaims

The primary result is **`ProfileOrModule`**:

- the shared finite Protocol grammar is native;
- the Plan and Relations seams are native;
- circle-specific algebra, AIR, fold, and access laws are owner-local modules
  and profiles;
- exact theorem and property profiles remain unpublished; and
- practical large carriers remain an intentional finite-v0 boundary.

This analysis does **not** establish:

- an executable Circle STARK fixture;
- support for any practical Stwo parameter set;
- equivalence to the Stwo implementation;
- soundness, knowledge soundness, or zero knowledge;
- security of a commitment scheme or Fiat--Shamir transform;
- a concrete field, extension, hash, query, or transcript profile; or
- endpoint, serialization, compiler, or deployment support.

## 9. Retained work and reopening conditions

No shared profile rotates. Retain the following for later packages:

1. exact Circle algebra and AIR module/profile construction if Circle STARKs
   becomes an implementation target;
2. source-pinned Batch Circle FRI and Circle AIR Analysis profiles;
3. an explicit variant split between randomized/ZK-oriented and optimized
   non-ZK protocols;
4. the cross-family study of large or algorithmic Oracles; and
5. a concrete commitment/transcript profile before any noninteractive claim.

Reopen the shared candidate only if a constructive member demonstrates that:

- an exact circle domain cannot inhabit a module-owned `ValueType`;
- a required source publication, challenge, query, answer, check, claim, or
  reduction has no Core representation;
- Plan causality cannot ground a proof-sent derived codeword without changing
  its source origin;
- Relations cannot own the AIR/code law without an opaque evaluator; or
- a protocol-sized carrier is declared in finite-v0 scope but cannot form.

None of those conditions was demonstrated at the assigned depth.
