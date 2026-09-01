# WARPfold Boundary Analysis

> **Kind:** Temporary source reconstruction, frozen-target pressure test, and
> adjudication record
> **State:** Complete
> **Frozen target:** `63c48b22c7aac56d9af3ab460e4ea135a87039f3`
> **Decision:** `ProfileOrModule`; no shared semantic profile rotates
> **Authority:** None

## 1. Question and assigned depth

This holdout asks whether the frozen semantic model can represent WARPfold's
bounded sequential folding over a right field and several non-native
wrongfields without:

- treating modular limb representation as a universally lossless value
  conversion;
- inferring witness equality merely from equal commitment values;
- erasing the degradation counter and finite-fold limit;
- widening strict-plus-relaxed folding into unsupported relaxed-plus-relaxed
  or tree folding; or
- turning heuristic extractor assumptions into established theorems.

The assigned depth is **boundary analysis**. The result is
**`ProfileOrModule`**: the shared Protocol, Plan, Relations, and incremental-
composition grammar is sufficient, while exact multi-field circuits, limb
relations, commitment laws, fold relations, and theorem profiles are
owner-local. The paper's broad “warp between proof systems” application is
under-specified at this depth and is not promoted into a semantic claim.

## 2. Source lock and source quality

The primary source is Lev Soukhanov, *WARPfold: Wrongfield ARithmetic for
Protostar folding*, IACR ePrint 2024/354, exact PDF recorded in
`source-ledger.json`.

The paper is a concise construction note. It gives definitions, one
interactive folding protocol, a sequence extractor argument, weak and
reinforced IVC constructions, and cost discussion. It also states material
limitations and assumptions:

- only a strict instance plus a relaxed instance can be folded;
- relaxed-plus-relaxed and tree-like folding are unavailable;
- only a bounded number of sequential folds is supported;
- the extraction argument is sequence-based rather than a standard folding
  extractor and may be exponential in sequence length;
- the paper does not provide the Algebraic Group Model analysis it suggests
  might be possible;
- weak IVC uses explicitly heuristic noninteractive-extractor assumptions;
- the naïve use of wrongfield arithmetic in the recursive circuit is left as a
  conjectured-unsound construction without a counterexample; and
- reinforced IVC assumes a noninteractive Protostar extractor.

These are semantic and theorem-profile axes, not editorial caveats. The
mapping below preserves each one.

## 3. Source-native anatomy

### 3.1 Underlying multi-round circuit and committed instances

The paper starts from a homogeneous, multi-round algebraic circuit. The public
and private witness spaces are split by round; public challenges alternate
with prover witness material, and a homogeneous constraint map targets a
constraint space. A distinguished relaxation factor allows non-homogeneous
constraints to be represented.

Committed witnesses bind each private round through a linearly homomorphic
commitment. The paper's committed instance links later public challenges to
hashes of earlier challenges and commitments. Its Protostar-style transform
compresses a vector of constraints using one final bounded challenge.

Strict and relaxed instances are different relation subjects:

- a strict instance retains the challenge-hash conditions, unit relaxation
  factor, and zero error; and
- a relaxed instance removes those strictness conditions and carries an error
  term.

### 3.2 Strict-plus-relaxed fold

Protocol 1 starts with one strict instance and one relaxed instance. The
prover sends the univariate cross-term polynomial obtained by evaluating the
transformed constraint on the affine witness line. The verifier checks the
constant coefficient against the relaxed error, samples a fresh fold
challenge, and derives a new relaxed instance by affine combination of public
coordinates and commitments, with the new error given by evaluating the
sent polynomial.

The absence of relaxed-plus-relaxed support is structural: the sent
polynomial has the reduced degree used by the check because one input is
strict. It is not a missing convenience method.

### 3.3 Multi-field circuit and limb discipline

WARPfold selects one right field and a finite collection of prime
wrongfields. A wrongfield witness element also has a base-limb representation
inside the rightfield circuit. The limbs are range checked. One bounded
integer challenge is interpreted in every field; these interpretations are
correlated images of the same public coin, not independent samples.

A strict WARPfold witness satisfies both the rightfield and wrongfield
constraints. A relaxed instance carries one error term per field and a
degradation counter. Its accumulated limb bounds grow with the number of
folds, and wrongfield values are reconstructed from limbs modulo the exact
wrongfield modulus.

The maximum degradation counter is part of the static construction. Once the
bound is reached, another fold is unavailable. The zero relaxed base case and
sequential accumulation topology are exact source requirements.

### 3.4 Weak and reinforced IVC

In the weak construction, all recursive-verifier logic stays in the
rightfield circuit and only the application step uses wrongfield arithmetic.
The paper then explains why this does not obtain the desired recursive
efficiency and why naïvely placing wrongfield constraints in the recursive
circuit is not justified.

The reinforced construction exposes two separately committed witness subsets
under the same commitment key:

- a subset containing accumulated large limbs; and
- a subset whose values are range checked for the next step.

The recursive circuit checks equality between the strict instance's
commitment to the checked subset and the relaxed instance's commitment to the
limb subset. The next witness copies the accumulated limbs into the checked
subset. A program-counter/degradation check ensures that the next fold remains
inside the selected no-overflow range.

The intended extraction argument additionally relies on commitment binding
and noninteractive extraction. Public equality of commitment values is not by
itself equality of their hidden openings.

## 4. Frozen owner mapping

### 4.1 Foundation modules own exact fields and representations

Exact modules can own:

- every prime field, commitment group, and scalar/group operation;
- bounded challenge-integer type and its injections into each field;
- limb-vector types, base decomposition, integer reconstruction, and modular
  reconstruction;
- homogeneous circuit and polynomial carrier types;
- affine witness/instance combination algorithms;
- commitment and hash algorithms; and
- exact failure values for partial representation or range operations.

One bounded public challenge value is sampled once. Pure functions derive its
rightfield and wrongfield images. Sampling separate field challenges would
destroy the source correlation and change the extraction experiment.

The shared model does not need a universal field tower, non-native field, or
limb kind. The exact field collection and limb base are authenticated profile
content.

### 4.2 Core owns one fold's public interaction

One Fresh fold Core contains:

- exact public input occurrences for the strict and relaxed instance views;
- one typed prover Message containing the cross-term polynomial for every
  active field;
- the verifier's constant-term checks;
- one fresh bounded-integer fold challenge;
- pure typed derivation of each field interpretation and the new public
  relaxed-instance coordinates;
- explicit checks for the degradation bound and reinforced commitment
  equality when those variants apply; and
- accept, reject, and sampling/typed-failure terminals.

The output relaxed instance may be exposed as exact public output values and
an accepted-terminal continuation payload. It is not a new event kind.

The committed/hash-derived version is a different Protocol obtained through
an exact transcript construction. The paper's use of the Fiat--Shamir
heuristic cannot collapse the Fresh and noninteractive Protocol identities.

### 4.3 Plan owns honest witnesses and continuation

The Plan computes:

- strict and relaxed witness material;
- each field's cross-term polynomial;
- the folded witness and accumulated limb values;
- reinforced exposed subsets and their commitments; and
- the next recursive-circuit witness.

Recipes read only values available before their source site. An accepted
terminal may provide the next relaxed witness and instance through one direct
same-process continuation arm. Reaching the maximum degradation counter
selects no further fold arm; a decider or flush operation is a distinct
protocol/application route.

Byte serialization of the accumulator does not recreate that causal handoff.
A later process can only decode and freshly admit a new input.

### 4.4 Relations owns circuit, range, commitment, and fold laws

Separate exact Relations definitions can own:

- strict rightfield and wrongfield circuit satisfaction;
- relaxed satisfaction with one error term per field;
- canonical strict limb encoding where the selected profile actually requires
  it;
- bounded accumulated-limb and modular reconstruction predicates;
- commitment-opening correspondence;
- strictness conditions for the source instance;
- cross-term polynomial correctness;
- affine public-instance and private-witness fold relations;
- zero-base-case and degradation-counter recurrence; and
- reinforced equality/copy grounding across exact subset occurrences.

The accumulated-limb relation is not automatically a `ValueEquivalence` or
`ValueEmbedding` between a wrongfield element and a limb vector. Modular
reconstruction can admit multiple limb vectors for one field element unless
the exact bounds and canonicality laws make the representation injective. At
the general WARPfold boundary it is a typed relation with an explicit range
premise.

If a selected strict representation has unique canonical limbs, that narrow
profile may separately admit an embedding. If a projection deliberately
forgets high integer information, it must use the lossy lane and export its
collision/loss premise. Neither case licenses a universal bridge.

Equality of two public commitment values is an ordinary same-type equality.
The proposition that their openings agree belongs to the commitment relation
under a binding assumption. Relations can record the exact equality and
opening equations; Analysis prices or retains the cryptographic assumption.

### 4.5 Incremental-composition Analysis owns the bounded family

The existing family vocabulary can select:

- `Path` topology;
- `ExactFinitePrefix(N_max)` execution depth;
- one statically fixed protocol/Plan/relation member;
- the degradation counter and folded instance as carried public coordinates;
- the exact update verifier; and
- a distinct final decider or flush route.

It must not select a finite-in-degree DAG, all-natural execution depth, or
arbitrary-party continuation merely because the generic vocabulary can
describe them. The WARPfold family supports only its stated sequential and
bounded member.

Exact source-pinned property and theorem profiles are still required for:

- the sequence extraction statement in Theorem 1;
- the weak IVC statement and its heuristic extractor assumptions;
- the reinforced IVC statement and commitment/extractor assumptions;
- the no-overflow invariant at every admitted depth;
- fold preservation in every field;
- final-decider correctness;
- completeness, knowledge soundness, and efficiency as separate goals; and
- any claimed composition with another proof system.

The paper's Conjecture 1 is not a theorem profile and cannot support the naïve
wrongfield-recursive member. It may be represented only as a conjectural
source/proposition with no affirmative judgment.

### 4.6 Crossing proof-system boundaries is not a value bridge

The paper motivates using WARPfold to move between systems or curves, but it
does not specify one universal cross-system protocol. An exact composition
must identify both protocol families, deciders, proof/instance encodings,
relations, setup and commitment assumptions, and the theorem connecting them.

Transported proof or accumulator bytes belong to Realization and fresh
re-admission. Their semantic correspondence may use an exact Interface or
Relations bridge, but causal continuation authority is not portable. The
cross-system theorem belongs to Analysis. The broad application claim is
therefore **undetermined**, not evidence for a new shared bridge primitive.

## 5. Preserved failed and tempting mappings

### 5.1 Model every wrongfield representation as a bijection

**Attempt.** Admit one bidirectional value equivalence between each
wrongfield element and its rightfield limb vector.

**Failure.** Modular reconstruction is many-to-one without exact canonical
bounds, and accumulated relaxed limbs intentionally inhabit a growing range.
The source's no-overflow argument is a theorem premise, not structural type
equality.

**Disposition.** Use exact relation predicates. Admit a narrow embedding only
for a source profile that proves unique canonical representation.

### 5.2 Sample one challenge independently in every field

**Attempt.** Give each field its own FreshChallenge occurrence.

**Failure.** The paper sends the same bounded challenge to every field. The
independent encoding changes correlations and invalidates the stated fold and
extraction argument.

**Disposition.** Sample one bounded integer and apply deterministic typed
field injections.

### 5.3 Treat commitment equality as copied witness equality

**Attempt.** Make the reinforced check `g_check = g_limbs` structurally prove
that the hidden subsets are equal.

**Failure.** Equal commitment values can be opened inconsistently if binding
fails. The paper's extraction argument explicitly branches on a commitment
break.

**Disposition.** Core checks the public equality; Relations records exact
opening/copy correspondence; Analysis retains commitment binding and
extraction hypotheses.

### 5.4 Reuse the generic fold for two relaxed instances

**Attempt.** Instantiate both input slots with relaxed instances.

**Failure.** Protocol 1's degree and coefficient checks use strictness of one
input. The paper expressly does not support relaxed-plus-relaxed folding.

**Disposition.** Formation or relation-profile admission refuses the wrong
source-role assignment.

### 5.5 Claim an unbounded or tree-shaped IVC

**Attempt.** Omit the degradation counter from family identity and infer
arbitrary depth or DAG composition.

**Failure.** Limb bounds accumulate and the construction deliberately removes
tree folding. The next step is unavailable at the selected maximum.

**Disposition.** Exact finite-prefix Path family with explicit counter
recurrence and final-decider/flush boundary.

### 5.6 Treat the paper's extractor discussion as an established theorem

**Attempt.** Attach generic knowledge soundness from the phrase “we extract.”

**Failure.** The sequence extractor differs from a standard folding extractor;
noninteractive variants are assumed, an Algebraic Group Model analysis is not
conducted, and the weak theorem is explicitly heuristic.

**Disposition.** Exact Analysis theorem schemas with every premise retained;
all results remain `NotEvaluated` here.

## 6. Falsification matrix

| Mutation | Required result |
|---|---|
| Replace the one bounded challenge with independent per-field samples | protocol/profile correspondence is negative |
| Change one field injection while retaining the module ID | module authentication or semantic admission refuses |
| Admit a noncanonical limb vector through a claimed equivalence bridge | bridge law check is negative |
| Remove a limb range check | strict/relaxed relation satisfaction or fold premise is negative |
| Let the degradation counter stay constant after a fold | recurrence grounding is negative |
| Continue at or beyond the selected maximum | no continuation arm or explicit bound check rejects |
| Fold two relaxed instances | source-role/degree-law admission refuses |
| Use a tree predecessor set | family topology/member correspondence refuses |
| Omit one wrongfield cross-term polynomial | message/reduction coverage is incomplete |
| Swap cross-term polynomials of equal-degree fields | exact typed field/profile disagreement |
| Let the prover compute a polynomial after seeing the fold challenge | Plan causality is negative |
| Infer hidden-subset equality from equal commitments without binding support | Analysis premise remains unanswered |
| Copy an extensionally equal subset from another run | occurrence grounding is negative |
| Serialize a continuation and reuse its one-use authority elsewhere | causal recurrence refuses |
| Use Conjecture 1 as theorem truth | theorem-source validation refuses |
| Relabel weak IVC as reinforced IVC | protocol/family/theorem identity mismatch |
| Claim all-natural-depth knowledge soundness from Theorem 1 | theorem applicability refuses depth/quantifier mismatch |
| Treat a final-decider test as fold-preservation theorem evidence | evidence kind/applicability mismatch |

## 7. Boundary adjudication

| Pressure | Frozen result | Owner |
|---|---|---|
| Several prime fields and one bounded challenge | exact types and deterministic injections | Foundation + Core |
| Wrongfield limb representation | exact typed relation, optionally narrow embedding | Relations |
| Strict and relaxed instances | separate relation Interfaces | Relations |
| Cross-term publications and challenge | ordinary message/check/challenge schedule | Core |
| Folded public instance | pure public derivation and accepted output | Core |
| Folded witness and exposed subsets | exact causal recipes/exports | Plan |
| Commitment equality versus opening equality | structural check versus conditional proposition | Core + Relations + Analysis |
| Degradation counter and no-overflow limit | carried coordinate and exact Path finite prefix | Relations + Analysis |
| Same-process next-step supply | one-use accepted continuation | Plan |
| Serialized restart | transport plus fresh local admission | Realization |
| Sequence extraction and reinforced IVC | source-pinned conditional theorem schemas | Analysis |
| Broad proof-system warping | under-specified application, no shared primitive | future exact profile |

## 8. Classification and nonclaims

The primary result is **`ProfileOrModule`**. The exact finite interaction and
bounded sequential family fit existing shared semantics. Multi-field algebra,
limb and fold relations, commitment profiles, and theorem schemas are
owner-local additions. No shared profile rotates.

This analysis does **not** establish:

- an executable WARPfold fixture;
- correctness of the paper's construction or proof sketches;
- a standard, polynomial-time, interactive, or noninteractive extractor;
- commitment binding, discrete-log hardness, random-oracle behavior, or
  Fiat--Shamir security;
- relaxed-plus-relaxed, tree, or unbounded folding;
- soundness of the naïve wrongfield recursive circuit;
- final-decider correctness or practical cost;
- compatibility with a named implementation; or
- a generic bridge between arbitrary proof systems.

## 9. Retained work and reopening conditions

Retain for later packages:

1. a source-pinned WARPfold multi-field Relations profile;
2. exact weak and reinforced family identities with distinct theorem schemas;
3. a no-overflow invariant and finite-prefix applicability rule;
4. commitment-binding and noninteractive-extractor assumptions as explicit
   Analysis goals;
5. a negative profile for the unsupported relaxed-plus-relaxed/tree cases;
6. a concrete decider/flush boundary if WARPfold becomes an implementation
   target; and
7. an exact cross-system composition study before using the paper's “warp”
   motivation as a capability claim.

Reopen the shared candidate only if a constructive member demonstrates that:

- one correlated challenge cannot be interpreted in multiple exact modules;
- strict-plus-relaxed source roles cannot be represented without conflation;
- a dynamic degradation counter cannot be grounded in a static finite-prefix
  family;
- exact accumulated-limb correspondence requires a fourth reusable value-
  bridge law rather than a relation predicate; or
- a reinforced same-step subset equality/copy cannot be grounded through the
  existing Core, Plan, Relations, and Analysis seams.

No such obstruction was demonstrated at the assigned depth.
