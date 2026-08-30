# FRI/IOR Variant Pressure Synthesis

> **Kind:** Temporary cross-family primary-source synthesis and architecture
> pressure record
> **State:** Exact classical control completed; the proposed virtual-Oracle
> seam and the remaining cross-family constructive tests stay open
> **Authority:** None. Source claims below report what the cited papers specify.
> Model observations and design inferences are separate and establish neither
> source correspondence nor a cryptographic theorem.
> **Durable destination:** Reviewed oracle-lifecycle requirements belong in
> PIR; exact experiment and theorem requirements belong in Analysis; source
> and local-subject correspondence belongs in Evidence.
> **Deletion:** Delete this page after accepted requirements, rejected options,
> open questions, and source-validation records have durable owners.

## 1. Result in one view

The cross-family evidence does **not** require reopening the central
factorization:

```text
native public-coin oracle interaction
        |
        | checked commitment/opening compilation
        v
committed interactive protocol
        |
        | checked Fiat--Shamir construction
        v
noninteractive protocol
        |
        | theorem application with exact experiments and premises
        v
qualified Analysis result
```

It does expose one narrower missing capability in the protocol model: an
Oracle cannot always mean either a full prover publication or a prover
publication represented by a public binding. DEEP-ALI and STIR independently
require a verifier-defined, non-materialized oracle view whose queries are
translated to queries against already fixed oracles. Encoding that view as a
new prover message changes the source protocol. An exact-used module can
implement the arithmetic of one fixed profile, but it does not by itself give
a nested protocol a reusable typed oracle capability with an explicit query
footprint and dependency law.

The source-supported conclusion is therefore narrower than a completed design:
the model needs a candidate declarative `DerivedOracle`/finite `QueryPlan`
seam, or an equivalent construction with the same visible dependencies and
query footprint. The leading design is to elaborate every finite nonadaptive
plan into explicit guarded Core occurrences before Core authentication. If
query expansion instead happens dynamically during execution, Core execution,
receipts, composition, and authentication must be reopened. Subject to that
choice, this remains a targeted Oracle/composition-boundary extension rather
than a replacement for the central factorization, Relations, commitment
compilation, Fiat--Shamir, or Analysis.

Other pressures are profile or composition work:

- the selected `d0 = 8` Algorithm 1 instance now has a distinct three-fold,
  scalar-terminal finite control; its theorem and family claims remain open;
- batched FRI needs multiple first-layer prover oracles, a batching challenge, a
  prover-fixed combined oracle, and query-level consistency;
- DEEP-FRI needs out-of-domain challenges, an intervening degree-one message,
  prover-published quotient oracles, and an explicit collision law;
- Circle FRI needs layer-indexed domain, projection, pairing, twiddle, fold,
  and full terminal laws rather than one global multiplicative-subgroup fold;
- WHIR needs evolving constrained-code claims, sumcheck subrounds, an OOD
  challenge/reply, shifted grouped fold queries, and recursive claim/weight
  updates; and
- the BCS theorem bridge needs exact source-to-committed correspondence and
  experiment/resource objects, not a wider definition of Protocol.

No protocol family reviewed here supplies evidence for a universal transition
algebra, an opaque “FRI effect,” or a single theorem named “FRI security.”

## 2. Method and classification discipline

Every substantive paragraph is one of:

- **Source claim:** a protocol step, definition, or theorem boundary stated in
  a primary source at the named locator;
- **Current-model observation:** a fact about the durable PIR documents, the
  provisional native-FRI design, or the finite executable profile;
- **Inference:** an architecture conclusion drawn from those two inputs.

The disposition vocabulary is:

| Disposition | Meaning |
|---|---|
| `Representable now` | The current finite/provisional model has the required semantic shape at the stated narrow scope. This does not establish source correspondence. |
| `Additive extension` | A new profile, schedule, composition, relation, or theorem object is needed, while existing semantic meanings can remain unchanged. |
| `Targeted redesign` | One existing local boundary lacks the right kind of object and must be extended or split. The central factorization can remain. |
| `Architecture reopen` | A central ownership or factorization decision must change. No reviewed family presently reaches this disposition. |

“Representable” is about semantic vocabulary, not proof. A paper theorem also
requires exact protocol correspondence, experiment equality or a proved
transport, every stated premise, source validation, and a truth discharge.

## 3. Primary-source snapshot

The following exact local bytes were inspected. Their hashes identify this
review snapshot only. They do not authenticate origin, prove correct reading,
or amend the executable package's source ledger.

| Source | Exact locators used | Primary link | Local SHA-256 |
|---|---|---|---|
| Ben-Sasson, Bentov, Horesh, Riabzev, *Fast Reed--Solomon Interactive Oracle Proofs of Proximity*, ECCC revision 2 | Definition 1.1; Sections 3.2--3.3; Remark 3.1; Theorem 3.3 and Main Theorem | [ECCC TR17-134 revision 2](https://eccc.weizmann.ac.il/report/2017/134/revision/2) | `f9868a06d50c727b349516d54915aa2a9bf8d966d8b04597bce054db73c1294d` |
| Ben-Sasson, Chiesa, Spooner, *Interactive Oracle Proofs*, ePrint revision 2 | Sections 3.1--3.2, 5.4, and 6; Theorem 7.1 | [ePrint 2016/116](https://eprint.iacr.org/2016/116.pdf) | `a2dc9bd042665081664287281b9bcf64735be2c818ce9207cce57cc43939fa2f` |
| Block, Garreta, Katz, Thaler, Tiwari, Zajac, *Fiat-Shamir Security of FRI and Related SNARKs*, archive revision 7 | Theorems 4.1--4.2; Corollaries 4.3--4.4; Sections 2.2.2, 5.2, 5.2.2, 5.5, and 5.7; Definition 6.2; Section 7.2; Theorem 5.11 | [ePrint 2023/1071](https://eprint.iacr.org/2023/1071.pdf) | `bb7a7e87b9000c98106de99c9af9d289def2a1b91919a3507ee78bf9bfd16947` |
| Ben-Sasson, Goldberg, Kopparty, Saraf, *DEEP-FRI: Sampling Outside the Box Improves Soundness*, author manuscript v1 | Section 5.2.1 and Lemma 5.3; Protocols 5.4 and 6.4; Theorem 6.2 | [arXiv:1903.12243v1](https://arxiv.org/pdf/1903.12243v1) | `e0f1d73000bb740729d8d5af4b610276befa836928787d1005ef7723348615f9` |
| Arnon, Chiesa, Fenzi, Yogev, *STIR: Reed--Solomon Proximity Testing with Fewer Queries* | Definition 4.2; Construction 5.2; Remark 5.3; Lemma 5.4 | [ePrint 2024/390](https://eprint.iacr.org/2024/390.pdf) | `766a5d955c5db75cdbfea2fdbf8939ec5c9dfe12df0ed054d6ec6f604e0615d2` |
| Haböck, Levit, Papini, *Circle STARKs* | Section 6; Protocols 1--2; Appendix B, Theorem 6 | [ePrint 2024/278](https://eprint.iacr.org/2024/278.pdf) | `8e60498a671ff147c211ac7733435057dff27b31b8bd3211485b85b4035d296d` |
| Arnon, Chiesa, Fenzi, Yogev, *WHIR: Reed--Solomon Proximity Testing with Super-Fast Verification* | Definition 4.5; Construction 5.1; Theorem 5.2 | [ePrint 2024/1586](https://eprint.iacr.org/2024/1586.pdf) | `ccacc62cf5529ff95c3cf115cf730b020336f8d95c310c8deb64e3beac30ce61` |

The DEEP source inspected here is the March 2019 author manuscript. The
published ITCS version is also a primary source, but this note does not claim
byte identity or locator identity between the two versions.

The ePrint PDF links above are mutable publication endpoints. The hashes pin
the inspected local bytes, but exact archive revision/date metadata remains a
reproducibility obligation for every row not already carrying it.

## 4. Current model baseline

### 4.1 Durable protocol vocabulary

**Current-model observation.** The durable Oracle declaration currently has
two publication modes, `FullCanonicalOracle` and `PublicBinding`. In both
cases, the carrier is strategy-supplied at its unique `PublishOracle`
occurrence, and publication is a prover decision. The model has typed
`QueryOracle` and `AnswerOracle` effects, exact scopes, immutable carriers,
ordered occurrences, and a generic exact-used `ModuleEffectRef` boundary.

**Current-model observation.** Durable composition already has explicit child
Cores, typed face maps, occurrence/value/object/check maps, causal seams,
interleaving, shared or derived challenges, failure policy, and terminal
combination. It deliberately produces and readmits one finite target Core.

**Inference.** Composition has much of the structural surface needed for
nested proximity tests and sumcheck/proximity interleaving, but current typed
face maps carry values rather than an oracle capability with a query
elaboration. The missing work is therefore local to the Oracle/composition
boundary only if a derived capability can be elaborated into the existing
finite target occurrence model before authentication. That compatibility is a
test obligation, not a result already established here.

### 4.2 Provisional native-FRI factorization

**Current-model observation.** The provisional design separates:

1. native logical-oracle FRI;
2. checked commitment/opening compilation into a different Core;
3. optional checked work augmentation into another Core; and
4. Fresh and Fiat--Shamir challenge interpretations over the same final Core.

It proposes `LogicalAccess` and distinguishes invocation-supplied initial
oracles from strategy-supplied prover oracles. Those proposals are not yet the
durable Oracle definition.

**Inference.** The reviewed families strengthen the reason for that split.
They do not justify collapsing logical access, cryptographic commitment, and
Fiat--Shamir into one oracle mode.

### 4.3 Executable finite profile

**Current-model observation.** The executable profile has one order-16
multiplicative-domain input oracle, two binary folds, a degree-less-than-two
terminal polynomial, and four ordered query occurrences. It exercises native
logical queries, a concrete commitment/opening compilation, public-only target
verification, optional grinding, and one Fiat--Shamir transcript profile.

**Current-model observation.** The earlier executable profile remains an
implementation-style two-fold early-terminated control. A separate exact
classical control now performs the source's three folds, sends a scalar after
the third fold, and executes four labelled draws with twelve layer checks.

**Inference.** The combined result retains the selected factorization and
closes exact classical correspondence only for the fixed-coin deterministic
verifier shape. No batched, DEEP, STIR, Circle, WHIR, BCS, or theorem
correspondence follows from it.

## 5. Cross-family disposition matrix

| Family | Source-required pressure | Current narrow support | Required disposition |
|---|---|---|---|
| Exact classical FRI | Initial logical Oracle, round-indexed fold challenges and Oracles, scalar terminal, late labelled query repetitions, complete fibres | Separate three-fold/scalar-terminal control with fixed-coin deterministic schedule correspondence, checked structural commitment construction, and public Fresh/Fiat--Shamir replay | Retained `ConservativeExtension`; randomized Protocol, theorem, BCS, and property correspondence remain open |
| Batched FRI | Several first-layer prover oracles, independent coefficient vector, prover-fixed combined oracle, query consistency, theorem-distinct powers variant | Generic messages/challenges/checks and composition can carry the shape; no constructive encoding exists | `Additive extension` |
| DEEP-FRI | `z -> B_z(X) -> x -> quotient oracle`, out-of-domain/collision law, quotient check | Generic messages, challenges, prover oracles, and checks can carry the shape | `Additive extension` |
| DEEP-ALI | Two verifier-defined quotient views consumed by two proximity tests, with a still-unreconstructed multipoint value/failure law | No non-materialized derived Oracle exists; a fixed exact-used module does not provide a reusable child capability | Candidate `Targeted redesign` at the Oracle/composition boundary, plus additive composition; exact disposition depends on static elaboration |
| STIR | Partial `Fill` oracle, virtual quotient and degree correction, index-dependent routing, sampled-point collision semantics, changing domains/rates | Prover messages and challenges are generic; virtual query routing is absent | Same candidate `Targeted redesign`, plus additive profiles and schedules; exact disposition depends on static elaboration |
| Circle FRI | Circle-code domain, layer-specific pairing/projections and twiddles, decomposition scalar, and a full clear terminal object | The finite algebra profile demonstrates profile-owned fold laws, but only for one multiplicative chain | `Additive extension` of algebra/domain and terminal profiles |
| WHIR | Constrained-code claim, sumcheck subrounds, OOD challenge/reply, shifted grouped fold reads, recursively updated weights/target | Generic claims, messages, challenges, and composition are plausible; no constructive encoding exists | `Additive extension`; a grouped static elaboration may reuse the candidate query-plan concept |
| BCS theorem bridge | Exact public-coin source, one commitment root per prover oracle, statement-seeded RO chain, late queries and paths, restricted-restoration premise | The factorization has the right source/target separation; local commitment and hash profiles are not literal BCS | `Additive extension` in construction, Relations, Evidence, and Analysis |

No source presently forces a row to `Architecture reopen`. That conclusion is
conditional: a finite nonadaptive derived-query plan must elaborate into the
authenticated static occurrence and face-map model. A runtime plan that emits
new occurrences during execution would itself reopen Core execution, receipts,
composition, and authentication. Section 14 states the tests that decide
between those outcomes.

## 6. Classical and batched FRI

### 6.1 Exact classical FRI

**Source claim.** ECCC revision 2 Definition 1.1 defines an IOP of proximity
where the verifier has oracle access to the input word. In Sections 3.2--3.3,
FRI alternates verifier localization challenges with prover oracle messages,
then sends a bounded terminal polynomial representation before sampling query
locations. Each query follows the domain-reduction path and reads the complete
fibre needed to check the corresponding fold. Remark 3.1 describes the smooth
multiplicative adaptation; the main protocol is more general than the local
binary `x -> x^2` specialization.

**Source claim.** Theorem 3.3 is stated first for the paper's fibre/block
distance, and the Main Theorem performs the additional step to ordinary
relative Hamming distance. The metric and that conversion are theorem data;
they are not interchangeable labels on one generic proximity claim.

**Source claim.** Section 5.7 Algorithm 1 of ePrint 2023/1071 fixes a smooth
multiplicative binary profile with `d0 = 2^k`. It runs exactly `k` folding
rounds, sends `G_k = C` as a scalar, and then performs `ell` query occurrences.
For each occurrence and layer, the verifier reads both points in the binary
fibre, interpolates the degree-one polynomial, and checks the next-layer value.

**Source claim.** Theorems 4.1 and 5.11 and Corollary 4.3 apply to that exact
algorithm and their stated field, rate, distance, strategy, query, and
random-oracle premises. They do not state a theorem for an arbitrary
early-terminated FRI profile.

**Current-model observation.** The new control preserves Oracle fixation,
fold-challenge order, immutable prior layers, scalar-before-query order,
complete binary fibres, ordered query multiplicity, and separate native versus
committed verifier views for the complete three-fold schedule. The earlier
two-fold subject remains separately identified.

**Inference.** Exact Algorithm 1 is an additive profile, not a reason to alter
the factorization. The new three-fold/scalar-terminal subject has its own Core
identity and checked deterministic schedule correspondence. The existing
early-stop subject remains a noncorresponding implementation-style profile
rather than being silently renamed. Randomized experiment and theorem
correspondence still require Analysis-owned premises.

### 6.2 Batched FRI

**Source claim.** Sections 2.2.2 and 5.2 of ePrint 2023/1071 specify:

1. the prover supplies oracle access to `t` initial functions;
2. the verifier samples an independent coefficient vector
   `(alpha_1, ..., alpha_t)`; and
3. the parties run Algorithm 1 on
   `G_0 = sum_i alpha_i f_i^(0)`.

The protocol adds a batching round, and its query phase checks consistency
between the source functions and the combined function. Theorem 4.2 and
Corollary 4.4 are batched-protocol results, not automatic consequences of the
single-oracle theorem.

**Source claim.** Section 5.2.2's communication-saving variant samples one
`alpha` and uses its powers. Lemma 5.10 records a factor proportional to the
batch size in the stated error. Independent coefficients and powers of one
coefficient are therefore different challenge and theorem profiles.

**Current-model observation.** Multiple prover oracles fixed before a vector
challenge, a later combined prover oracle, consistency checks, and a nested FRI
child can be represented by the provisional origin split and existing
composition vocabulary. No current finite witness constructs them.

**Inference.** The combined `G_0` must remain a prover-fixed oracle in the
exact batched interaction. Replacing it by a deterministic verifier-derived
view would remove a malicious prover choice and change the protocol/game. A
derived linear-combination view can be useful inside a verifier check, but it
must not erase the actual `G_0` publication or its consistency obligation.

**Disposition:** additive construction and exact batched correspondence. No
central or Oracle redesign is required beyond the already needed
logical-access and origin distinctions.

### 6.3 Open related-protocol pressure cases

**Source claim.** Section 5.5 of ePrint 2023/1071 describes a Toy Problem
Protocol in which the prover first supplies oracle access to `f`, the verifier
samples `alpha`, and FRI is then invoked on the verifier-randomized function
`g(x) = (f(x) - alpha) / x`. The paper also gives the corresponding batched
shape `g_i(x) = (f_i(x) - alpha_i) / x`. Conjectures 5.13--5.14, rather than a
proved FRI theorem, own the security comparison made there.

**Source claim.** Definition 6.2 compiles a delta-correlated hIOP by passing
the verifier-constructed list of words `W` to a correlated-agreement IOPP.
Section 7.2 instantiates that pattern for the OPlonky/Plonky2-related protocol.
This is a stronger composition pressure than standalone batched FRI because a
child proximity protocol consumes verifier-constructed quotient words.

**Inference.** Both cases should be added to the constructive queue after the
DEEP-ALI/STIR seam tests. They independently pressure a typed derived
capability and its face-map/elaboration boundary, but the conjectural Toy
Problem results must remain Analysis-owned and the general compiler requires
its own exact correspondence.

**Carried-forward coverage gap.** The earlier Analysis dossier retains
BaseFold as a separate pressure case for shared challenges across multilinear
claim, sumcheck, and fold state. Its primary paper was not part of this
snapshot, so this synthesis makes no new BaseFold source claim or disposition.
It must be source-revalidated before being used as architecture evidence.

## 7. DEEP-FRI and DEEP-ALI

### 7.1 DEEP-FRI

**Source claim.** Section 5.2.1 defines
`QUOTIENT(f,z,b)(y) = (f(y)-b)/(y-z)`. Lemma 5.3 assumes `z` is outside the
evaluation set. Protocol 5.4 then orders each round as:

```text
verifier samples z_i
    -> prover sends degree-one B_{z_i}(X)
    -> verifier samples fold challenge x_i
    -> prover sends quotient oracle f_{i+1}
```

The query phase reads a source fibre, evaluates its localization polynomial,
and checks the exact quotient equation before comparing the final layer with a
scalar `C`.

**Source claim with textual tension.** Protocol 5.4 writes `z_i` as uniform in
the whole field, while Lemma 5.3 requires `z_i` outside the relevant domain and
the surrounding motivation says “outside the box.” This note does not resolve
that difference by interpretation.

**Current-model observation.** Degree-one messages, two ordered challenges,
prover-published quotient oracles, exact checks, and a scalar terminal all fit
the generic Core shape. A quotient oracle in DEEP-FRI is a prover publication;
it is not the verifier-derived view proposed below.

**Inference.** An exact profile must choose and identify one collision law:
sampling directly from the complement, rejection sampling, explicit abort on
collision, or the paper's literal whole-field step plus an independently
justified total semantics. The choice affects challenge distribution,
failure, transcript, and theorem applicability. It cannot be buried in a
division routine.

**Disposition:** additive algebra/schedule/profile work. No architecture
reopen is justified.

### 7.2 DEEP-ALI

**Source claim.** Protocol 6.4 has the prover send `f : D -> F`, receives a
coefficient vector `alpha`, sends `g_alpha : D' -> F`, receives a random `z`,
and sends the values of `f` on the mask set `M_z`. The verifier derives the
alleged `g_alpha(z)` value and then defines two quotient functions `h_1` and
`h_2`. The paper explicitly says that the verifier has oracle access to those
functions using the earlier `f` and `g_alpha` oracles. Two RPT invocations test
the derived functions over different domains and degree bounds.

**Source limitation.** Section 5.2.1 defines the single-point quotient under
the condition that the sampled point lies outside the evaluation set.
Protocol 6.4 uses a multipoint quotient notation and denominators `Q_i(z)`,
but the inspected text does not by itself provide a total executable law for
`Q_i(z) = 0`, collisions between the mask and queried domains, or a collapsed
mask. The proof's probability accounting for bad points is not an execution
failure rule.

**Current-model observation.** Existing composition can in principle host two
proximity-test children and shared earlier challenges. Durable Oracle semantics
cannot currently give a child a non-materialized oracle view. An exact-used
module can expose fixed arithmetic inputs and outputs, but current typed face
maps do not pass a reusable oracle capability or its query elaboration.

**Inference.** Materializing `h_1` and `h_2` as new prover messages changes the
interaction and gives those values independent strategy authority. A fixed
module implementation can compute one selected case, but it does not provide
the generic child-oracle interface or occurrence correspondence needed by
commitment compilation and resource analysis. Exact DEEP-ALI correspondence
also remains blocked until its multipoint value and collision laws are
reconstructed and tested.

**Disposition:** candidate targeted Oracle/composition-boundary redesign plus
additive nested composition and relation transport. Static pre-authentication
elaboration is the leading design; this page does not yet establish that it
fits the existing face-map model.

## 8. STIR

**Source claim.** Definition 4.2 gives a total quotient function over an
evaluation domain by using a supplied `Fill` value at denominator-zero
locations. Construction 5.2 then repeats the following shape:

1. the prover sends folded oracle `g_i`;
2. the verifier sends out-of-domain samples;
3. the prover replies with their evaluations;
4. the verifier sends the next fold challenge, a combination challenge, and
   shift points;
5. the prover sends a partial `Fill_i` oracle for shift points that collide
   with the next evaluation domain; and
6. the verifier virtually defines a quotient `g_i'` and degree-corrected
   oracle `f_i`.

Construction 5.2 states that a query to `f_i` translates to one query to
`g_i` when the index is outside the special set and one query to `Fill_i` when
it is inside. A later folded query expands to the appropriate fibre of that
virtual `f_i`. Remark 5.3 removes the `Fill` path only under an explicit
domain-disjointness condition.

**Source limitation.** Definition 4.2 is total only when its supplied
`Ans : S -> F` is a well-defined function. Construction 5.2 forms `S` from
out-of-domain and shifted sample sets and assigns answers by two rules, but the
inspected text does not state cross-family distinctness or a precedence rule.
If the same point occurs in both families with unequal supplied values, exact
execution needs conditioned sampling, an equality check and rejection, or an
explicit collision rule.

**Source claim.** Lemma 5.4 is a round-by-round statement over the exact
iteration, rate, distance, list-decoding, and Section 4.1 `B*`/`err*`
premises. It does not turn ordinary FRI's theorem into a STIR theorem by
profile renaming. Conjecture-dependent parameter profiles must remain
separate from proved-premise profiles.

**Current-model observation.** Prover oracle messages, scalar replies,
challenges, checks, and changing per-layer profiles can be added. The missing
piece is the virtual `f_i` capability and its visible branch-dependent query
footprint.

**Inference.** STIR independently demands the same concept as DEEP-ALI but
with stronger routing pressure: the source oracle selected by a derived query
depends on the requested index and public set membership. It also demonstrates
why the seam must preserve labelled logical multiplicity and causal order and
expose flattened base-query cost.

**Disposition:** the same candidate `DerivedOracle`/`QueryPlan` redesign, plus
additive layer schedules and theorem profiles. A universal STIR-specific Core
effect is unnecessary. The collision case and static elaboration must be
closed before exact correspondence is claimed.

## 9. Circle FRI

**Source claim.** Section 6 of *Circle STARKs* adapts FRI to circle-code
function spaces and a chain of two-to-one projections. Before folding, the
prover decomposes `f = g + lambda v_n` and sends `lambda`. The first projection
is quotient by the circle involution `J` onto the x-axis; later projections use
`pi(x) = 2x^2 - 1`. Correspondingly, the first even/odd decomposition uses the
`y` coordinate as twiddle and later rounds use `x`.

**Source claim.** In Protocol 1, nonterminal folds are prover-published oracle
layers, while the final folded function/polynomial is sent in the clear and is
checked in full against the terminal code. Query checks follow the projection
trace using a layer-specific pairing map `T_j`: the first layer uses the circle
involution `J`, while later layers use negation. Protocol 2 first combines a
batch with powers of one random coefficient and extends the query phase with
the batching equation. Appendix B, Theorem 6 is a batch Circle-FRI soundness
statement with its own correlated-agreement and parameter premises.

**Current-model observation.** The finite profile already places domain chain,
fold evaluator, query projection, and terminal evaluator in an algebra profile
rather than in the generic Core. Its concrete laws are nevertheless fixed to
one multiplicative subgroup and binary square-map chain.

**Inference.** `multiplicative subgroup`, `x -> x^2`, one global pairing map,
and a single twiddle rule cannot become global Oracle or Core invariants.
Circle FRI is representable by a separate algebra profile whose layer
descriptors carry domain type, pairing, projection, fibre enumerator, twiddle
selector, fold law, function-space bound, and whose terminal profile carries
the complete clear-object validation law.

**Disposition:** additive algebra/domain profile and constructive encoding.
The source gives no reason to change message ownership, Core composition, or
the commitment/Fiat--Shamir factorization.

## 10. WHIR

**Source claim.** Definition 4.5 defines a constrained Reed--Solomon code by a
field, smooth evaluation domain, variable count, weight polynomial, and target
sum. Construction 5.1 begins with such a claim, performs `k_i` sumcheck rounds,
sends a folded oracle for the next domain, obtains an out-of-domain evaluation,
samples shifted-query points and a combination challenge, and recursively
updates the weight polynomial. It ends with a clear multilinear polynomial
and checks both fold agreement and the final constrained claim.

**Source claim.** In the decision phase, the verifier defines
`g_{i-1} = Fold(f_{i-1}, alpha_{i-1})` and computes requested values by querying
the appropriate `2^{k_{i-1}}` source locations. The out-of-domain step is a
verifier challenge followed by a prover scalar reply, not an oracle query.
Theorem 5.2 gives a round-by-round result under separate exact
mutual-correlated-agreement, list-decoding, distance, and parameter hypotheses.
The JB/CB instantiations rely specifically on Conjecture 4.12 for mutual
correlated agreement of the powers generator; conjecture-dependent profiles
must remain distinct from proved-premise profiles.

**Current-model observation.** Claims, reductions, polynomial messages,
challenge groups, child interleaving, changing profiles, and a final clear
polynomial can be added through existing generic objects and composition. No
current witness demonstrates that complete encoding. A grouped fold read is a
one-level deterministic expansion from the published preceding oracle and may
benefit from the same finite static-elaboration concept as STIR. WHIR does not
by itself require recursively nested persistent derived-oracle layers.

**Inference.** The central pressure is evolving claim state, not a new notion
of Protocol. Each iteration must carry an exact constrained-code claim
`(domain, variables, weight, target)`, and each sumcheck/fold step must map it
to the next claim. Structural composition can record that map; Analysis must
separately own mutual-correlated-agreement and round-by-round conclusions.

**Disposition:** additive claim/reduction profiles, finite composition, and
theorem objects. Test grouped static query elaboration for visible fold
expansion; reopen composition only if a constructive encoding cannot express
the exact claim transport without an unmodeled effect.

## 11. The BCS theorem bridge

**Source claim.** Section 6 of *Interactive Oracle Proofs* transforms a
public-coin IOP by splitting the random oracle into verifier-coin and
Merkle/hash purposes. It initializes `sigma_0` from the statement, derives each
verifier message from the statement and previous chain state, commits each
prover oracle message by a Merkle root, updates the chain with that root, and
derives final query randomness only after the last root. The proof contains
the roots, one authentication path for each logical IOP query, and the final
chain value.

**Source claim.** Section 5.4 defines restricted state restoration; after the
first iteration the attacker cannot restore the empty verifier state. Theorem
7.1 bounds target soundness by the source restricted-restoration quantity plus
`3(m^2+1)2^-lambda`, and gives analogous knowledge and zero-knowledge
statements under their separate premises. Sections 3.1--3.2 supply specific
Merkle extractability and privacy requirements.

**Current-model observation.** The selected factorization correctly gives the
native logical-oracle Core and committed Core different identities, then gives
Fresh and Fiat--Shamir forms of the committed Core one Core identity. The
finite commitment profile uses typed field leaves, pair grouping, a two-node
cap, salts, deduplicated opening material, and SHA-256 framing. Those are not
the literal bit-string Merkle/RO construction of Section 6.

**Inference.** BCS is not permission to identify native and committed Cores.
It is a theorem bridge over an exact checked compilation and exact source and
target experiments. For FRI, the bridge must also resolve the source's special
initial-oracle convention: whether it is an outer indexed input, a first IOP
prover oracle, or a separately committed statement component changes the
round map and restricted-restoration game. Adding salts or a hash label alone
does not establish the source's extractability or privacy requirements; that
is a design inference from the mismatch, not a statement made by BCS.

**Disposition:** additive construction correspondence, occurrence/resource
maps, source validation, theorem schema, and applicability checking. Reopen
the architecture only if exact correspondence proves that the chosen initial-
oracle fork cannot inhabit the BCS source experiment.

## 12. Candidate `DerivedOracle` / `QueryPlan` seam

### 12.1 Why the seam is evidence-supported

The candidate is worth testing because two independent protocols need the
same missing semantic capability:

| Requirement | DEEP-ALI Protocol 6.4 | STIR Construction 5.2 |
|---|---|---|
| No new prover authority | `h_1` and `h_2` are defined by the verifier from prior oracles and public values | `g_i'` and `f_i` are virtually defined by the verifier from `g_i`, `Fill_i`, and public challenges/answers |
| Query translation | One derived read reduces to a read of `f` or `g_alpha` plus deterministic quotient arithmetic | One `f_i(x)` read chooses `g_i(x)` or `Fill_i(x)` from public membership, then applies quotient and degree correction |
| Downstream consumer | Two nested RPT invocations | Later folds and the final consistency test |
| Resource visibility | RPT query count must induce source-oracle reads | The paper explicitly accounts for mapped source queries and grouped fibres |

This common shape is narrower than an arbitrary computed oracle and broader
than either protocol's quotient formula. It supports the need for a seam, not
the correctness or minimality of the particular representation below.

### 12.2 Candidate semantic shape

The following is design notation, not durable syntax. It describes an
authoring/construction object that should first be tested by elaborating it
away before Core authentication:

```text
DerivedOracleDecl = {
  scope,
  index_type,
  element_type,
  dependencies: ordered prior values, challenges, and oracle capabilities,
  query_plan: QueryPlanRef,
  value_law: PureFunctionContractRef,
  source_failure_law: SemanticFailureContractRef,
  maximum_leaf_expansion_per_query,
  maximum_elaboration_depth
}

ElaborateDerivedUse(
  declaration,
  logical_query_occurrence,
  symbolic_requested_index,
  public_dependencies)
  -> bounded guarded sequence of ordinary Core effects

ordinary effects include:
  source-index computation
  QueryOracle / AnswerOracle occurrences
  value-law evaluation
  one consumer-visible derived answer value

EvaluateDerivedValue(
  requested_index,
  public_dependencies,
  ordered_source_answers)
  -> DerivedValue | DeclaredSemanticFailure
```

The elaborator must emit the complete finite occurrence shape, including both
branches of public-data-dependent routing under explicit guards, before the
target Core is authenticated. Runtime values may select guards and determine
typed query indices, but they do not create occurrences. The authenticated
target Core and a checked occurrence/value map then own semantic identity; it
remains open whether the authoring declaration also needs a separately sealed
construction identity.

Neither cited protocol contains an `ActivateDerivedOracle` interaction event.
Availability should therefore follow from dependency closure unless a future
constructive test proves that an explicit local verifier effect is necessary.
If such an effect is introduced, its outputs, observation class, replay law,
Fiat--Shamir treatment, and identity contribution must be specified; it must
not be presented as a source event.

### 12.3 Required admission laws

A candidate can be promoted only if all of the following are checked:

1. **Causal closure:** every dependency is in scope and strictly earlier than
   the logical use; no future message, challenge, answer, or terminal is read.
2. **Well-founded elaboration:** dependencies between derived declarations form
   a DAG and are fully expanded before target-Core authentication. Recursive or
   cyclic expansion is rejected.
3. **Finite structural planning:** every admitted logical use expands to a
   bounded finite set of guarded ordinary occurrences. Runtime values may
   select an authenticated guard but cannot allocate a new occurrence or
   invoke a host callback.
4. **Type and domain closure:** every source query index has the exact source
   Oracle index type and lies under its declared query contract.
5. **Response closure:** the value law consumes exactly the ordered answers
   selected by the guarded plan and returns the declared element type or an
   exactly classified semantic branch.
6. **Visibility preservation:** a derived query cannot reveal a verifier-only
   source index or answer through a public result without an explicit
   declassification rule.
7. **Multiplicity preservation:** repeated logical source queries remain
   repeated occurrences. Later commitment compilation may share physical
   openings only through a separate occurrence-to-opening map.
8. **Resource ownership:** per-query leaf expansion and semantic traversal
   bounds belong to the plan. Total logical-use count belongs to the consumer's
   static schedule. Independent evaluator work limits remain execution policy
   and cannot rotate semantic identity merely by changing a budget.
9. **Failure classification:** source-declared algebraic/collision branches,
   absent finite-oracle entries, authenticated retry exhaustion, independent
   evaluator-limit exhaustion, Fresh noncompletion, and Fiat--Shamir sampling
   failure remain distinct. In particular, evaluator-limit exhaustion is
   noncompletion rather than a protocol rejection, and interpretation failure
   is not silently converted into a Core terminal.
10. **Canonical identity:** the authenticated target Core includes every
    elaborated effect, guard, dependency, and semantic bound. If the authoring
    declaration is separately sealed, its domain and query/value/source-failure
    law IDs enter that construction identity. Expository names, citations, and
    evaluator budgets do not.

The initial candidate should permit only **nonadaptive** plans: the guarded
source-query structure depends on the requested index and already available
public dependencies, not on source answers. DEEP-ALI and STIR appear to fit
that boundary, subject to their unresolved collision laws. Answer-dependent
routing should require new evidence and a separate review.

### 12.4 Execution and observation

The leading execution model is static elaboration:

```text
authoring declaration plus logical use
    -> recursively elaborate a finite guarded occurrence template
    -> authenticate the complete target Core
    -> execute only authenticated occurrences selected by their guards
    -> compute the consumer-visible answer from recorded source answers
```

A checked elaboration map must retain both levels: the logical derived query
seen by its consumer and the exact target source-query occurrences. Omitting
the first loses protocol-level query meaning; omitting the second loses
resource, commitment, and causality meaning. The runtime does not emit a new
subschedule.

If a future design instead evaluates `QueryPlan` at runtime and emits leaf
`QueryOracle`/`AnswerOracle` occurrences dynamically, that is not compatible
with the current fixed occurrence list and occurrence-keyed receipts. It would
reopen Core execution, receipts, composition, and authentication rather than
remain a local Oracle-ABI addition.

No new prover carrier is snapshotted for a derived view. Its consumer-visible
value is computed from immutable earlier carriers/answers and public
dependencies by authenticated ordinary effects. Equal outputs do not by
themselves establish correspondence between two declarations or elaborations.

### 12.5 Commitment and Fiat--Shamir interaction

Commitment compilation authenticates the actual prover or invocation oracles
that a flattened plan reads. It does not invent a root for a virtual oracle.
A construction that materializes and commits a derived view is a different
target protocol and needs a checked correspondence.

Likewise, declaring or elaborating a deterministic virtual view invents no
transcript message. Fiat--Shamir absorbs the source protocol's actual public
statement, prover messages/publications, and declared public observations.
Any public observation produced by an elaborated effect must map to a real
source observation; the declaration's mere existence is not one.

### 12.6 Composition and Relations

Current typed face maps carry value references; they do not yet carry a
derived-oracle capability or an object-to-many occurrence elaboration. The
leading candidate is therefore to elaborate a child's logical derived use
into a finite target occurrence sequence before the composed target Core is
authenticated, with a checked map preserving:

- dependency availability before the child's first logical use;
- every shared challenge and public dependency;
- the child's logical query/value occurrence;
- every guarded target source-query occurrence; and
- all semantic failure and terminal paths.

If that cannot be expressed without extending face maps, a separately typed
capability/object map is the next additive design. Claiming that current face
maps already carry the capability would be premature.

Relations should be able to state both `derived answer = value law(source
answers)` and occurrence correspondence between one logical derived query and
its labelled, causally ordered target-query occurrences. A relation fact does
not create the derived capability and cannot replace Protocol execution.

### 12.7 Boundaries that must not be crossed

The new seam must not be used for:

- batched FRI's prover-fixed `G_0` oracle;
- DEEP-FRI's prover-published quotient oracle;
- a commitment root or authenticated opening table;
- an arbitrary effectful verifier callback;
- a theorem assertion or proximity claim;
- hiding an unbounded or response-adaptive algorithm; or
- emitting unauthenticated runtime occurrences under the current static Core.

Those negative boundaries prevent “derived” from becoming another opaque
universal escape hatch.

## 13. Cross-family invariants and profile-local choices

The review supports the following **cross-family invariants**:

- every prover-controlled oracle is fixed before a dependent challenge;
- initial, prover-published, and verifier-derived oracles have different
  authority and must not be inferred from equal values;
- terminal material is fixed before query randomness;
- logical query occurrences preserve source labels, multiplicity, and causal
  partial order; a canonical total order is a target-model choice unless the
  source specifies one;
- a virtual query has an explicit, finite underlying query footprint;
- source semantic failure, protocol rejection, absent lookup, authenticated
  retry exhaustion, evaluator-limit noncompletion, Fresh noncompletion, and
  Fiat--Shamir interpretation failure are not collapsed into one outcome;
- commitment/opening is a construction over native access, not native access
  itself;
- Fiat--Shamir is a challenge interpretation/transform with an exact
  transcript, not a native IOP property; and
- theorem conclusions remain Analysis-owned and bind exact experiments,
  profiles, resources, and premises.

The following are **profile-local choices** and must not become Core
invariants:

- additive versus multiplicative versus circle domains;
- `x -> x^2` versus circle projection chains;
- binary versus higher-arity folds;
- scalar versus coefficient-vector terminal;
- early termination;
- independent batching coefficients versus powers of one coefficient;
- quotient collision policy and `Fill` behavior;
- field/base-extension choice;
- leaf grouping, tree arity, cap shape, salting, and multiproof format; and
- concrete hash, framing, sampler, and Fiat--Shamir query expansion.

## 14. Constructive validation and reversal conditions

The exact classical control is complete at its deterministic structural scope.
The remaining validation order should maximize information before expanding
the durable vocabulary:

1. **Batched control:** add two initial Oracles, independent coefficient
   vector, actual `G_0` publication, and query consistency. Mutate `G_0`
   independently to prove that it remains a prover choice.
2. **DEEP-FRI control:** encode one round with `z`, degree-one `B_z`, later
   fold challenge, quotient oracle, and each candidate collision disposition.
3. **DEEP-ALI seam test:** reconstruct a total multipoint quotient/failure law,
   define `h_1` and `h_2`, statically elaborate one query of each to its
   underlying oracle, and invoke two finite proximity-test children.
4. **STIR seam test:** exercise both query-plan branches, including an index
   that requires `Fill`, test an OOD/shift collision, then statically elaborate
   a later fibre query through the derived oracle.
5. **Circle profile test:** represent the first `J/y` fold and one later
   `pi/x` fold, their different pairing maps, and the full clear terminal check
   in the same Core without a special-case Core constructor.
6. **WHIR composition test:** carry one constrained-code claim through a
   sumcheck block, folded-oracle publication, OOD reply, shifted query block,
   and updated `(weight,target)` claim.
7. **BCS bridge test:** map the exact classical source to one literal BCS
   target first; compare the local optimized commitment profile only through a
   second checked construction/correspondence.
8. **Related-SNARK pressure:** encode the Section 5.5 Toy Problem only as a
   structural/conjectural profile, then encode Definition 6.2's
   verifier-constructed word list passed to a proximity child. Do not promote
   either to a theorem claim through structural success.
9. **BaseFold holdout:** first add and validate the exact primary-source
    snapshot, then test shared-challenge composition across claim, sumcheck,
    and fold state.

Required negative cases include:

- derived-oracle cycle or future dependency;
- undefined quotient collision;
- uncovered derived index, missing `Fill` branch, or conflicting STIR
  OOD/shift assignments;
- answer-dependent route under the nonadaptive plan version;
- wrong source Oracle or source index type;
- loss of repeated query occurrences or causal dependencies;
- runtime emission of an occurrence absent from the authenticated Core;
- materializing a derived oracle as a prover message without a construction;
- absorbing a derived declaration or local availability effect as an invented
  transcript message;
- authenticating a virtual oracle under an invented root;
- reporting evaluator-limit exhaustion as a protocol rejection;
- treating powers-of-one-alpha batching as the independent-vector theorem;
- applying a scalar-terminal theorem to the early-stop profile; and
- treating a conditional or conjecture-instantiated WHIR premise as checked.

The central architecture should be reopened only if one of these occurs:

1. DEEP-ALI or STIR cannot be pre-elaborated into a finite declarative guarded
   occurrence structure without an unmodeled callback;
2. existing composition cannot relate a child's logical derived use to the
   elaborated target occurrences without widening its ownership model;
3. commitment compilation cannot authenticate flattened source reads without
   pretending the virtual oracle was published;
4. the BCS source experiment cannot accommodate any explicit and defensible
   initial-FRI-oracle mapping; or
5. WHIR claim evolution requires dynamic unbounded Core generation rather
   than finite pre-authenticated unrolling.

Until one of those failures is observed, the evidence favors testing a
targeted Oracle/composition-boundary candidate and additive protocol profiles,
not replacing the central architecture. It does not yet prove that the
candidate is minimal or compatible with the existing Core.

## 15. Open questions

1. Which exact initial-oracle convention should the literal BCS bridge use,
   and which outer relation grounds it?
2. Which collision/sampling law best matches the intended DEEP-FRI revision?
   The answer must be source-validated rather than inferred here.
3. Can `DerivedOracle` remain an authoring/construction declaration that is
   completely erased into an authenticated Core, or must the Core retain a
   first-class logical capability for downstream composition?
4. What checked map relates one child logical query/value to several guarded
   target occurrences without treating a runtime subschedule as already
   supported?
5. How should logical grouped fibre queries map to scalar source-query
   occurrences and physical multiproofs without losing theorem multiplicity?
6. Is pre-authentication elaboration sufficient with current value/object
   maps, or is a narrowly typed capability/object map required?
7. What total multipoint quotient and collision semantics correspond exactly
   to the selected DEEP-ALI source revision?
8. How does exact STIR execution resolve a point appearing in both the OOD and
   shifted sample families with inconsistent supplied answers?
9. Which WHIR parameter results are unconditional at the selected revision,
   and which depend on named mutual-correlated-agreement or list-decoding
   conjectures?
10. Should Circle FRI's function-space family be one algebra profile with
   layer-local laws or a checked composition of two profile families?
11. Which limits are semantic per-query expansion bounds, which are consumer
   occurrence counts, and which are nonsemantic evaluator budgets?
12. After source validation, do the Toy Problem, Definition 6.2/OPlonky, and
   BaseFold expose a pressure not already covered by DEEP-ALI and STIR?

## 16. Explicit nonclaims

This synthesis does not claim:

- implementation or durable-PIR support for any complete reviewed variant;
- correspondence between the finite early-stop witness and a paper theorem;
- randomized-Protocol or theorem correspondence for the exact classical
  deterministic control;
- that DEEP-FRI's sampling tension has been resolved;
- that DEEP-ALI's multipoint quotient or STIR's sample-collision semantics are
  total or source-corresponding;
- that a `DerivedOracle` design has passed formation, execution, composition,
  commitment, Relations, or Analysis tests;
- that current face maps can carry a derived capability, or that runtime query
  expansion fits the authenticated static occurrence model;
- that a finite query-plan test proves general expressiveness;
- FRI, batched FRI, DEEP-FRI, STIR, Circle FRI, or WHIR soundness;
- BCS applicability to the local typed SHA-256 commitment profile;
- random-oracle, QROM, knowledge, hiding, binding, or extraction security; or
- that the local paper hashes authenticate the papers or supersede source
  validation.

The narrow conclusion is architectural: the central separation remains
supported, while verifier-derived oracle access is a source-backed missing
capability. Static pre-authentication elaboration is the leading candidate;
the exact seam, identity ownership, and composition map remain open until the
constructive tests close them.
