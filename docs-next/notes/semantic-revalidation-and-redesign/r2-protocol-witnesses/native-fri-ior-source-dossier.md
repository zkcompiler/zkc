# Native FRI/IOR Source Dossier

> **Kind:** Temporary primary-source reconstruction and implementation-profile
> comparison
> **State:** Two-lane finite validation retained; the exact classical lane
> closes fixed-coin deterministic Algorithm 1 verifier-shape correspondence,
> while theorem applicability and cross-family conclusions remain open
> **Authority:** None. This page records source facts, deductions, profile
> choices, and unresolved theorem obligations. It does not define target
> semantics or establish FRI, commitment, Fiat--Shamir, or implementation
> security.

## 1. Research question and source discipline

This dossier asks what an exact semantic model must preserve when it represents
FRI first as an interactive oracle proof of proximity, then as a protocol with
authenticated oracle openings, and finally under a Fiat--Shamir
interpretation.

The three forms are related but are not one protocol with interchangeable
spellings. They have different messages, verifier capabilities, identities,
and theorem premises. The reconstruction therefore distinguishes:

1. the source IOP/IOPP interaction;
2. the commitment-and-opening compiler;
3. the noninteractive challenge interpretation;
4. concrete implementation profiles; and
5. the local finite profile selected only for falsification.

The principal primary sources are:

- Ben-Sasson, Bentov, Horesh, and Riabzev, [*Fast Reed--Solomon
  Interactive Oracle Proofs of Proximity*, ECCC revision
  2](https://eccc.weizmann.ac.il/report/2017/134/revision/2), and its [ICALP 2018 proceedings
  version](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2018.14);
- Ben-Sasson, Chiesa, and Spooner, [*Interactive Oracle
  Proofs*](https://eprint.iacr.org/2016/116), especially the transformation and
  state-restoration analysis in Sections 5--7;
- Block, Garreta, Katz, Thaler, Tiwari, and Zając, [*Fiat-Shamir Security of
  FRI and Related SNARKs*](https://eprint.iacr.org/2023/1071), especially its
  smooth multiplicative FRI, Section 5.2 batched construction, Section 5.7
  Algorithm 1, round-by-round analysis, and concrete discussion;
  and
- Attema, Fehr, and Klooß, [*Fiat--Shamir Transformation of Multi-Round
  Interactive Proofs*](https://eprint.iacr.org/2021/1377), used only for its
  exact multi-round theorem boundary rather than as a generic FRI theorem.

The executable package's source ledger binds five named paper artifacts used as
design inputs and two implementation snapshots used as comparison inputs. It
does not bind AFK or the other Analysis and variant-pressure citations in this
dossier. A citation locates a source, while a digest identifies bytes and checks
them only relative to a separately trusted expected digest. Neither establishes
provenance on its own or proves that a local deduction is correct.

## 2. Native FRI semantics

### 2.1 IOPP input and actors

FRI is an interactive oracle proof of proximity for a Reed--Solomon code. The
common input fixes the code specification, including the field, evaluation
domain, rate or degree bound, and distance measure. The initial function
`f[0]` is the purported codeword. The verifier receives oracle access to it and
the prover receives it as input.

This is not yet a cryptographic commitment. In the native model, “sending an
oracle” means fixing a function and granting the verifier the protocol's
specified query access. It neither discloses the whole function nor publishes
a Merkle root.

The initial oracle is semantically special. It is the object whose proximity
is tested, whereas later oracles are prover responses constructed after fold
challenges. The FRI definition calls `f[0]` the first-message format while
simultaneously giving the verifier oracle access to it, giving it to the
prover as explicit input, and excluding it from proof length and prover
complexity. The message-position name therefore does not by itself make
`f[0]` an adaptive prover-strategy output.

The selected native profile makes that ownership precise: `f[0]` is an
invocation-supplied oracle input fixed at the initial publication occurrence.
The finite commitment compilation then publishes its cap as the first target
proof message before the first fold challenge. A different outer embedding
may instead supply a pre-existing authenticated commitment as indexed public
input. That changes the target relation, statement bytes, and first public
occurrence; it must not be merged with this profile merely because one run has
equal roots. The outer predicate relating the public statement to the initial
oracle remains open here.

### 2.2 Commit phase

Let `f[i] : L[i] -> F` be the oracle fixed at layer `i`. For the smooth
multiplicative binary specialization, the quotient map is `q_i(x) = x^2` and
`L[i+1] = q_i(L[i])`. One round has the following causal order:

```text
f[i] is fixed
    -> verifier samples beta[i]
    -> prover fixes f[i+1]
```

For antipodal points `x` and `-x`, write `a=f[i](x)` and `b=f[i](-x)`. The
binary fold is

```text
Fold(beta, a, b, x)
  = (a + b)/2 + beta * (a - b)/(2x).
```

The general source protocol uses a localization polynomial and interpolation
over a whole fibre; binary folding is the size-two specialization. Additive
domains, multiplicative domains, binary fibres, and higher-arity fibres are
therefore exact profiles, not implicit variants of one untyped operation.

Every published oracle remains immutable and queryable through the final
decision. A later oracle may depend on all earlier public challenges but not
on a future challenge or final query randomness.

### 2.3 Terminal material

The general FRI source does not publish another large final oracle. It sends a
bounded coefficient representation of the terminal low-degree polynomial, and
the verifier reconstructs the terminal function from those coefficients.
The common binary presentation often folds until the terminal function is a
constant and sends that scalar directly. Real implementations may stop earlier
and send a short coefficient vector.

These are distinct terminal contracts:

- general bounded coefficient vector;
- clear constant scalar;
- committed terminal vector; or
- short coefficient vector with an implementation-specific order and bound.

Terminal material is fixed before query randomness. It is neither acceptance
nor proof that the preceding oracle is low degree.

### 2.4 Query phase

All query randomness is chosen after every oracle and the terminal material
are fixed. For each ordered query occurrence, the verifier:

1. samples one point in the initial domain;
2. derives its image through every domain quotient;
3. queries the complete fibre required at each nonterminal layer;
4. interpolates that fibre;
5. evaluates the interpolant at the corresponding fold challenge; and
6. compares the result with the next-layer value, or with the terminal
   polynomial evaluation at the last layer.

The verifier accepts exactly when every required consistency equation and the
terminal-degree condition hold. Rejecting a failed check is a protocol
terminal. Resource exhaustion, unavailable oracle access, or a checker defect
is not a third FRI verdict.

Query draws are occurrences. Repeated points are valid and remain distinct in
the source probability experiment. An implementation may share values or
authentication nodes, but that physical compression cannot change the number
or order of logical draws.

Accordingly, the native Core owns one ordered query-occurrence vector sampled
directly with replacement. It does not own a byte seed. The selected
Fiat--Shamir construction uses a query seed only as internal derivation state
and expands it to resolve that same Core vector.

### 2.5 What native acceptance means

An accepting execution means only that this verifier accepted this interaction
under its sampled coins. FRI soundness is a quantified probabilistic claim
about all permitted prover strategies and a proximity relation. It is not an
execution invariant.

FRI acceptance alone does not establish:

- that the initial oracle is exactly a low-degree codeword;
- that it is close to the code without the selected theorem and premises;
- knowledge of polynomial coefficients;
- an AIR, trace, circuit, or computation relation;
- commitment binding or hiding; or
- Fiat--Shamir security.

## 3. Commitment-and-opening compilation

### 3.1 Literal transformation shape

The 2016 IOP transformation treats prover oracle messages as bit strings and
uses separate random-oracle purposes for verifier randomness and Merkle/hash
work. For statement `x`, its central chain is:

```text
sigma[0] = rho_hash(x)

for each IOP round i:
    m[i]     = rho_coin(x || sigma[i-1])
    f[i]     = next prover oracle message
    root[i]  = MerkleRoot(f[i])
    sigma[i] = rho_hash(root[i] || sigma[i-1])

query_randomness = rho_coin(x || sigma[last])
```

The noninteractive proof carries the roots, values and authentication paths
needed for the verifier's logical queries, and the final chain value. The
verifier reconstructs the challenges and query locations, runs the IOP
decision logic over opened values, and authenticates every logical query
against the corresponding earlier root.

This yields non-negotiable structural requirements:

- a commitment to each oracle precedes every coin that may depend on it;
- the statement participates in initial state and every coin derivation;
- root order is fixed by the chain;
- query randomness follows all committed interaction material;
- every consumed value is tied to an exact oracle, position, and root; and
- opening material cannot retroactively choose the committed oracle.

The transformation does not define field codecs, grouped leaves, tree arity,
padding, caps, salts, multiproofs, prime-field sampling, or a portable proof
serialization. Those belong to an exact compilation profile.

### 3.2 Source and target are different protocols

The native verifier possesses a logical oracle-access capability. A committed
verifier possesses roots or caps and later proof-supplied openings. It does not
possess the confidential complete oracle.

Consequently, a public verifier that replays `PublicBinding` by receiving the
full private oracle is not a faithful committed verifier. Likewise, a native
oracle represented by publishing its full carrier gives the verifier more
information and work than the IOP specifies.

The retained factorization is therefore:

```text
native logical-oracle Core
    -> checked profile-bound commitment/opening construction
committed interactive Core
    -> admitted checked same-Core Fiat--Shamir construction
committed noninteractive Protocol
```

The first arrow changes the verifier-observable interaction and has distinct
source and target Core identities. The exact classical lane admits one checked
structural construction for its fixed source/target/profile triple and retains
an inert receipt for one concrete execution. That does not establish a
universal FRI compiler or a cryptographic commitment property. The second
arrow changes challenge interpretation while sharing the committed Core and
is admitted at its structural scope.

### 3.3 Initial-oracle fork

There are at least two valid compilation profiles:

1. take the initial logical oracle as an indexed, invocation-supplied source
   input and publish its cap as the first target proof message before the first
   fold challenge; or
2. make an already authenticated initial commitment part of the target indexed
   statement and compile only later oracle messages.

The second form is common in larger proof systems, where an outer polynomial
commitment or trace commitment supplies FRI's initial values. It is not a
drop-in representation of the first. The source relation, statement bytes,
first branch point, and theorem game differ.

The finite witness selects the first form because it exercises the complete
native-to-committed path. This is compatible with the source's
"first-message" nomenclature, but does not turn the fixed source oracle into
an adaptive prover decision and does not establish the outer
statement-to-oracle predicate. An outer system may select the second form
through a different construction.

### 3.4 Randomized commitments

Commitment salts or randomness are construction-owned prover material. They
are not logical-oracle entries, public statement values, or automatically an
outer relation witness. The root construction consumes both logical material
and exact construction advice; openings reveal only the advice required for
their selected leaves.

A deterministic seed is useful for a reproducible finite fixture. It is not
evidence of hiding, entropy, independence, or production-safe randomness.

## 4. Fiat--Shamir and security-analysis boundary

### 4.1 Structural construction

The committed Core is public coin when all verifier messages and query choices
are derived from declared public randomness and no verifier-private dependency
reaches an accepting sink. A Fiat--Shamir construction must then bind the exact
statement, application context, ordered caps, terminal material, grinding
nonce when present, namespaces, codecs, and samplers.

The local finite profile places work in this order:

```text
statement and application context
    -> cap[0] -> fold challenge[0]
    -> cap[1] -> fold challenge[1]
    -> terminal coefficients
    -> work-seed challenge
    -> grinding witness and check
    -> ordered query draws
    -> openings and verifier checks
```

Openings occur after the last protected random choice and therefore need not
feed another challenge in this exact profile. A future protocol that derives
later coins must absorb the relevant opening publications as ordinary prior
prover material.

Original native FRI has no work-seed, nonce, or grinding rejection path. The
selected committed profile therefore introduces those effects through a
grinding augmentation declaration separate from oracle-commitment compilation.
The finite witness checks that declaration only for one exact execution and
issues a validation-bound receipt; generally admitted augmentation remains
open. Its Fresh and Fiat--Shamir forms then share the same augmented Core:
Fresh supplies an independent work seed, while the Fiat--Shamir interpretation
derives that seed from the protected transcript prefix.

### 4.2 Theorem premises are not structural fields

The literal IOP transformation's soundness theorem assumes restricted
state-restoration soundness and includes an additive random-oracle collision
term. Modern FRI analysis instead establishes a particular round-by-round
property and applies a later theorem. Ordinary interactive soundness,
state-restoration soundness, round-by-round soundness, and special soundness
are not aliases.

State restoration is an Analysis game over immutable prefix states. It does
not grant the runtime Core a rollback operation. The game permits an adversary
to branch from previously seen verifier states under an exact restriction and
budget; the Core still executes one forward interaction.

An Analysis judgment must name at least:

- the exact source and target Protocols and, where the theorem crosses a
  construction, its generally admitted checked construction; a one-execution
  receipt cannot fill this slot;
- classical or quantum random-oracle model;
- adversary strategy and oracle-query interface;
- restricted or unrestricted restoration law, or exact round-by-round law;
- commitment assumptions and random-oracle purpose separation;
- query, work, and state budgets;
- source theorem revision and exact proposition; and
- quantitative loss expression and every unproved premise.

No finite witness in this package establishes those premises.

## 5. Implementation-profile comparison

### 5.1 Plonky3

The repository's retained Plonky3 replay pins revision
`3da346791c813433b201299afc3d10bf42f8a078`. The selected files at that pinned
revision demonstrate why an implementation profile cannot be collapsed into
generic FRI:

- input commitments may cover matrices of different heights;
- FRI leaves group adjacent values in bit-reversed order;
- fold arity can vary by round;
- commitments can be ordered Merkle caps rather than one digest;
- input and fold-round openings use shared multiproofs;
- ordered query draws retain multiplicity even when authentication frontiers
  are deduplicated;
- extension values are flattened in a profile-specific basis order; and
- terminal coefficients and the realized arity schedule are transcript
  material.

The exact proof serializer is a separate choice. A language-level serialization
derivation is not by itself a canonical interoperable wire format.

### 5.2 Winterfell

The compared Winterfell source is pinned at revision
`2f78ee9bf667a561bdfcdfa68668d0f9b18b8315`. Its selected profile makes
materially different choices:

- fixed arity-four fibres;
- one binary Merkle root rather than a cap;
- a Blake3 hash-chain public coin;
- ordered draws followed by explicit sorting and deduplication;
- one batch Merkle proof per layer;
- initial values authenticated by the surrounding STARK layer rather than the
  standalone FRI proof object; and
- a bounded reversed terminal-coefficient vector rather than a clear scalar.

The standalone verifier consumes initial evaluations from its caller. That is
evidence that initial-oracle ownership belongs to an explicit outer seam, not
to a universal FRI proof-object field.

### 5.3 Shared semantic nucleus

The two profiles and the papers agree on a small nucleus:

- explicit field, degree, and domain geometry;
- oracle fixation or cryptographic commitment before the corresponding fold
  challenge;
- exact fibre-to-parent fold arithmetic;
- query randomness after commit-phase material;
- authentication of every value consumed by the committed verifier;
- an exact occurrence-to-opening relation; and
- agreement of every completed fold chain with the terminal polynomial.

Everything else is an exact profile: encoding, evaluation order, fibre layout,
arity schedule, cap/root representation, hashing, transcript transition,
sampling, work placement, deduplication, opening proof, terminal encoding, and
initial-oracle ownership.

## 6. Candidate-model disposition

The candidate architecture already had immutable oracles, causal prover views,
public-coin analysis, strong transcript influence, typed relation-oracle
statements, commitment grounding, and Analysis-owned theorem propositions.
Native FRI required the following completions and retained boundaries.

### 6.1 Logical access without disclosure or commitment

Native IOP access needs a third meaning beyond full publication and public
binding: the Oracle is fixed and queryable under an exact domain law, but
neither its full carrier nor a cryptographic binding is published. The PIR
target now owns this as `LogicalAccess`.

Such a Core is Fresh-valid. It is not directly eligible for same-Core
Fiat--Shamir when the oracle affects acceptance, because no public value binds
its content before dependent challenges.

The finite executable representation retains complete carriers inside one
trusted evaluator. Its exported publication view and query resolver expose
only metadata and selected answers, so it checks the intended extensional
behavior. It does not enforce host-level confidentiality or noninterference.
That limitation is an explicit residual, not evidence that the verifier lacks
access to unqueried entries. A durable runtime requires a separately admitted
owner carrier and a restricted exact-domain query handle.

### 6.2 Total exact-domain oracles

The generic finite oracle is a bounded partial map with a present/absent lookup
result. FRI's layer functions are total on exactly their declared domains.
An owner-local domain law must reject missing, duplicate, or extra points and
derive a total element answer. This is a profile law over the standard oracle
lifecycle, not permission for callers to assert totality.

### 6.3 Initial versus prover-authored Oracle material

The initial Oracle may be invocation- or relation-supplied, whereas later
Oracles are causal strategy decisions. Treating all three as strategy-authored
changes the proximity statement. PIR therefore distinguishes `InitialOracle`
from `ProverOracle` and gives the former an owner-local pre-execution supply
capability.

### 6.4 Checked commitment compilation

The same-Core Fiat--Shamir construction is intentionally insufficient for an
IOP compiler. The admitted exact structural source-to-target construction
relates:

- source logical oracle publications to target caps;
- source query occurrences to target derived positions;
- source answers to selected opened values;
- target opening messages to earlier caps and exact positions;
- logical multiplicity to physical deduplication;
- native consistency checks to target fold and terminal checks; and
- construction advice to its owner without adding it to logical-oracle
  identity.

Its structural success proves no binding, hiding, extraction, soundness, or
general FRI-family compilation.

### 6.5 Opening correspondence

Public commitment grounding remains distinct from opening and initial-material
agreement. For the exact logical initial Oracle, PIR now owns a causal,
purpose-bound confidential view and Relations owns the matching whole-carrier
agreement question. No public run view, declassified trace, or secret-derived
identity can substitute for those live owner authorities. The checked
construction separately connects source answer occurrences, target opening
selectors, public roots, query occurrences, and authentication checks.
Cryptographic binding remains an Analysis premise.

## 7. Source ambiguities and non-silent choices

The following must remain explicit:

- the full FRI pseudocode has an apparent commit-loop off-by-one; the narrative
  and query interface support exactly the challenges needed to construct the
  terminal polynomial, not an extra unused challenge;
- displayed aggregate query counts do not erase the separate reads of terminal
  coefficients;
- “commit” in native FRI means oracle fixation, not Merkle commitment;
- literal BCS operates on bit-string messages, while field-element leaves
  require a checked generalized vector-commitment profile;
- literal BCS emits one path per logical query; multiproofs and deduplication
  are representation transformations with an occurrence map;
- prime-field challenge sampling needs an exact bias or rejection rule;
- a clear terminal scalar and an all-message Merkle compilation are different
  constructions; and
- adding typed transcript domains or persistent state may strengthen or change
  the literal two-purpose random-oracle construction and therefore requires a
  theorem-applicability argument.

## 8. Selected finite profile

The executable witness uses an independently derived profile chosen to exercise the shared
nucleus and the implementation forks without claiming conformance to either
library:

| Coordinate | Selected value |
|---|---|
| base field | `F_97` |
| multiplicative generator | `5` |
| domains | order `16`, `8`, and `4`, with generators `8`, `64`, and `22` |
| extension | `F_97[u]/(u^2-5)`, ordered coordinates `(a,b)` |
| rounds | two binary folds |
| initial semantic degree bound | less than `8` |
| terminal semantic degree bound | less than `2` |
| query occurrences | four ordered draws with replacement |
| logical oracle layers | initial order-16 oracle and one order-8 folded prover oracle |
| terminal | canonical coefficient sequence, syntactically bounded separately from the degree check |
| commitment | salted SHA-256 binary tree over antipodal-pair leaves |
| public commitment | ordered cap of two nodes |
| salts | sixteen bytes per leaf, derived deterministically only for fixture reproduction |
| work | explicit 32-byte work-seed challenge, then a two-bit pre-query grinding predicate |
| sampling | typed SHA-256 calls and bounded big-endian rejection sampling |

This is an implementation-style **early-terminated structural profile**, not
the exact protocol instance of Section 5.7 Algorithm 1 in ePrint 2023/1071.
For `d0 = 8 = 2^3`, that algorithm performs three folds and sends a scalar
constant after the third fold. The executable profile deliberately performs
two folds and sends a degree-less-than-two polynomial. Original FRI Section
3.2 independently gives three binary-localization rounds for the analogous
`k = 4`, `R = 1`, `eta = 1` parameter calculation. No theorem correspondence
or early-termination theorem is claimed for the executable choice.

The syntactic terminal carrier permits a canonical polynomial of bounded size;
the verifier separately checks degree less than `2`. This prevents a parser
shape from authoring the positive result. The honest fixture uses a nonconstant
terminal polynomial so coefficient order and Horner evaluation are exercised
on the positive path.

Salted leaves, pair grouping, cap height, typed SHA-256 framing, work, and the
terminal carrier bound are local compilation choices. They are not attributed
to native FRI.

### 8.1 Exact classical control

The retained additive control removes the early-stop source-shape ambiguity
without rewriting the earlier lane:

| Coordinate | Selected value |
|---|---|
| source locator | ePrint 2023/1071 revision 7, Section 5.7, Algorithm 1 |
| base field | Goldilocks prime field |
| initial domain | multiplicative subgroup of order `64` |
| initial degree bound | less than `8 = 2^3` |
| rounds | three binary folds |
| terminal | one scalar `C` after the third fold |
| query occurrences | four labelled draws with replacement |
| logical layer checks | twelve, one at each of three layers per draw |
| committed target | three salted SHA-256 pair-leaf roots plus proof-supplied openings |
| challenge forms | Fresh and strong Fiat--Shamir over one committed Core |

For fixed verifier coins, the control maps the source's Oracle fixation,
challenge, folded-Oracle, scalar-terminal, query, complete-fibre, and check
order. Frozen public input and proof are reconstructed by a separately coded
verifier. The Goldilocks choice, four repetitions, Statement and application
context, Merkle profile, physical-opening deduplication, framing, samplers, and
resource policy are local zkc choices rather than Algorithm 1 claims.

This is deterministic schedule/control correspondence only. The executable
Fresh resolver receives concrete coins; it does not establish the source coin
law, strategy quantification, non-anticipation, a probability experiment,
theorem applicability, BCS, commitment security, ROM, QROM, proximity, or an
outer relation.

The following remain additive validation obligations, not current features or
claims:

1. the batched FRI schedule of ePrint 2023/1071 Section 5.2, including several
   initial oracles, the coefficient challenge vector, and the combined oracle;
2. verifier-derived quotient-oracle views and nested proximity tests from
   DEEP-ALI Protocol 6.4; and
3. the virtual quotient, degree-corrected oracle, partial `Fill` oracle, and
   dynamic query routing of STIR Construction 5.2.

These obligations extend profiles and the oracle/composition seam. They do not
change the selected native/commitment/augmentation/Fiat--Shamir factorization.

## 9. Required executable conclusions

The finite package must answer, with independent public reconstruction:

1. whether the native logical interaction can be represented without full
   oracle disclosure;
2. whether the committed verifier can run from public statement and proof only;
3. whether a checked map preserves logical query occurrences while sharing
   opening material;
4. whether every cap precedes its dependent challenge and terminal material
   precedes query randomness;
5. whether authentication, fold consistency, terminal degree, and protocol
   acceptance remain separate first boundaries;
6. whether relation grounding stops at FRI's oracle/proximity statement; and
7. whether the current domain owners can absorb the required extensions
   without introducing a universal FRI object.

A successful finite result establishes only one source-informed structural
inhabitant and its named refusals. Failure at any one of these boundaries is an
architecture finding, not a reason to weaken the witness.

The case-level result, gate disposition, retained two-lane evidence boundary,
and reopening conditions are consolidated in the
[final classification and retention record](native-fri-ior-final-classification-and-retention.md).
