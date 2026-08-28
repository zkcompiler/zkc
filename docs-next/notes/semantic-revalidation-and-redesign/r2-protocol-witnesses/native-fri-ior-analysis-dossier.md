# Native FRI/IOR Analysis Dossier

> **Kind:** Temporary theorem and experiment research record
> **State:** Requirements selected for constructive validation; no theorem has
> been imported as checked proof
> **Authority:** None. This page separates published theorem statements from
> local arithmetic checks, retained truth assumptions, and prohibited claims.
> It neither establishes a property nor changes the durable Analysis model.

## 1. Result in one view

Native FRI, commitment compilation, and Fiat--Shamir are not one security
claim. The minimum honest property graph is:

```text
native IOPP experiment
  + exact Reed--Solomon proximity relation
  + theorem-specific hypotheses
       -> native proximity or round-by-round property

native property
  + exact oracle-commitment compiler
  + a theorem for the selected branching game
       -> committed interactive property

committed interactive property
  + exact grinding augmentation
  + placement- and resource-specific grinding theorem
       -> work-augmented committed property

work-augmented committed property
  + exact random-oracle experiment
  + one applicable transformation theorem
       -> classical-ROM property

QROM property or knowledge property
       -> only through its own experiment and theorem edge
```

The executable FRI case may check the interaction, commitment openings,
transcript, and deterministic verifier result. It cannot discharge any arrow
above. Analysis must own the quantifiers, adversary capabilities, branching
game, resource coordinates, theorem statement, applicability, and retained
truth premise for each arrow.

This leads to four rules:

1. proximity soundness, vector round-by-round soundness, restoration
   soundness, classical-ROM soundness, QROM soundness, and knowledge are
   different properties;
2. native logical-oracle access, commitment-hash access, and Fiat--Shamir
   random-oracle access are different capabilities and resource dimensions;
3. a theorem edge is identified by its exact source and target experiments,
   not by a label such as “FRI soundness”; and
4. a finite parameter calculation may refute applicability or show that a
   bound is vacuous, but it cannot prove the theorem or the property.

## 2. Evidence discipline

The following classifications are orthogonal and must remain visible in every
future Analysis result.

| Classification | Meaning |
|---|---|
| **Paper-stated theorem** | The selected primary source states the recorded theorem under the recorded hypotheses. Source authentication and transcription are still separate obligations. |
| **Local parameter check** | A bounded evaluator checked arithmetic side conditions or instantiated a formula. It did not check theorem truth, protocol correspondence, or an adversarial experiment. |
| **Retained theorem-truth assumption** | The exact theorem statement is used conditionally because no checked proof artifact discharges its truth. This is the required status for every theorem below at present. |
| **Nonclaim** | The local evidence is intentionally insufficient for the stated conclusion; no downstream consumer may treat it as established. |

A paper-stated theorem therefore normally has both `PaperStated` provenance
and `RetainedTheoremTruthAssumption` discharge. `EstablishedByCheckedProof`
would require a separately admitted proof artifact over the same theorem
schema. A citation, PDF digest, successful test, or parameter calculator is not
that artifact.

## 3. Primary theorem matrix

Notation in this section is local. `N` is an evaluation-domain size, `rho` is
code rate, `delta` is relative distance, `ell` is the number of logical query
draws, `Q` is an adversary random-oracle-query bound, `b` is a restoration
budget, `r` is the number of interaction rounds, and `kappa` is a random-oracle
output length. A source's original variable name is renamed only to prevent
collision; the typed theorem schema must retain the source binding.

| Source edge | Exact paper-stated shape | Required experiment distinction | Local disposition |
|---|---|---|---|
| Original FRI IOPP | For the binary additive Reed--Solomon family with `rho = 2^-R`, `R >= 2`, `rho N > 16`, a `delta`-far word is rejected with probability at least `min(delta, delta0) - 3N/|F|`, where `delta0 >= (1/4)(1 - 3rho) - 1/sqrt(N)`; the paper separately remarks on smooth multiplicative domains. | Native oracle access and a distance promise; no commitment or random oracle. The conclusion is a rejection lower bound, not an execution invariant. | Paper-stated; retained assumption. The selected finite profile is not an instance of the literal binary-additive theorem. |
| Direct FRI round-by-round result | Under Theorem 4.1's smooth multiplicative hypotheses, `epsilon_rbr = max{ ((m + 1/2)^7 |L0|^2)/(3 rho^(3/2) |F|), (1 - delta)^ell }`. Theorem 5.11 gives the same expression as the round-by-round knowledge error for its named doomed set and extractor. | A vector- or round-indexed doomed-prefix experiment. Knowledge additionally owns an extractor and witness relation. | Paper-stated; retained assumption. The finite positive execution is not a doomed-prefix experiment. |
| Round-by-round to restoration | Round-by-round error `epsilon_rbr` gives restoration error at budget `b` bounded by `b epsilon_rbr`; for a vector, use the theorem-selected aggregate such as `b max_i epsilon_i`. | A branching experiment over previously reached verifier states, with an explicit branch-extension budget. | Paper-stated edge; retained assumption. No Core rollback operation is introduced. |
| Restoration to round-by-round | Holmgren proves that a public-coin `r`-round protocol that is `(q, epsilon)`-sound against restoration attacks has round-by-round error at most `(r/q) ln(2r/(1-epsilon))`. | Unrestricted restoration and round-by-round experiments remain distinct even though they are asymptotically equivalent. | Paper-stated; retained assumption. The conversion is not lossless. |
| BCS compilation | Theorem 7.1 gives `epsilon_NI(x,Q,kappa) = barred_s_sr(x,Q) + 3(Q^2 + 1) 2^-kappa`, with the analogous proof-of-knowledge expression, from **restricted** restoration security of the public-coin IOP. | Restricted restoration forbids returning to the empty verifier state after the initial iteration. The target has a random oracle and authenticated openings. | Paper-stated; retained assumption. A SHA-256 fixture is not this random-oracle experiment. |
| Special soundness to vector round-by-round soundness | A `(k1,...,k_mu)`-special-sound IOP with challenge sets `C_i` has vector errors `epsilon_i = (k_i - 1)/|C_i|`. Standard soundness is at most `1 - product_i(1 - epsilon_i)`. | Transcript-tree extraction and doomed-prefix persistence are separate experiments connected by an explicit theorem. | Paper-stated; retained assumption. The same source proves that special soundness does **not** imply round-by-round knowledge soundness. |
| Special soundness to QROM soundness | For `epsilon = max_i (k_i - 1)/|C_i|`, the cited BCS-style transform has adaptive QROM soundness `O(t^2 epsilon + t^3/2^kappa)` against the source's adjusted quantum-query budget. | Quantum superposition access is a distinct oracle ABI, schedule, observation law, and resource type. | Paper-stated asymptotic result; retained assumption. It gives soundness, not QROM knowledge soundness. |
| Direct FRI to classical ROM | Combining the FRI round-by-round theorem with the cited compilation gives `epsilon_fs = Q epsilon_rbr + 3(Q^2 + 1)/2^kappa`. The source also states a QROM bound only asymptotically as `Theta(Q epsilon_fs)` with an adjusted query budget. | The exact FRI algorithm, commitment transform, random-oracle experiment, and query accounting are all theorem premises. | Paper-stated; retained assumption. The hidden constants make the QROM expression unsuitable as a concrete local bound. |
| Multi-round Fiat--Shamir knowledge | For a `(k1,...,k_mu)`-special-sound protocol, `kappa_FS(Q) = (Q + 1) kappa_IP`, where `kappa_IP = 1 - product_i(1 - (k_i - 1)/N_i)`. The extractor makes at most `K + Q(K - 1)` expected adversary calls for `K = product_i k_i`. | Classical random-oracle knowledge extraction with consistent answers, exact challenge sets, and expected extractor cost. | Paper-stated; retained assumption. It is not a generic FRI soundness theorem. |
| Grinding over vector errors | For round errors `(epsilon_1,...,epsilon_mu)` and per-round difficulties `(z_1,...,z_mu)`, the grinded interactive experiment has errors `epsilon_i 2^-z_i`; after the stated compilation, `epsilon_NI(T,kappa) <= T max_i{epsilon_i 2^-z_i} + 3(T^2 + 1)/2^kappa`. | Each proof-of-work is placed before the coin it protects; random-oracle trials and expected honest work are separately counted. | Paper-stated for the named experiment; retained assumption. A nonce predicate alone earns no security bits. |

Primary sources and exact locators:

- Ben-Sasson, Bentov, Horesh, and Riabzev,
  [*Fast Reed--Solomon Interactive Oracle Proofs of Proximity*, Theorem
  2](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2018.14);
- Ben-Sasson, Chiesa, and Spooner,
  [*Interactive Oracle Proofs*, Sections 5.4 and 7, Theorem
  7.1](https://eprint.iacr.org/2016/116.pdf);
- Holmgren,
  [*On Round-By-Round Soundness and State Restoration Attacks*, Theorems 1.1
  and 3.2](https://eprint.iacr.org/2019/1261.pdf);
- Block, Garreta, Katz, Thaler, Tiwari, and Zajac,
  [*Fiat-Shamir Security of FRI and Related SNARKs*, Theorems 3.15, 4.1, and
  5.11 and Corollary 4.3](https://eprint.iacr.org/2023/1071.pdf);
- Block, Garreta, Tiwari, and Zajac,
  [*On Soundness Notions for Interactive Oracle Proofs*, Theorems 1.1 and 1.4
  and Corollaries 1.5 and 1.6](https://eprint.iacr.org/2023/1256.pdf);
- Attema, Fehr, and Klooß,
  [*Fiat--Shamir Transformation of Multi-Round Interactive Proofs*, Equation
  (1) and Theorems 2 and 3](https://eprint.iacr.org/2021/1377.pdf); and
- Ben-Sasson et al.,
  [*ethSTARK Documentation*, Sections 6.1 and 6.3 and Theorems 6 and
  8](https://eprint.iacr.org/2021/582.pdf).

The theorem rows are deliberately not collapsed. For example, the direct FRI
round-by-round theorem and the special-soundness route can target similarly
named properties while using different premises, extractors, and losses.

## 4. Bounded-profile arithmetic check

The constructive case selects `F97`, an order-16 multiplicative domain,
degree bound `d0 = 8`, rate `rho = 1/2`, two folds, and four ordered query
draws. This supports the following local checks only.

1. The literal binary-additive hypotheses of original FRI Theorem 2 do not
   match: the field is odd, `rho` is not of the required `2^-R` form with
   `R >= 2`, and `rho N = 8` is not greater than `16`.
2. Even a formula-only substitution using the local domain and field, together
   with `m = 3`, `delta = 1/10`, and `ell = 4`, makes the first displayed term
   of `epsilon_rbr` greater than `16009`, while `(1-delta)^ell = 0.6561`.
   This calculation does not assert that the theorem's other side conditions
   hold.
3. The resulting displayed maximum is vacuous as a probability bound, so no
   theorem-applicability or security claim can be obtained from it.
4. The positive fixture begins with an honestly generated low-degree word. It
   therefore does not supply the theorem's `delta`-far premise or a false
   instance on which soundness is measured.
5. Two bits of grinding can exercise placement, framing, and nonce search.
   They do not justify multiplying any local error by `1/4` until the exact
   grinding experiment and its random-oracle resource transform apply.

These are useful outcomes: the small profile can falsify semantic structure
without being mistaken for a meaningful security parameterization. A later
large-parameter evaluator must be a separate artifact with exact integers,
interval or rational arithmetic, and theorem-owned side-condition checks.

## 5. Required Analysis model

### 5.1 Property families are not subtypes

The minimum catalog needs distinct coordinates for:

- native IOPP proximity soundness and completeness;
- scalar and vector round-by-round soundness;
- round-by-round knowledge soundness;
- restricted and unrestricted restoration soundness;
- restoration knowledge soundness;
- generalized special soundness and special unsoundness;
- adaptive classical-ROM soundness;
- adaptive classical-ROM knowledge soundness and extraction;
- adaptive QROM soundness; and
- grinding-adjusted variants parameterized by exact placement.

No property may be obtained by changing an experiment-model flag. In
particular, soundness does not imply knowledge, special soundness does not
imply round-by-round knowledge, classical ROM does not imply QROM, and a
scalar error does not silently stand for an error vector.

### 5.2 Exact experiment profiles

Each property profile must fix:

- the indexed relation, code family, distance metric, true/false-instance
  predicate, and witness type, if any;
- the ordered quantifier prefix over parameters, instances, strategies,
  verifier coins, oracles, and extractors;
- the strategy ABI and its causal views of fixed oracles, messages, coins,
  query answers, auxiliary input, and advice;
- the public-coin, logical-oracle, classical random-oracle, or quantum
  random-oracle capability exposed to each actor;
- scheduler, abort, invalid-move, sampling-failure, nontermination, and
  terminal laws;
- the observation and win event; and
- the complete typed resource basis.

For this FRI profile the Core challenge is the ordered query-occurrence vector,
not the Fiat--Shamir construction's internal query seed. Fresh samples the
vector directly; the FS interpretation derives and expands a seed to resolve
the same typed Core value. Any equivalence, closeness, or security statement
about those sampling experiments needs its own theorem premises and cannot be
inferred from same-Core identity.

The executable identity graph now preserves that separation. The
`FriAlgebraProfile` owns the field, domain chain, binary fold, direct ordered
query-vector law, native answer projection, and terminal evaluator. A distinct
`FriCommitmentProfile` owns the leaf and node codecs, salted tree, ordered cap,
and authentication-path law. The transcript construction plan owns its framing,
samplers, and query-seed expansion. Consequently a Merkle or transcript change
does not rotate the native algebra profile, while a change to a fold or native
query-vector rule does.

The finite native evaluator also stores complete oracle carriers while
exposing only selected answers through its modeled verifier view. It can test
observation discipline, but not capability noninterference at the host-language
boundary. Until owner-side admission issues a restricted query handle, this is
a retained execution-model residual rather than a discharged capability
premise.

The native IOPP experiment consumes logical oracle queries. A compiled
experiment consumes proof-supplied openings and commitment checks. A ROM
adversary consumes random-oracle queries. Equal numeric counts across those
experiments do not identify the resources.

### 5.3 Doomed-prefix and restoration games

Round-by-round soundness requires a theorem-owned family of doomed sets over
typed partial transcripts. For every round, it quantifies over a doomed
prefix, every legal next prover message, and the distribution of the next
verifier challenge. A complete doomed transcript must map to verifier
rejection. Round-by-round knowledge additionally invokes its extractor when
the escape probability crosses the theorem threshold.

Restoration is an Analysis scheduler over a reached-prefix set:

```text
reached := {initial prefix}
repeat within budget b:
    adversary selects an allowed reached prefix and next prover message
    verifier samples fresh next-round randomness
    append the resulting prefix to reached
win iff reached contains a theorem-defined accepting leaf
```

The restricted game separately forbids a return to the empty state after its
first iteration. Neither game rewinds a live Protocol execution, mutates an
immutable Core, or exposes a replay-engine control to the prover.

### 5.4 Resource coordinates

At minimum, the profiles must distinguish:

| Resource | Why it cannot be merged |
|---|---|
| Ordered logical query draws | Repetitions remain separate probability-experiment occurrences. |
| Unique opened positions | Deduplication changes proof work, not logical sampling. |
| Authentication nodes and hash invocations | A cap, binary path, or multiproof has profile-specific physical cost. |
| Adversary classical random-oracle queries | Appears directly in classical Fiat--Shamir losses. |
| Adversary quantum random-oracle queries | Has a different capability and theorem loss. |
| Restoration branch extensions | Prices the branching attack, not ordinary verifier calls. |
| Grinding trials and proof-of-work checks | Expected honest trials and adversarial oracle calls have different aggregation. |
| Extractor invocations and adversary calls | Knowledge theorems may use expected rather than worst-case cost. |
| Proof symbols, bytes, time, and memory | Representation and implementation resources require exact codecs and algorithms. |

A theorem transform must name source and target resource coordinates and the
exact arithmetic operation on them. It cannot accept an ambient integer named
`queries` or `cost`.

### 5.5 Construction and theorem separation

The checked oracle-commitment construction may establish deterministic
correspondence between native queries and authenticated target openings. A
separate checked grinding augmentation may establish the insertion and
placement of a work-seed challenge, nonce publication, and work predicate. The
same-Core Fiat--Shamir construction may establish complete transcript
influence and deterministic challenge reconstruction. None establishes:

- collision resistance, binding, hiding, or extractability;
- native proximity soundness or round-by-round soundness;
- preservation of a property across commitment compilation;
- quantitative soundness amplification from grinding;
- random-oracle or quantum-random-oracle security; or
- knowledge extraction.

Analysis must therefore bind each theorem to exact source and target Core or
family views, exact construction identities, exact relation meanings, and an
occurrence map. A changed cap shape, leaf codec, query-deduplication policy,
transcript framing rule, grinding position, or initial-oracle convention may
invalidate applicability without changing the theorem text.

The finite executable catalog represents those bindings as local application
coordinates. Every question binds one exact source and target Core or Protocol.
Construction declarations and admitted constructions occupy different typed
slots: the presently admitted Fiat--Shamir construction is bound exactly,
whereas commitment-compilation and grinding declarations are bound but their
checked-construction slots remain explicitly open. No reviewed canonical
Relations schema or construction-specific opening map is available yet, so
those slots carry no invented identity and instead point to named open
applicability obligations. The native logical-query-to-layer-answer projection
is the one currently bound occurrence map because its exact owner and identity
already exist.

A bound coordinate is not correspondence evidence. It identifies the local
candidate to which a theorem might apply; it does not show that a source
paper's experiment, relation, or resource accounting matches that candidate.

### 5.6 Theorem import and applicability

Every theorem row needs three separately rotating identity layers:

1. a semantic theorem schema containing local binders, source and target
   property schemas, source and target experiment schemas, required views,
   maps, side conditions, resource/loss transform, and conclusion law; and
2. source validation containing the exact publication revision, artifact
   digest, theorem and definition locators, and truth-discharge metadata; and
3. a local theorem-question identity containing the source anchor, exact local
   Core or Protocol endpoints, construction coordinates, relation and map
   slots, and their open obligations.

Changing only a local endpoint or construction coordinate rotates the third
identity but not the source theorem schema. Formation leaves `theorem_true`,
`applicable`, and `property_established` unset, including for rows whose local
Fiat--Shamir construction identity is already admitted.

Applicability then checks exact protocol correspondence and every side
condition. A local formula evaluator returns only such outcomes as
`ApplicableAtParameters`, `Inapplicable(reason)`, `VacuousBound`, or
`LimitExceeded`; it never returns `TheoremTrue` or `PropertyEstablished`.

## 6. Pressure variants

The following sources are design pressure, not additional claims for the
constructive case. They test whether the selected abstractions are genuinely
semantic rather than a transcription of binary multiplicative FRI.

| Variant | Source feature that must remain representable | Model pressure; no present claim |
|---|---|---|
| DEEP-FRI | A verifier sample outside the evaluation box, a prover-supplied evaluation, and a linked quotient function before the recursive proximity test. | Out-of-domain membership and its failure branch, quotient-oracle origin, and the changed proximity relation must be typed. No theorem for ordinary FRI may be reused by renaming the oracle. |
| STIR | Recursive rate improvement, changing domain/code parameters, and round-dependent query work. | Domain and rate schedules cannot be globally constant; resource formulas must depend on the exact round profile. This dossier does not claim STIR applicability. |
| Circle FRI | Circle-code function spaces and a first quotient by the circle involution, followed by a different projection chain; the first fold uses a different coordinate from later folds. | `multiplicative subgroup`, `x -> x^2`, and one universal fold law cannot be Core invariants. Algebraic domain and fold families need typed profiles. |
| BaseFold | Multilinear evaluation or inner-product claims, sumcheck polynomials, and FRI-like folds intertwined with shared verifier challenges. | One challenge may simultaneously parameterize multiple reductions. Claim state, fold state, and sumcheck state must compose without claiming that structural commutation proves correlated agreement. |
| WHIR | Constrained Reed--Solomon codes, sumcheck rounds, out-of-domain samples and answers, shifted logical queries, changing domains, and recursive weighted claims. | Relation and terminal schemas must evolve across recursion. Conjecture-dependent and proved theorem profiles must have different provenance and cannot share a truth capability. |

Primary variant sources:

- [*DEEP-FRI: Sampling Outside the Box Improves
  Soundness*](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2020.5);
- [*STIR: Reed--Solomon Proximity Testing with Fewer
  Queries*](https://eprint.iacr.org/2024/390.pdf);
- [*Circle STARKs*, Section 6 and Protocol
  1](https://eprint.iacr.org/2024/278.pdf);
- [*Basefold in the List Decoding Regime*, Sections 3 and
  5](https://eprint.iacr.org/2024/1571.pdf); and
- [*WHIR: Reed--Solomon Proximity Testing with Super-Fast
  Verification*](https://eprint.iacr.org/2024/1586.pdf).

Passing these pressures would show that the architecture admits the required
shapes. It would not show source fidelity, theorem applicability, or security
for any variant.

## 7. Constructive validation contract

The finite FRI package should exercise only structural premises that can be
observed exactly:

- initial and derived oracle origin, fixation, total domain, and causal order;
- ordered query occurrences, including repetition, separate from physical
  opening deduplication;
- cap, salt, path, and opening correspondence for one exact commitment
  profile;
- fold equations, terminal-degree rejection, and public-only target replay;
- complete statement, root, terminal, and grinding influence on the
  construction-internal query seed and resulting Core query vector;
- one concrete coupling of the work-augmented Fresh query vector and every
  one-shot Fiat--Shamir challenge result, without promoting that execution to
  general construction correctness; and
- distinct native, committed Fresh, and committed Fiat--Shamir subjects.

Its report must state `NotEvaluated` for proximity soundness, round-by-round
soundness, restoration soundness, ROM/QROM security, knowledge, binding,
hiding, and parameter security. Negative cases may establish that malformed
or inconsistent artifacts are rejected; they do not estimate an adversarial
success probability.

After the executable case and independent reconstruction pass, the durable
Analysis work should proceed in this order:

1. add exact native IOPP and vector round-by-round experiment profiles;
2. add restricted and unrestricted restoration profiles with typed branch
   budgets;
3. import one direct FRI theorem schema and source validation as a retained
   assumption;
4. add the exact BCS target experiment and loss transform for the selected
   commitment profile;
5. add grinding as a separate theorem transform with explicit placement and
   resource accounting; and
6. consider QROM and knowledge profiles only after their distinct capabilities
   and extractor relations have an identified consumer.

The architecture should be reopened if this requires placing adversary games
inside Protocol execution, treating logical and random-oracle queries as one
resource, erasing the source/target Core distinction, or coercing between the
property families above. Otherwise the required work is additive to the
selected semantic factorization.

## 8. Explicit nonclaims

This dossier does not claim that:

- the finite profile is cryptographically secure or theorem-representative;
- a passing verifier execution proves completeness, soundness, or proximity;
- SHA-256 is a random oracle, a Merkle test proves binding, or salts prove
  hiding;
- structural Fiat--Shamir admission implies ROM or QROM security;
- round-by-round soundness implies round-by-round knowledge;
- special soundness implies QROM knowledge soundness;
- physical query deduplication preserves a theorem's logical query count; or
- grinding contributes exactly its displayed bit count outside the theorem's
  exact placement, independence, and query-budget hypotheses.

Those are open Analysis obligations, not defects to conceal behind the
executable witness.
