# K3-C Minimum Analysis: Research and Selection

> **Document kind:** Temporary research and bounded-selection record
> **Document state:** Bounded K3-C selection, durable integration, and local
> validation complete
> **Provisional owner:** `project`, coordinating `analysis`, `pir`, and
> `relations`
> **Authority:** None. This page records the selected minimum profile and its
> rationale. Only exact durable owners may define target semantics.
> **Started:** 2026-08-27
> **Selection completed:** 2026-08-27
> **Disposition:** Retain through K3-E, then delete after its selected
> contracts, rationale, and deferrals have durable owners.

## 1. Bounded question

K3-C asks whether Analysis can consume the closed K1/K2/K3-B sources and state
two useful properties without reconstructing Protocol, accepting a supplied
trace as an adversary, hiding a quantitative loss, or conflating execution
replay with cryptographic rewinding.

The selected answer is deliberately small but has three non-collapsing edges:

1. a relation-bound two-transcript special-soundness property for a bounded
   native Schnorr Sigma subject;
2. an Attema--Fehr--Klooß (AFK) classical-ROM transport from an independently
   established all-parameter Fresh family property to the corresponding
   abstract Fiat--Shamir family property; and
3. a separately checked pointwise correspondence that may specialize the
   family result at one representable native member.

This is not a complete Analysis catalog. It is the minimum end-to-end cone
needed to test the source, experiment, applicability, and quantitative
boundaries before K1/K2 can be frozen.

## 2. Research conclusions

| Pressure | Selection | Limit retained |
|---|---|---|
| K2 causal execution | A finite native profile imports exact K2 `StrategyStep`/`ProverView` constraints. An asymptotic family uses a distinct Analysis mathematical strategy schema and can meet K2 only through an exact pointwise process correspondence. Generated runs are experiment outputs. | A caller-supplied `RunRecord` is never adversary semantics or evidence of non-anticipation; a finite K2 subject is never an all-`n` family. |
| K2 replay | `ReplayRun` proves only deterministic transition agreement. | It proves neither causal generation nor a cryptographic fork, rewind, or restoration. |
| K3-B Relations | Analysis imports exact relation, Statement, claim, witness-role, occurrence, and correspondence sources through owner-qualified results. | It cannot restate satisfaction, author an occurrence, or derive a universal property from one run. |
| [AFK, *Fiat-Shamir Transformation of Multi-Round Interactive Proofs*](https://eprint.iacr.org/2021/1377.pdf) | Select the February 16, 2022 version-2 classical-ROM adaptive knowledge-soundness result, specialized to a three-move, 2-out-of-`N` special-sound Sigma protocol. The exact source coordinates are Definition 4, Definition 10, Definition 11, Lemma 4, the adaptive construction in Section 6.3 immediately preceding Theorem 4, Remark 2 for deterministic next-message access and rewinding, Remark 6 for oracle-table consistency across reruns, and Theorem 4. | The result does not establish QROM security, zero knowledge, round-by-round soundness, signature security, or applicability to a different oracle/query/sampler model. |
| [Round-by-round and state-restoration soundness](https://eprint.iacr.org/2019/1261.pdf) | Keep cryptographic restoration as an Analysis-owned counterfactual experiment. | No universal restoration algebra is selected, and K2 replay cannot fill this role. |
| [RFC 8235](https://www.rfc-editor.org/rfc/rfc8235.html) | Use only as a Schnorr syntax and implementation cross-check. | It is not theorem authority for the selected property or FS transport. |

The AFK journal version is independently identifiable as
[Journal of Cryptology 36, article 36 (2023)](https://link.springer.com/article/10.1007/s00145-023-09478-y).
The selected theorem statement is version-bound to that ePrint revision. The
journal version requires a distinct locator set and statement digest; a later
paper revision or a different theorem with a similar name is a different
applicability source.

## 3. Selected dependency order

```text
finite K2/K3-B subject S
  -> finite manifest and experiment
  -> conditional relation-bound Schnorr special-soundness judgment

finite authenticated description of abstract family F
  -> family role and experiment schemas
  + independently established uniform all-n Fresh source judgment
  + exact AFK applicability judgment
  + retained theorem-truth premise
  -> conditional abstract-family FS knowledge-soundness judgment

abstract-family target judgment
  + exact FamilyInstanceCorrespondence(F,n0,S,ell0)
  -> conditional finite-member target judgment
```

Construction, theorem applicability, and property transport are three
different judgments. `CheckedFSConstruction` establishes only the structural
same-Core Fresh/FS pair. It establishes neither the Fresh source property nor
the AFK theorem or its applicability. The native special-soundness judgment is
also not the AFK family source judgment: its finite quantifier domain cannot
fill `forall n : LogicalNat`.

## 4. Two typed source-ingress variants

The finite native profile owns one `AnalysisSemanticReadManifest` under one
experiment-independent concrete `AnalysisSourceProfile`. A semantic slot
fixes:

```text
AnalysisSemanticReadSlot = {
  source_owner,
  source_kind_and_exact_semantic_coordinate,
  read_purpose: SemanticMeaning | PremiseSupport | OccurrenceEvidence,
  exact field projection,
  adequacy_requirement,
  source_binding_schema and required authority class,
  qualified_failure_disposition
}
```

The semantic manifest contains no concrete checked-result binding or live
capability. An `AnalysisSourceSupport` separately binds each slot to its exact
owner-issued source result; matching fresh capability is invocation-only. This
split prevents result origin and local authority from changing question meaning
while preserving exact use-time validation. The manifest does not copy source
facts into an Analysis-owned Protocol or Relations aggregate. Missing, extra,
duplicate, wrong-purpose, wrong-subject, stale, or locally authored sources do
not form the requested profile or support.

The asymptotic profile instead owns one finite authenticated family definition
and dependent `AnalysisFamilyReadManifestSchema`. Its abstract role slots are
derived from one denoted member at a logical index; they contain no K2 owner
coordinate or live authority. Family denotation, projection coherence, and
all-`n` laws remain ordinary propositions. The concrete and abstract slot
variants cannot be mixed in one source profile.

The finite native manifests select only the sources they use:

- K2 `PublicBindingView`, `StrategyDecisionView`, `PublicCoinView`,
  `EffectView`, `ClaimReductionView`, and `ExecutionView`;
- for the FS profile, K2 `TranscriptDeclarationView`,
  `RequiredInfluenceView`, `ChallengeTransitionView`, and
  `FSConstructionView`;
- admitted K3-B `ProtocolRelationBinding` and `PlanWitnessBinding`, exact
  correspondence question/ref schemas for Statement, claim, and Witness, and
  separately bound affirmative `CheckedCorrespondence` support results;
- exact K2 check and terminal coordinates plus an explicit universal Analysis
  acceptance-correspondence proposition; and
- `RelationRunView`, `CheckedRelationSatisfaction`, or a causal run capability
  only for a proposition that actually concerns one concrete occurrence.

The universal profiles selected here do not accept a concrete run as a
substitute for a strategy or relation theorem. Process-local capabilities are
support inputs, not semantic facts that survive serialization or Analysis
cold replay.

All identified Analysis bodies in this cone use K1
`SemanticContentId<K>(B, body)` under the same authenticated prior-meta basis.
K3-C introduces no independent `AnalysisSemanticRegimeId`, no second
question/goal/proposition identity formula, and no concrete support
proposition inside a hypothesis-free goal.

## 5. Profile A: relation-bound Schnorr special soundness

The selected relation is over a prime-order group with generator `g`:

```text
R(Y, x) := Y = g^x
Verify(Y, A, c, z) := g^z = A * Y^c
```

The Statement is `Y`, the relation witness is `x`, the first prover message is
the commitment `A`, and `c` and `z` are the challenge and response at their
exact K2 occurrences. K3-B correspondence must bind those roles to this exact
relation instance and claim.

The property quantifies over two accepting transcripts with the same `(Y,A)`
and distinct challenges `c != c'`. Its deterministic extractor is:

```text
x = (z - z') / (c - c') mod q.
```

This is a deterministic two-transcript hyperproperty, not a
successful-one-run bad event, probability-bound result, or discrete-log
hardness claim. Perfect completeness is a separate universal algebraic
property of the honest response; it is not Profile A and is not theorem
authority for Profile B.

The counterfactual two-transcript experiment is Analysis-owned. It may use a
profile-specific fork/restoration law, but it never consumes `ReplayRun` as a
rewinding capability and never mints K2 causal provenance.

## 6. Profile B: AFK adaptive Fresh-to-FS transport

The selected theorem profile is classical ROM and is specialized to the exact
schema of a three-move Schnorr family, not to the one finite Profile-A subject.
It is not a generic rule for transporting an arbitrary Fresh soundness or
knowledge property. Its exact edge is uniform asymptotic deterministic
`k`-out-of-one-fixed-`N` special soundness of the public-coin Fresh family to adaptive
knowledge soundness of its adaptive FS family transform. Those are distinct
tagged property families; no same-family cast is involved.
Its exact premise coordinates are:

- one authenticated finite mathematical-family description with total,
  single-valued, coherent member denotation;
- an independently established affirmative all-`n` source judgment with one
  uniform 2-special-sound extractor family over the exact family relation;
- one theorem-local finite challenge cardinality `N >= 2`, with an explicit
  all-`n` premise that every member challenge set `C_F(n)` has exactly that
  cardinality;
- an adaptive classical prover making at most `Q` random-oracle queries;
- a finite oracle-index carrier exactly represented by bitstrings of length at
  most an authenticated bound `u(n)`, with decidable equality, an injective
  prefix-free encoder, finite lazy-table semantics, and efficient
  encode/equality/lookup/sample operations;
- a random oracle returning exact uniform values in `C_F(n)`;
- the paper's exact one-round query index `(statement, commitment)`, with the
  Statement included rather than supplied only as ambient context, plus a
  checked map to zkc's exact domain/framing encoding;
- the theorem's requirement that extractor output preserve the distribution
  of `(statement, proof, auxiliary_output, verifier_output)` while adding the
  witness;
- theorem-granted lazy sampling and reprogramming; and
- exact abstract relation, Statement, commitment, challenge, response, setup,
  Fresh/FS experiment, outcome, and resource maps. K2/K3-B coordinates enter
  only a separate pointwise family/member correspondence.

K3-C deliberately defines no native semantic basis that proves the all-`n`
source proposition. The selected family language describes roles and
relations, but it has no authenticated family algebra/program language from
which a uniform source extractor proof could be derived. Until an independent
proof authority supplies that exact capability, property transport returns
`CannotAnswer`; the finite Schnorr fixture cannot manufacture it.

Its native Definition 10 order is `exists q_KS; exists one uniform black-box
extractor E; for all statement lengths n, hard query bounds Q, and adaptive
Q-query provers P^a`. The prover is not required to be polynomial time. `E`
takes only `n` and black-box access to `P^a`; it cannot take `Q`, the success
probability, prover code, or the hidden oracle table as advice. Its expected
running time is polynomial in `n` and the actual `Q`, counting one black-box
prover invocation as one step. `P^a` takes no external input and produces
`(statement, proof, aux)`; `aux` is an arbitrary output, not a sampled auxiliary
input. The prover and extractor experiments occupy separate probability spaces
whose `(statement, proof, aux, verifier_output)` laws must be identical.

The selected target is explicitly the `0 <= Q < N` restricted-query
subprofile, so that `kappa_FS` remains in `[0,1]` without a hidden cap. It is a
valid restriction of the AFK theorem but is not the full all-`Q` Definition 10
property; later support for the latter must select an exact capped error law or
a broader quantitative sort.

The absence of a prover time bound is not a partial-algorithm extension of the
paper. The selected prover ABI returns one typed `(statement, proof, aux)` on
every admitted invocation; a diverging or missing-output module is outside the
quantified class. Its returning computation may nevertheless take unbounded
time in the unit-cost black-box model used for the extractor.

For the selected pointwise family/member correspondence, `statement` is the
raw relation Statement `Y`. Group parameters, session/application domain,
Core/construction headers, scope/framing rules, challenge-condition schema,
and namespace form fixed public setup chosen before and independently of the
prover and oracle. The required pointwise map is an injective value-level
encoder from `(Y,A)` to the exact K2 derived prefix plus challenge namespace,
including the repeated typed `Y` challenge-condition frame. It also equates
the complete native adaptive oracle interaction with the corresponding family
lazy-random-function interaction:
same-index repeats over the exact finite bounded-bitstring carrier, joint
independent-uniform values at distinct adaptively chosen indices, exact query
counting, and theorem-authorized rerun/programming
behavior must all agree. A coordinate list or pointwise uniform marginals are
insufficient. An adversary-selected or oracle-correlated session refuses this
profile; an extended-Statement/lifted-relation treatment would be a different
future profile.

The finite pointwise pressure fixture uses a power-of-two challenge set
embedded in the scalar field and an exact one-draw total uniform decoder. K2's
general bounded-rejection path and `SamplingExhausted` outcome do not match
AFK's total uniform oracle by construction and therefore remain outside this
pointwise candidate.
A fixed SHA-256 execution can test transcript structure; it is not ROM
evidence.

The fixed-`N` and finite-index premises are intentionally narrower than a
desirable generic family theorem. The selected AFK source fixes `N` for one
protocol and models the oracle over `{0,1}^{<=u}`. A family with varying
`N_F(n)`, an unbounded canonical-byte index, or a different oracle
representation therefore needs a separately identified uniformization or
generalization theorem; K3-C does not silently attribute that extension to
AFK.

The literature is primary theorem support, but zkc currently imports no
machine-checked proof or certificate for it. Structural applicability excludes
theorem truth: it answers only whether the exact theorem statement matches the
selected schemas. Every transported proposition separately retains the exact
`TheoremTruthGoal(AFK...)` as established or `Assumed` in its canonical
hypothesis context. A citation, theorem catalog entry, or formal-receipt shape
cannot turn theorem truth or the target property into an unconditional
conclusion.

## 7. Exact quantitative selection

K3-C needs only a closed, typed symbolic-rational fragment sufficient for the
AFK specialization. It preserves parameters, arithmetic, side conditions,
and source-property IDs exactly; unsupported operators do not elaborate
through an arbitrary callback. Property bounds use basis-neutral quantitative
formula IDs. The theorem schema owns the instruction that maps the exact source
terms to one of those formulas, not the formula identity itself. This keeps an
ordinary target property stable across proof bases and prevents a theorem-
schema/target-property identity cycle.

For `k`-out-of-`N` special soundness, the selected transform records:

```text
theorem extraction-error term: Er(k;N) = (k - 1) / N
target FS knowledge error:     kappa_FS(n,Q,N) = (Q + 1) * Er(k;N),
                               definitionally independent of n
expected calls to A:           k + Q * (k - 1)
native Definition 10 success threshold:
  (epsilon - kappa_FS(n,Q,N)) / q_KS(n)
Lemma 4 transcript-extraction lower bound:
  N / (N - k + 1) * (epsilon - (Q + 1) * (k - 1) / N)
```

For Schnorr, `k = 2`, so the target error is `(Q + 1) / N` and the expected
number of calls to the adversary-running algorithm `A` is `Q + 2`. This exact
instance selects `q_KS(n) = 1`: Lemma 4 gives a factor `N/(N-1)` stronger than
`epsilon - kappa_FS` when that difference is nonnegative, and probability
nonnegativity handles the negative case; the adaptive construction before
Theorem 4 preserves the required output law. The abstract family target
therefore states
successful relation-witness extraction of at least
`epsilon - (Q + 1)/N`. The stronger Lemma 4 bound remains a separate theorem
output. Domain and denominator conditions and the selected nontrivial-bound
condition `Q < N` are explicit propositions. Signed lower bounds are not
silently clamped to `[0,1]`; vacuous bounds remain visibly vacuous rather than
becoming stronger claims.

AFK does not justify appending an arbitrary relation-projection or collision
term. The initial lane therefore accepts only identity/equivalence, or an
exact relation map recognized by the selected theorem. A K3-B priced-lossy
bridge remains conditional until a separate exact bridge theorem supplies its
premise, occurrence map, consumer-source joins, use count, and quantitative
transform. Generic Analysis may not synthesize a formula such as
`AFK loss + m * Adv_collision`.

## 8. Replay and authority separation

The selected profiles keep three relations disjoint:

1. K2 `ReplayRun`: deterministic transition agreement only;
2. AFK or special-soundness forking/restoration: a theorem/profile-specific
   Analysis experiment; and
3. Analysis cold replay: dependency authentication and checker/derivation
   reconstruction.

None recreates another's capability. In particular, cold replay and K2 replay
cannot recreate causal generation, confidential occurrence authority, or
theorem truth.

The K3-C executable package is a finite formation and refusal instrument. Its
lazy-random-function helper checks a supplied realized lookup trace, exact
repeat consistency, typed resource identities, and selected boundary
mutations. It does not execute an online adaptive strategy, prove that native
K2 steps realize the abstract family process, establish the joint distribution
law across the two AFK probability spaces, or prove theorem-authorized
programming/rerun semantics. Those remain exact hypotheses or separately typed
contracts; the instrument must not be reported as adaptive-ROM evidence.

## 9. Exact deferrals

K3-C deliberately defers:

- QROM, malicious-verifier zero knowledge, multi-prover independence,
  signatures/EUF, and a general multi-round AFK catalog;
- a universal cryptographic restoration or property-composition algebra;
- BCS/IOR-to-Core correspondence and native FRI/IOR pressure to K4;
- general bounded-rejection-to-uniform-oracle correspondence;
- arbitrary lossy relation bridges and collision pricing without a separate
  theorem and exact K3-B consumer-source joins;
- concrete RNG/hash conformance and any claim that SHA-256 realizes a random
  oracle;
- imported machine-checked AFK proof authority;
- full Analysis persistence, broad property families, compiler consumption,
  OIR, realization, migration, and cutover.

These items are deferred because none is required to close the three selected
edges, while folding them into optional fields would hide material changes
in adversary class, theorem model, authority, or loss.

## 10. Reopen rule and exit boundary

The bounded K3-C selection reopens if primary-source rechecking changes an
AFK premise or formula, the finite instrument cannot form the exact selected
questions or enforce `CannotAnswer` for the absent family-source capability, a
same-boundary mutation is accepted, the pointwise query/transcript map cannot
be formed from K2 views, or an unpriced bridge is required for the claimed
target relation.

K2 does **not** reopen for a new theorem, adversary class, loss expression,
relation map, or Analysis experiment. It reopens only if a concrete selected
case requires a verifier-observable or identity-bearing Core fact that cannot
be derived faithfully from current owner views. A reopen request must name:

1. the exact protocol or theorem case;
2. the missing observable;
3. why a source-owned derived view is inadequate;
4. the identity, admission, execution, and FS consequences;
5. a positive inhabitant and a same-boundary negative; and
6. the rejected smaller downstream alternative.

No selected K3-C case currently meets that rule. The missing work is
downstream Analysis definition and validation, not a defect in the K2 Core.

The exact durable source manifests, strategy/experiment bodies,
question/goal/proposition identities, theorem-applicability judgment, typed
transform, qualified outcomes, and finite positive/negative instrument now
agree at the selected bounded scope. The companion
[validation record](k3-c-validation.md) closes local K3-C validation and records
the completed adversarial-review rounds, final gates, and the absence of an
independent final-`PASS` artifact after peer-service timeouts. This closure
still establishes no cryptographic security, theorem truth, implementation
conformance, or protocol-family completeness.
