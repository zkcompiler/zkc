# P01 Schnorr/Sigma: Fresh and Fiat--Shamir Witness

> **Kind:** Temporary R2 T3 witness design and current-model obstruction record
> **State:** Source reconstruction complete; finite executable design selected,
> with report closure still pending
> **Authority:** None. This page can falsify or motivate a model; it does not
> define Protocol semantics, establish a theorem, or claim implementation
> support.
> **Classification:** Current target: `FundamentalObstruction`. Candidate C:
> provisionally `Native` only relative to the repaired model, pending the T3
> closure gate.
> **Research boundary:** Public primary and authoritative sources only. No
> material under `docs/private/` was consulted or copied.
> **Disposition:** Retain through R2--R4, absorb accepted results into their
> durable owners, then delete this page.

## 1. Decision in brief

The current target can encode the algebraic messages, Fresh challenge, verifier
equation, and terminal of minimal Schnorr. It cannot encode the complete source
model:

1. the Fiat--Shamir construction has no Core-preserving path by which a
   `Statement` input must influence the first challenge; and
2. `ExecuteProtocol` consumes a completed `ProverTrace`, not a causal prover
   strategy, so a commitment chosen with knowledge of the later challenge is
   indistinguishable from a generated trace.

These are shared Core/execution-boundary defects, not missing Schnorr-specific
syntax. The selected finite repair candidate is
`ChallengeNeutralConversationCore + ChallengeRealization = ProtocolVariant`.
The Core retains the challenge occurrence, domain, order, visibility, and
logical-failure contract, but no Fresh sampler. A Fresh realization supplies
public-coin resolution, distribution, and disclosure; an FS realization
supplies the exact transcript program. The FS program derives its required
influences from semantic roles and occurrences. Honest witness and nonce inputs
belong to a strategy/local execution binding, not to the participant-neutral
Core. This `MCR-P01` refinement and strategy-generated execution remain
provisional rather than ratified by this note.

## 2. Source ledger and exact use

| Source | Exact use in P01 |
|---|---|
| [Schnorr, *Efficient Identification and Signatures for Smart Cards*, CRYPTO '89](https://doi.org/10.1007/0-387-34805-0_22) | Historical identification/signature construction. |
| [Fiat and Shamir, *How To Prove Yourself*, CRYPTO '86](https://doi.org/10.1007/3-540-47721-7_12) | Historical removal of the verifier challenge through hashing; not a complete modern generic theorem. |
| [Damgård, *On Sigma Protocols*](https://cs.au.dk/~ivan/Sigma.pdf), Sections 1--3 | Minimal Schnorr equations, perfect special soundness, perfect special HVZK, and the `2^-t` knowledge-error theorem. |
| [Bellare--Palacio, CRYPTO 2002](https://www.iacr.org/archive/crypto2002/24420162/24420162.pdf), Figure 1 and Section 3; Figure 4 and Section 5 | Stateful two-activation prover schedule, reset boundary, canonical Schnorr identification, and the separate active/concurrent impersonation theorem. |
| [Abdalla--An--Bellare--Namprempre, EUROCRYPT 2002](https://www.iacr.org/archive/eurocrypt2002/23320414/main.pdf), Construction 1 and Theorems 1--2 | Canonical identification-to-signature FS syntax and the separate ROM/signature-security and commitment-entropy obligations. |
| [Pointcheval--Stern, J. Cryptology 2000](https://doi.org/10.1007/s001450010003), Theorem 3 | Classical forking extraction boundary for FS signatures. |
| [Unruh, *Post-Quantum Security of Fiat-Shamir*](https://eprint.iacr.org/2017/398.pdf), introduction and Definition 17 | Statement-bound `H(instance || commitment)` form and the separate QROM theorem boundary. |
| [CFRG Sigma draft v03](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-sigma-protocols-03), Sections 3--5 and 7 | Current concrete linear-relation interface, single-use prover state, instance validation/serialization, full-field challenge, simulator, and DSFS use. |
| [CFRG Fiat--Shamir draft v03](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-fiat-shamir-03), Sections 3--6 and 8 | Public-coin prerequisite, session separation, mandatory instance-first absorption, prefix-free codecs, duplex absorb/squeeze flow, decoding bias, and theorem prerequisites. |

Both CFRG documents are Internet-Drafts published 17 August 2026. They are
authoritative external design pressure and source comparisons for P01, but
remain work in progress and have no authority over zkc's model. Their vectors
are not reused as the finite executable's vectors.

## 3. Source anatomy and selected finite specialization

The source protocol is the one-equation Schnorr relation in a prime-order
group. In multiplicative notation it is

```text
R_DL(Y, x) iff x in Z_q and Y = g^x

Commit(Y, x; r):  r <- uniform Z_q; A := g^r
Challenge:         c <- uniform C, only after A
Respond:           z := r + c*x mod q
Verify:            accept iff g^z = A * Y^c
```

The selected executable is deliberately finite: `p = 23`, `q = 11`,
`G = <g = 2> <= Z_23*`, and `C = {0,...,7}` embedded into `Z_11`. Group
elements and scalars use their checked fixed-width encodings (one byte in this
profile). The frozen positive assignment is `x=7`, `Y=13`, `r=4`, `A=16`;
Fresh uses `c=3`, `z=3`. The group/profile, generator, relation convention, and
codec names are semantic inputs even though the runtime Statement occurrence
contains `Y`.

For this exact profile, completeness is algebraic equality. Two accepting
transcripts with the same `A` and distinct `c,c' in C` extract

```text
x = (z - z') * (c - c')^-1 mod 11.
```

The inverse always exists because distinct members of `C` remain distinct in
the prime field `Z_11`. For prescribed `c`, the special-HVZK simulator samples
uniform `z in Z_11` and sets `A := g^z * Y^(-c) mod 23`. These finite facts are
exhaustively checkable, but they do not themselves promote Damgård's general
special-soundness, SHVZK, or knowledge-error results.

An adversarial interactive prover is an arbitrary stateful probabilistic
strategy with the same activation order. Its commitment decision sees only its
visible past, private input/advice, private state/randomness, and permitted
prior oracle responses. Its response decision additionally sees `c`. If `c`
is exposed before `A`, a prover without `x` can choose `c,z` and set
`A := g^z * Y^(-c)`; the equation then accepts by construction. A completed
accepting trace is therefore not evidence of causal generation.

### Fiat--Shamir delta in the executable

The executable deliberately uses a small, exact construction rather than the
CFRG v03 DSFS suite. Its framing operation is

```text
Frame(label, payload) =
  u16be(len(label)) || ASCII(label) || u32be(len(payload)) || payload
```

It first derives a 32-byte session identifier from the exact initialization

```text
session_preimage =
    Frame("algebra-profile-id", ASCII(AlgebraProfileId))
 || Frame("core-id", ASCII(CoreId))
 || Frame("transcript-construction-id", ASCII(TranscriptConstructionId))
 || Frame("application-domain", UTF8("zkc/p01/minimal-schnorr/v1"))
 || Frame("challenge-namespace",
          ASCII("zkc/p01/schnorr/challenge/c/v1"))

session_id = SHAKE128(
    Frame("zkc/p01/fs/session/v1", session_preimage), 32 bytes)
```

The challenge query then is

```text
Frame("session-id", session_id)
|| Frame("InitialStatement:statement:y:fixed-width-group-element.v1",
         EncodeGroup(Y))
|| Frame("PriorProofMessage:message:commitment:fixed-width-group-element.v1",
         EncodeGroup(A))
|| Frame("derive", challenge_namespace)

c = IntegerBE(SHAKE128(query, 1 byte)) & 0x07
```

Thus the exact runtime influence order is application/suite domain,
Statement, then commitment, and the sampler codomain is precisely `C`. For the
frozen assignment it gives `c=4`, `z=10`. The verifier rebuilds the identical
query and applies the same Schnorr equation.

This is **not** a CFRG DSFS/P-256 conformance vector: it does not use
`SerializeLinearRelation`, the CFRG duplex suite, full-field challenges,
`DecodeField`, wide reduction, or the CFRG proof container. It makes no claim
about full-field sampling or decode bias. CFRG v03 remains authoritative design
pressure for statement-first absorption, public-coin eligibility, injective
framing, single-use state, and theorem boundaries.

FS changes the challenge realization and adversary interface, not the Core
conversation, relation, or response/check equation. The FS prover may make
adaptive oracle queries and try multiple commitments. Interactive fresh-coin
non-anticipation is therefore not copied verbatim: an FS strategy must form a
query before seeing that query's answer, while Analysis quantifies over the
full adaptive oracle-querying strategy.

## 4. Current-target correspondence and obstruction

| Source item | Current target location | Result |
|---|---|---|
| Prover, Verifier, public environment | [`protocol-model.md` Section 3.3](../../../pir/protocol-model.md#33-roles-knowledge-and-ports) | Native for this two-party public-coin case. |
| Instance `I` and witness `x` | Public `Statement` and private Prover `Witness` input occurrences | Structurally representable. |
| Nonce `r` | `PrivateProverSample` attached to the commitment prover obligation | Structurally representable; distribution realization remains a separate obligation. |
| Commitment `A` and response `z` | Two Prover-to-Verifier `Proof` messages with prover obligations | Values, ordering, and domains are representable. |
| Challenge slot and Fresh `c` | `FreshChallenge`, PublicEnvironment randomness, and challenge value | The occurrence/domain/order/failure are representable, but the current Core is Fresh-specific; the repaired finite candidate moves resolver/distribution/disclosure into a `FreshRealization` over `C={0,...,7}`. |
| Equation and result | `InvokeCheck`, check-false rejection, and accepting terminal | Structurally representable; this is not relation satisfaction or a theorem. |
| `I` before `A` in every FS prefix | [`fiat-shamir-and-composition.md` Section 3](../../../pir/fiat-shamir-and-composition.md#3-transcript-construction) | **Blocked.** Initialization accepts only public `Context` ports; `Statement` has no path. |
| Required inclusion of `A` | Message `Transcript` bit and event-action map | **Unsound authority split.** A Wire-only `A` can be omitted by author choice instead of being rejected from its semantic proof/round role. |
| Commitment-before-challenge strategy | [`ProverTrace` and `ExecuteProtocol`](../../../pir/protocol-model.md#311-invocation-grammar-and-execution) | **Blocked.** The completed trace is supplied wholesale; no strategy-to-trace generation relation exists. |
| Public-coin FS eligibility | `ProtocolAdmissible` | P01's exact Core is public coin, but the reusable admission rule does not exclude every verifier-private influence on a prover-visible verifier move. |
| DL relation correspondence | [`RelationBinding`](../../../relations/relation-model.md#6-protocol-to-relation-binding) | Public/witness occurrence bridges are expressible; relation satisfaction, protocol acceptance, and either implication between them remain separate judgments. |
| Special soundness, HVZK, FS security | [`cryptographic-properties.md`](../../../analysis/cryptographic-properties.md) | Analysis-owned applicability only; no property follows from structural admission or finite replay. |

Encoding `I` as `Context`, synthesizing a dummy statement message, or handing
the evaluator a precomputed transcript are modeling workarounds. They change
semantic purpose, alter the source interaction, or move authority into the
evaluator and therefore do not count as P01 support.

## 5. Repair alternatives

| Candidate | Repair | Benefit | Failure or cost | Decision |
|---|---|---|---|---|
| A: statement-as-event | Widen `ObservePublicValue` to permit `Transcript` and insert an initial observation of every statement value. | Small local change; current event-action machinery can absorb the value. | Invents an interaction event absent from Schnorr Fresh, makes required binding an authored observation choice, and does not repair strategies. | Reject. |
| B: FS-only statement initialization | Extend `TranscriptConstruction` with a total Statement map beside its Context map. | Preserves the visible Fresh event schedule and can encode `instance` before `A`. | Splits influence authority between initialization and events, retains the authored message bit, and scales poorly to scoped/dynamically introduced statements. | Viable narrow patch, not selected. |
| C: challenge-neutral Core plus derived influence | Factor `ProtocolVariant` into a `ChallengeNeutralConversationCore` and exactly one `ChallengeRealization`; derive the FS influence view from Statement purpose, proof/round contracts, prior challenges, and Core order. | Preserves one conversation, prevents omission by authored bits, keeps Statement distinct from Context, and assigns Fresh and FS mechanics to the correct realization without claiming Fresh coins depend on transcript values. | Requires a Core/admission refactor and a precise scope/profile law; later protocols must test dynamic statements and explicit relaxations. | **Selected provisional candidate.** |

A separate-Fresh/FS-Core construction remains a legitimate fallback when a
transform really changes interaction structure. It is unnecessary for minimal
Schnorr and would duplicate the same commitment/challenge/response skeleton.

Candidate C keeps challenge shape in the conversation while moving challenge
resolution out of it:

```text
ChallengeNeutralConversationCore
  + exactly one ChallengeRealization
  = ProtocolVariant
```

The Core owns the occurrence, domain, order, visibility, and logical-failure
contract. `FreshRealization` owns public-coin resolver, distribution, and
disclosure. `FiatShamirRealization` owns the transcript construction and
sampler. The latter consumes a challenge-neutral derived view:

```text
DerivedInfluenceOccurrence =
    InitialStatementOccurrence(PortOccurrenceRef)
  | PriorEventInputOccurrence(EventRef, input_ordinal)
  | PriorChallengeOccurrence(ChallengeRef)

RequiredInfluence(Core, challenge, admitted profile)
  -> canonical ordered sequence of DerivedInfluenceOccurrence
```

The sequence is recomputed, not independently authored or separately elevated
into semantic identity. Its authoritative inputs already belong to Core and
the admitted profile. For P01 it is exactly `[I, A]` before `c`.

- Fresh proves that `c` is sampled according to its realization-owned
  public-coin law and disclosed at the Core challenge boundary after `A`; the
  influence view does not become a sampling dependency.
- FS maps every required influence occurrence, exactly once and in order, to
  an injectively framed transcript atom before deriving `c`.
- Any relaxation is a named profile/theorem input with exact scope, rather than
  an omitted observation bit.

## 6. Authority, identity, strategy, and Relations

### Authority and identity

- `ChallengeNeutralConversationCore` owns the ordered interaction, port
  purposes, challenge occurrence/domain/order/failure, and checks. `CoreId`
  binds this shape but not runtime `Y`, `x`, `r`, or `c`, and not a Fresh or FS
  resolution mechanism.
- `ChallengeRealization` owns how the slot is resolved. Fresh owns its public
  resolver/distribution/disclosure; FS owns the framed SHAKE128 program and
  low-three-bit sampler. `ProtocolVariantId` binds one Core to exactly one
  realization.
- The invocation owns the concrete public Statement. Honest `x` and `r` belong
  to the strategy/local execution binding; placing either in the shared Core
  would confuse a protocol conversation with one honest implementation.
- The Fresh and FS `ProtocolVariantId` values remain distinct even when their
  `CoreId` is shared. Equality of Core IDs establishes no distributional or
  cryptographic equivalence.
- The application tag/context is semantic domain separation and must have an
  explicit construction and consumer. It is not provenance, evaluator, file,
  or replay identity.
- Derived influence is a checked view/cache. It receives no independent
  authoring authority and cannot create a second truth about the Core.

### Strategy and execution

Replace strategy-free semantic execution with a relation of the form:

```text
GenerateExecution(
  admitted Protocol,
  admitted strategy,
  invocation,
  actor randomness / Fresh coins / permitted oracle,
  bounds)
  -> generated execution record
```

At each Prover decision point the strategy receives only the authenticated
visible history and permitted private state. Execution emits the trace; it
does not accept a preauthored trace as evidence of generation. A separate
`ReplayTrace` operation may remain useful, but its result means replay
consistency only. Analysis, not PIR, owns PPT/adversarial strategy classes,
games, extractor access, and probabilities.

The honest Schnorr strategy and its local witness/nonce binding are separately
identified execution operands, not part of `CoreId` or
`ProtocolVariantId`. The same applies to a cheating strategy and to an FS
oracle strategy. The two-stage machine enforces one commitment activation per
generated execution. Detecting nonce reuse across independent invocations is a
separate, explicitly excluded service; acceptance does not make reuse safe.

### Relation boundary

P01 uses independently owned operands:

```text
Relation instance:  public X under R_DL
Relation witness:   private x
Protocol instance:  Statement occurrence containing I
Protocol-local secret: strategy/local execution binding containing x
```

The public and secret bridges are total typed identity/isomorphism bridges only
when both domains literally share the selected group/scalar contracts;
otherwise explicit bijections are required. A private nonce is neither a
relation witness nor a Core input. The verifier check references the equation,
while these remain separate results: structural binding, instance
correspondence, witness
satisfaction, Protocol acceptance, soundness direction, completeness
direction, and full behavioral equivalence.

## 7. Finite T3 witness design

The selected executable freezes an intentionally toy profile. It uses CFRG
v03 as comparative design pressure, not as its concrete suite or vector source.

| Subject | Frozen finite form |
|---|---|
| Algebra | `p=23`, `q=11`, `g=2`, `C={0,...,7}`; checked subgroup/scalar/challenge domains and fixed-width codecs. |
| Core | Initial public Statement `Y`; schedule `A, c, z, check, terminal`; challenge slot retains domain/order/visibility/failure but has no sampler, witness, or nonce. |
| Realizations | Fresh: PublicEnvironment, uniform `C`, disclosure at the challenge boundary. FS: the exact framed SHAKE128/low-three-bit program in Section 3. Both form distinct `ProtocolVariant`s over one `CoreId`. |
| Local strategy | Public request contains no `x` or `r`. A request-bound private local binding supplies them to a closed two-stage strategy through capability-checked reads; generation emits access receipts. |
| Positive support | `Y=13`, `x=7`, `r=4`, `A=16`; Fresh `c=3,z=3`; FS `c=4,z=10`; both equations accept. |
| Extraction | Enumerate all 11 witnesses, 11 nonces, and 28 unordered distinct challenge pairs: 968 accepting transcripts and 3,388 forks; each fork must extract and revalidate the unique enumerated witness. |
| Simulation | For each of 11 Statements and 8 fixed challenges, compare the exact 11-point honest and simulator distributions: 88 conditional distribution equalities. |
| Relations | Relation, instance, witness admission, satisfaction, execution-Statement grounding, transcript acceptance, and theorem applicability remain separate results. |
| Identities and bounds | Bind fixture, algebra, Core, realization, construction, strategy, local binding, request, execution, qualification, relation operands, evaluator-source digests, and report root; cap strategy steps, reads, atoms, hash queries, and replay. |

The executable layer checks closed finite algebra, exact generation and replay,
admission, identity, grounding shape, and mutations. Exhaustive special-
soundness and special-HVZK checks establish equalities only in this finite
model; they are not experiments and are not general cryptographic theorems.

### Frozen positive and negative matrix

These are report expectations, not passing claims until the closure replay is
frozen and reproduced.

| ID | Witness or mutation | Current target | Repaired finite candidate expectation |
|---|---|---|---|
| `P01-SEM-OK` | Admit Core, both realizations, and their factorization | Fresh-shaped Core only | `P01-CORE-OK`, `P01-FS-OK`, two `P01-PROTO-OK`, and `P01-FACT-OK`. |
| `P01-F-OK` | Honest Fresh support point | Supplied trace can be replayed | Strategy-generated `Accept` with `c=3,z=3`, then exact requalification. |
| `P01-FS-OK` | Exact finite statement-bound FS support point | Source-faithful construction blocked | Exactly two ordered transcript reads `[Y,A]`, `c=4,z=10`, `Accept`, then exact requalification. |
| `P01-EXT` | Every equal-`A`, distinct-challenge accepting fork | Pointwise algebra can be run | 968 accepts and all 3,388 forks extract the enumerated `x`; `P01-SS-ENUM-OK`. |
| `P01-SIM` | Every Statement and prescribed challenge | Pointwise algebra can be run | 88 exact real/simulator distribution equalities; `P01-SHVZK-OK`. |
| `P01-N-STMT-OMIT` / `-COMMIT-OMIT` | Remove either required FS source | Can be author-omitted | First failure `P01-FS-005`; authors cannot opt either source out. |
| `P01-N-PREFIX` | Reorder, duplicate, mis-type, or mis-codec an atom; alter initialization/framing/namespace/codomain | Partial authored checks | Exact non-admission at `P01-FS-004/006/007/008/011/012/014` as applicable. |
| `P01-N-CLAIRVOYANT` | Commitment strategy reads future `c` | Completed trace may accept | Capability read is refused at `P01-EXEC-CAUSALITY` before a record exists. |
| `P01-N-PRIVATE-V` | Verifier-private state affects the public-coin interaction | Reusable eligibility gap | Fresh or FS non-admission at `P01-PROTO-008` or `P01-FS-015`. |
| `P01-N-ORDER` | Challenge before commitment, or response reads a future challenge | Mixed structural checks | Generic conversation admission is distinguished from Schnorr correspondence (`P01-CORR-001`); an actual future read fails `P01-CORE-009`. |
| `P01-N-RESPONSE` | Closed strategy emits `z+1 mod q` | Equation can reject | Generated `Reject` with an exact false-check terminal; direct transcript check yields `P01-TRN-008`. |
| `P01-N-BIND/REPLAY` | Wrong request-local secret binding or mutated record | Trace carries excessive authority | Binding admission or exact-replay qualification fails; a supplied record cannot mint generation evidence. |
| `P01-N-STATEMENT/TAG` | Change Statement or application domain | No mandatory FS influence | A Statement change alters its framed atom and query but not reusable construction identity; an application-domain change alters construction/variant identity and the query. Because `C` has only eight values, challenge inequality is **not** required and collisions are not admission failures. |
| `P01-N-THEOREM` | Promote finite facts to general SS/SHVZK/HVZK/PoK/ROM/QROM | Analysis must reject | Explicit refusals `P01-APP-101` through `P01-APP-106`. |

The two decisive current-target failures are `P01-N-STMT-OMIT` and
`P01-N-CLAIRVOYANT`. Green algebraic replay cannot override either failure.

## 8. Theorem boundary and non-claims

PIR may expose the transcript, causal strategy execution, relations, and exact
assumption-bearing inputs needed by Analysis. It does not mint these results:

- perfect completeness follows from the Schnorr equation;
- special soundness requires two accepting transcripts with the same
  commitment and distinct challenges;
- special HVZK is only honest-verifier zero knowledge;
- an interactive proof-of-knowledge claim needs an extractor definition and
  knowledge-error accounting;
- active/concurrent identification security is a separate Bellare--Palacio
  theorem under the one-more discrete-logarithm assumption;
- classical FS extraction uses a separate ROM theorem such as forking, with
  query-dependent loss;
- Abdalla et al.'s signature result additionally concerns passive
  identification security and commitment nontriviality/entropy; and
- QROM/post-quantum FS requires a separate theorem and assumptions. A classical
  ROM result does not transport automatically.

The CFRG FS v03 claims preservation from state-restoration soundness and HVZK
under an extraction- and simulation-friendly random-oracle instantiation, with
query-dependent losses. P01 records those as candidate Analysis premises, not
as facts established by citing the draft.

P01 makes no claim of malicious-verifier ZK, active/concurrent/reset security,
EUF-CMA signatures, ROM realization by a concrete hash, QROM security,
simulation soundness, composability, implementation conformance, constant-time
behavior, discrete-log hardness, general Sigma support, or Fresh/FS
distributional equivalence. Reusing a nonce across distinct challenges reveals
the witness; it is not an accepted honest-strategy behavior.

The executable's exact exclusions are stronger: it is not a CFRG DSFS or
P-256 conformance vector; does not implement a full-field challenge,
`DecodeField`, or wide-reduction analysis; makes no decode-bias or security-bit
claim; and cannot support a hardness claim because discrete logarithms in the
11-element toy group are trivial. Calling its domain-separated, typed `[Y,A]`
query "strong FS" means only that the required influences are present and
checked.
It does not assert any ROM/QROM transform theorem. Exhaustive finite special-
soundness and SHVZK equalities do not generalize beyond the frozen domain, and
the local two-stage strategy machine is not a universal adversary language or
a cross-invocation nonce-reuse service.

## 9. Model-change request

`MCR-P01` is one provisional fundamental refinement with four inseparable
parts:

1. replace the Fresh-specific `InteractiveCore` with a
   `ChallengeNeutralConversationCore` that retains challenge occurrence,
   domain, order, visibility, logical failure, and causal dependencies, but no
   resolver or sampling mechanism;
2. define `ProtocolVariant = Core + exactly one ChallengeRealization`, with
   Fresh owning public-coin resolver/distribution/disclosure and FS owning its
   transcript construction and sampler;
3. replace authored transcript-observation bits as FS authority with the
   derived influence view, and require complete Statement influence, required
   proof-message influence, exact prefix/order/codec coverage, and public-coin
   eligibility; and
4. expose strategy-generated execution plus a separate trace-replay judgment,
   keeping honest witness and nonce in a request-bound strategy/local binding,
   never in the shared Core; retain strategy classes, games, probabilities,
   and theorem applicability in Analysis.

Relations needs no Schnorr-specific primitive. It must consume the repaired
Protocol execution and retain the already-required distinction between
relation-facing Witness inputs and unrelated private protocol state.

The change is fundamental because it changes the Core/realization factorization,
Core-derived facts, FS admission, and the meaning of execution evidence. It
should replay `FRI-Grind-1`, P01, and every later case that relies on transcript
coverage or prover causality. P01 selects this finite shape for testing; it
does not yet ratify the durable cross-family abstraction.

## 10. Closure gate

P01 closes only when all of the following hold:

1. the public source ledger freezes the cited revisions, while the fixture
   explicitly identifies `p=23,q=11,g=2,C={0,...,7}` as an independent toy
   profile and excludes CFRG/P-256 conformance;
2. the finite schema, one-byte codecs, frame grammar, initialization labels,
   application domain, challenge namespace, SHAKE128 query, low-three-bit
   sampler, and positive values are frozen before final replay;
3. Fresh and FS reconstruct the same `ChallengeNeutralConversationCore` but
   distinct realization and `ProtocolVariant` identities;
4. the positive report reproduces Fresh `c=3,z=3`, FS `c=4,z=10`, exactly two
   ordered FS transcript reads, accepting terminal witnesses, and exact replay
   qualification;
5. exhaustive evaluation reports 968 accepting transcripts, 3,388 extracted
   forks, and 88 exact challenge-conditioned SHVZK distribution equalities;
6. every negative-matrix row reaches its named first boundary, especially
   Statement/commitment omission and clairvoyant commitment, without demanding
   challenge inequality after a Statement/domain mutation;
7. relation public/secret operands are independently sourced; grounding,
   satisfaction, acceptance, and theorem applicability remain distinct;
8. identity perturbations distinguish semantic changes from evaluator,
   provenance, and report changes, and evaluator sources are digest-bound;
9. an independent, context-isolated replay reproduces the report from frozen
   public inputs and verifies the SHAKE query rather than trusting recorded
   digest-shaped fields; and
10. a cold reviewer either reproduces the repaired candidate or retains a
    decisive failed witness and exact reopening condition.

Until then, `FundamentalObstruction` is the current-target result and
Candidate C remains provisional. P01 does not activate R3, R4, or Stage 4B.
