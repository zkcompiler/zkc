# P01 Schnorr/Sigma: Source Reconstruction and Target Obstruction

> **Kind:** Temporary R2 T3 source-reconstruction and model-pressure record
> **State:** The prior Phase B snapshot failed cold review on modeled causality,
> occurrence aliasing, and independent-basis closure. The staged repair, rotated
> public report, and 69-test suite now pass. The current target remains
> fundamentally unable to express the complete source model; separate lifecycle
> and provenance cold rechecks pass on the repaired final snapshot.
> **Authority:** Non-normative. This page owns the P01 source reconstruction,
> current-target obstruction, and theorem boundary. The
> [Phase B Repair and Refreeze Decision](p01-phase-b-repair-and-refreeze.md)
> owns the selected finite model, executable evidence, and gate states.
> **Classification:** Current target: `FundamentalObstruction`. Repaired
> finite candidate: `Native` at the exact implemented support point only.
> **Research boundary:** Public primary and authoritative sources only. No
> material under `docs/private/` was consulted or copied.
> **Disposition:** Retain through R2--R4, absorb accepted results into their
> durable owners, then delete this page.

## 1. Result in brief

Minimal Schnorr separates three concerns that the model must not collapse:

1. one challenge-neutral conversation and verifier equation;
2. a Fresh or Fiat--Shamir realization of the challenge; and
3. causal prover generation, distinct from replay of an already completed
   trace.

The current target can represent the algebraic values, message order, Fresh
challenge, verifier equation, and terminal. It cannot represent the complete
source model because:

- a public `Statement` has no mandatory path into the first Fiat--Shamir
  challenge prefix;
- inclusion of a prior proof message remains an author-controlled transcript
  annotation rather than a consequence of its semantic role;
- reusable Fiat--Shamir admission does not establish the required public-coin
  eligibility law; and
- `ExecuteProtocol` consumes a completed `ProverTrace`, so it does not prove
  that `A` was chosen before the prover learned `c`.

These are shared protocol and execution-boundary defects, not missing
Schnorr-specific syntax. Phase B therefore implements a finite candidate with
one neutral Core, separate Fresh and Fiat--Shamir realizations, meaning-derived
Fiat--Shamir influence, staged owner-local generation, portable public replay,
and separate Relations and Analysis judgments. Its precommitment-before-
challenge result is limited to the modeled capability flow; it is not a theorem
about out-of-band knowledge or general non-anticipation. The exact construction
and evidence are intentionally delegated to the Phase B decision rather than
duplicated here.

## 2. Source ledger and exact use

| Source | Exact use in P01 |
|---|---|
| [Schnorr, *Efficient Identification and Signatures for Smart Cards*, CRYPTO '89](https://doi.org/10.1007/0-387-34805-0_22) | Historical identification and signature construction. |
| [Fiat and Shamir, *How To Prove Yourself*, CRYPTO '86](https://doi.org/10.1007/3-540-47721-7_12) | Historical removal of the verifier challenge through hashing; not a complete modern generic theorem. |
| [Damgård, *On Sigma Protocols*](https://cs.au.dk/~ivan/Sigma.pdf), Sections 1--3 | Minimal Schnorr equations, perfect special soundness, perfect special HVZK, and the knowledge-error theorem. |
| [Bellare--Palacio, CRYPTO 2002](https://www.iacr.org/archive/crypto2002/24420162/24420162.pdf), Figure 1 and Sections 3 and 5 | Stateful two-activation prover schedule, reset boundary, canonical Schnorr identification, and separate active/concurrent impersonation results. |
| [Abdalla--An--Bellare--Namprempre, EUROCRYPT 2002](https://www.iacr.org/archive/eurocrypt2002/23320414/main.pdf), Construction 1 and Theorems 1--2 | Identification-to-signature syntax and separate ROM, passive-security, and commitment-entropy obligations. |
| [Pointcheval--Stern, J. Cryptology 2000](https://doi.org/10.1007/s001450010003), Theorem 3 | Classical forking-extraction boundary for Fiat--Shamir signatures. |
| [Unruh, *Post-Quantum Security of Fiat-Shamir*](https://eprint.iacr.org/2017/398.pdf), introduction and Definition 17 | Statement-bound `H(instance || commitment)` form and separate QROM theorem boundary. |
| [CFRG Sigma Protocols draft v03](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-sigma-protocols-03), Sections 3--5 and 7 | Concrete linear-relation interface, single-use prover state, instance validation and serialization, challenge handling, simulator, and DSFS use. |
| [CFRG Fiat--Shamir draft v03](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-fiat-shamir-03), Sections 3--6 and 8 | Public-coin prerequisite, session separation, mandatory instance-first absorption, prefix-free codecs, duplex flow, decoding concerns, and theorem prerequisites. |

The two CFRG documents are design pressure, not authority over zkc and not the
source of the finite positive vector. The selected citations and revisions are
recorded in
[`cases/source-ledger.json`](../../../../evaluation/r2-p01-schnorr/cases/source-ledger.json).
The public report binds that ledger fixture's bytes; it does not vendor or hash
the external documents.

## 3. Source anatomy

For a prime-order subgroup generated by `g`, the relation and three-move
conversation are:

```text
R_DL(Y, x) iff x in Z_q and Y = g^x

Commit(Y, x; r):  r <- uniform Z_q; A := g^r
Challenge:         c <- uniform C, only after A
Respond:           z := r + c*x mod q
Verify:            accept iff g^z = A * Y^c
```

The public Statement is `Y`; the relation witness is `x`; `r` is private
protocol-local randomness, not another relation witness. A causal interactive
prover chooses `A` from its visible past and private state before receiving
`c`, then computes `z` after `c` is disclosed. A completed accepting tuple
does not establish that causal history: given `c,z`, a prover can set
`A = g^z * Y^(-c)` and satisfy the equation without demonstrating possession
of `x`.

For Fiat--Shamir, the verifier challenge is replaced by a construction whose
required input includes the public instance and prior commitment. At minimum,
the model must distinguish:

- eligibility of the source interaction for a public-coin transform;
- required semantic influences and their order;
- injective framing and codecs;
- session, suite, application, and challenge-domain separation;
- the challenge sampler and any bias or failure behavior;
- adaptive oracle-querying strategies; and
- the assumptions and loss of the particular transform theorem.

The repaired executable specializes these obligations to the self-contained toy
profile `p=23`, `q=11`, `g=2`, `C={0,...,7}`. The fixed public Statement is
`Y=13` and the owner-local positive assignment is `x=7,r=4`, giving `A=16`.
Fresh has `c=3,z=3`. The selected v3 Fiat--Shamir construction has
`c=6,z=2` and proof bytes `1002`. These values are finite evidence, not CFRG
conformance or a security parameterization.

For this profile, two accepting transcripts with the same `A` and distinct
challenges extract

```text
x = (z - z') * (c - c')^-1 mod 11.
```

For a prescribed `c`, the special-HVZK simulator samples `z` and sets
`A = g^z * Y^(-c) mod 23`. Exhaustive equality in this finite domain is useful
falsification evidence, but it does not promote the cited general theorems.

## 4. Current-target correspondence and obstruction

| Source item | Current target location | Result |
|---|---|---|
| Prover, Verifier, and public environment | [`protocol-model.md` Section 3.3](../../../pir/protocol-model.md#33-roles-knowledge-and-ports) | Native for this two-party public-coin case. |
| Instance `Y` and witness `x` | Public `Statement` and private Prover `Witness` input occurrences | Structurally representable. |
| Nonce `r` | `PrivateProverSample` attached to the commitment obligation | Structurally representable; sampling and single-use execution remain separate obligations. |
| Commitment `A` and response `z` | Prover-to-Verifier `Proof` messages | Values, order, and domains are representable. |
| Fresh challenge | `FreshChallenge` and PublicEnvironment randomness | Its occurrence, domain, visibility, and order are representable. |
| Equation and terminal | `InvokeCheck`, check-false rejection, and accepting terminal | Structurally representable; neither relation satisfaction nor theorem applicability follows. |
| `Y` before `A` in every FS prefix | [`fiat-shamir-and-composition.md` Section 3](../../../pir/fiat-shamir-and-composition.md#3-transcript-construction) | **Blocked.** Initialization accepts public `Context` ports, while the public `Statement` has no mandatory route. |
| Required inclusion of `A` | Message transcript annotation and event-action map | **Wrong authority.** An author can omit a semantic proof message instead of admission deriving and enforcing its influence. |
| Commitment-before-challenge causality | [`ProverTrace` and `ExecuteProtocol`](../../../pir/protocol-model.md#311-invocation-grammar-and-execution) | **Blocked.** A wholesale supplied trace is replay input, not evidence of causal strategy generation. |
| Public-coin FS eligibility | `ProtocolAdmissible` | P01 is public coin, but the reusable rule does not express the complete transform prerequisite. |
| DL relation correspondence | [`RelationBinding`](../../../relations/relation-model.md#6-protocol-to-relation-binding) | Bridges are expressible, but grounding, satisfaction, acceptance, and implications between them must remain separate. |
| Special soundness, HVZK, and FS security | [`cryptographic-properties.md`](../../../analysis/cryptographic-properties.md) | Analysis-owned applicability only; none follows from structural admission or finite replay. |

Encoding `Y` as generic `Context`, synthesizing a dummy Statement message, or
supplying a precomputed transcript would change semantic purpose or move
authority into the evaluator. Those workarounds do not constitute source-
faithful support.

## 5. Design implication

The selected repair has the high-level factorization:

```text
ChallengeNeutralConversationCore
  + exactly one ChallengeRealization
  = Protocol
```

The Core owns the ordered conversation, challenge occurrence and domain,
visibility, checks, and terminal behavior. A Fresh realization owns public-
coin resolution, distribution, and disclosure. A Fiat--Shamir realization
owns the admitted transcript construction and sampler. Required transcript
influences are derived from the Core's semantic roles and occurrences rather
than copied from author-controlled observation bits.

The durable design requirement still splits execution into two non-
interchangeable judgments:

```text
GenerateExecution(admitted protocol, strategy, invocation, allowed state,
                  coins or oracle, bounds)
ReplayPublicExecution(admitted protocol, public record, validation basis)
```

A future general generation relation must expose only the admitted visible
history at each prover decision point. The finite P01 evaluator does not yet
implement that strategy language. It instead creates an exact opaque occurrence
for a challenge-neutral prefix, freezes Relations authority, witness occurrence,
nonce, canonical commitment, response plan, validation bases, and resources in
a precommitment, and consumes that precommitment once at finalization. A Fresh
support-point binding enters only then; the Fiat--Shamir challenge is derived
from frozen `A`. Equal-content occurrences remain locally distinct.

Qualification is a read-only, non-authoritative reconstruction of frozen local
state followed by public replay; it cannot reuse finalization authority. Replay
verifies a completed public record but cannot mint honest-generation or witness-
possession evidence. Private assignments, relation-satisfaction authority, and
generation qualifications therefore stay owner-local; public artifacts, replay,
proof verification, Statement grounding, and finite Analysis remain portable.

This staged lifecycle establishes order only inside its modeled capability
flow. It does not establish out-of-band challenge ignorance, nonce uniformity or
independence, Fresh sampling, historical artifact-authoring chronology, or a
general adversarial non-anticipation property. Its closed `ResponsePlan` is not
a prover or adversary strategy language.

Relations requires no Schnorr-specific primitive. It must keep relation
admission, public-instance grounding, private witness satisfaction, protocol
acceptance, honest-prover correspondence, and theorem implications distinct.
Analysis, not PIR admission, owns strategy classes, games, extractors,
probabilities, assumptions, and theorem applicability.

This is a model-change request, not a durable ratification. Later witnesses
must pressure dynamic Statements, richer public-coin interactions, oracle
messages, composition, and protocols where Fresh and Fiat--Shamir genuinely
change interaction shape.

## 6. Current finite evidence boundary

The [Phase B decision](p01-phase-b-repair-and-refreeze.md) is the evidence and
gate owner. Its repaired executable checkpoint contains:

- 69 passing tests: 8 semantic, 27 execution/Interface, 8
  provenance/diagnostics, 13 Relations/Analysis, and 13 report/replay;
- a source-bound public report with 45 executed cases: 22 affirmative and 23
  nonaffirmative;
- Fresh `c=3,z=3` and Fiat--Shamir `c=6,z=2`, proof `1002`;
- a 448-byte Fiat--Shamir query with SHA-256
  `ccb57bf733f23917e32f91edfefc8ff82332bb30e36118f411f21caf874e4218`;
- 968 accepting finite transcripts, 3,388 unordered distinct-challenge forks,
  88 conditional distribution equalities, and 968 samples per side;
- a classification of all 203 declared diagnostics as 30 affirmative, 144
  constructible-driver, 15 internal, 1 environmental, and 13 retired; and
- a separately frozen expected projection and minimal copied-checkout replay.

The repaired report identity is
`evidence-sha256:a74b746e60a3fd344f00d8673011ce53749291d51fef2e4d126a7109bc091006`;
the expected projection has SHA-256
`0589d7aef533111dded0bc57bc8bb145a9e6abc98812903e33b278866ea29ae2`.

The diagnostic classification is a closed inventory, **not** executed
reachability. The current suite fires 68 of the 203 declared codes and leaves
135 unreached. This does not prove that all 144 constructible diagnostics have a
driver or reach their intended first boundary. Full diagnostic reachability
remains a nonblocking hygiene queue rather than the T3 denominator. The repaired
13-obligation semantic falsification matrix and all ten gates are closed at the
finite P01 scope. P01 is therefore retained as a T3 result, without promoting
the finite observations into a theorem or durable target decision.

The retired v1 prose and v2 implementation produced different transcript
constructions and positive values. Phase A preserved that drift in
[R2 State Reconciliation](r2-state-reconciliation.md); Phase B replaced both
with v3. They are historical failed candidates, not alternative current
specifications.

## 7. Theorem boundary and non-claims

The finite evaluator can check exact algebra, staged local generation within
its modeled capability flow, public replay, transcript construction, Relations
grounding, fork extraction, and conditional simulator distributions. It does
not establish:

- general completeness, special soundness, special HVZK, HVZK, or proof of
  knowledge;
- malicious-verifier, active, concurrent, or reset security;
- EUF-CMA signatures, ROM or QROM Fiat--Shamir security, or concrete-hash
  random-oracle realization;
- simulation soundness, composability, constant-time behavior, or compiler
  correctness;
- CFRG Sigma/Fiat--Shamir, P-256, or full-field-decoding conformance; or
- cryptographic hardness or secret confidentiality in the 11-element toy
  group.

In particular, the finite special-soundness and simulator equalities are not
general theorems. The local staged lifecycle proves neither out-of-band
challenge ignorance nor nonce independence, and `ResponsePlan` is not a
universal adversary language. The Fresh input is a fixed support point, not
sampling evidence. Fresh and Fiat--Shamir sharing one Core establishes no
distributional or cryptographic equivalence.

## 8. Promotion and reopening

Any durable redesign informed by P01 must preserve these distinctions:

1. conversation identity versus challenge realization;
2. semantic required influence versus authored transcript membership;
3. causal generation versus completed-trace replay;
4. owner-local private authority versus portable public evidence;
5. relation grounding and satisfaction versus verifier acceptance; and
6. structural admission and finite facts versus theorem applicability.

Reopen the P01 source model if the cited protocol schedule, required
Fiat--Shamir influences, relation equation, or theorem prerequisites were
misstated. Reopen the candidate decision under the conditions owned by the
Phase B page. P01 does not activate R3, R4, or Stage 4B.

## 9. Model-change request

`MCR-P01` requests the factorization and judgment separation summarized in
Section 5. Its durable form must be evaluated together with later protocol
witnesses; this page does not decide the final cross-family vocabulary.

## 10. Historical Phase A pointer

### 10.1 Phase A blocker summary

[R2 State Reconciliation](r2-state-reconciliation.md#4-p01-closure-finding)
preserves the bounded Phase A blocker summary, not a line-by-line current gate
matrix. The Phase B decision owns the current gate table and supersedes the
v1/v2 construction and publication status while retaining the historical
mismatch as negative evidence.
