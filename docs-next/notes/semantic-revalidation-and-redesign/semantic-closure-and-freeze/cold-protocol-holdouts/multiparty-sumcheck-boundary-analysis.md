# Multiparty Sumcheck Boundary Analysis

> **Kind:** Temporary source reconstruction, frozen-target pressure test, and
> adjudication record
> **State:** Complete
> **Frozen target:** `63c48b22c7aac56d9af3ab460e4ea135a87039f3`
> **Decision:** `IntentionalBoundary` for the full MPC protocol;
> `ProfileOrModule` for its virtual two-role Sumcheck projection; no shared
> semantic profile rotates
> **Authority:** None

## 1. Question and assigned depth

This holdout asks whether the frozen two-role Protocol model can faithfully
represent the protocols in *On the Power of Sumcheck in Secure Multiparty
Computation*, where several MPC parties jointly construct a masked Sumcheck
proof and every party also verifies the opened proof.

The answer has two layers:

1. The **virtual Sumcheck projection**—one logical prover, one logical verifier,
   masked polynomial messages, public coins, and verifier checks—is
   `ProfileOrModule`.
2. The **actual MPC protocol and its security experiment** are an
   `IntentionalBoundary` of finite v0. Collapsing the parties into the virtual
   roles loses secret-sharing knowledge, coalition corruption, per-party
   views, broadcast/opening behavior, correlated randomness, and security with
   abort.

This is the first holdout in the package whose full source semantics do not fit
the frozen role lifecycle. It does not trigger a shared rotation because the
current v0 deliberately identifies one Prover, one Verifier, and at most one
PublicEnvironment. A future multiparty regime must be researched as a coherent
extension rather than added as a local role-count flag.

## 2. Source lock and theorem boundary

The primary source is Zhe Li, Chaoping Xing, Yizhou Yao, and Chen Yuan,
*On the Power of Sumcheck in Secure Multiparty Computation*, IACR ePrint
2025/177, exact PDF recorded in `source-ledger.json`.

The source separates several protocols and settings:

- classical Sumcheck;
- a general distributed Sumcheck over an authenticated sharing of a
  polynomial;
- multiplication verification for an honest majority using Shamir sharing;
- authenticated-triple verification and a malicious MPC compiler for a
  dishonest majority; and
- ideal functionalities for public coins, commitments, sharings, triples,
  authentication, preprocessing, and target verification.

The security model is static malicious security with abort. Honest-majority
and dishonest-majority protocols use different sharing/authentication
assumptions and corruption thresholds. Theorems 5.2 and 6.1 have different
hybrid functionalities, communication/randomness costs, and adversary bounds.
They are not one generic “distributed Sumcheck is secure” theorem.

This boundary analysis records source correspondence only. It establishes no
simulation proof, soundness bound, privacy statement, malicious-security
compiler, or ideal-functionality realization.

## 3. Source-native protocol anatomy

### 3.1 Why the proof is distributed

The statement and witness vectors are secret shared. No single party knows the
complete polynomial or multiplication relation. The parties jointly emulate a
virtual Sumcheck prover by locally computing shares of each round polynomial
and collectively opening that polynomial.

The same parties jointly emulate the virtual verifier. A public coin
functionality samples each challenge for all parties, and every party locally
checks the reconstructed messages. Thus a physical participant contributes to
both sides of the virtual proof.

This is not the ordinary delegated-proof setting where a prover knows a whole
witness and a separate verifier knows a whole public statement.

### 3.2 Distributed Sumcheck schedule

For the paper's general distributed Sumcheck:

1. parties hold authenticated shares of the claimed sum and polynomial;
2. correlated randomness supplies shares of a sparse masking polynomial;
3. parties open the masked claimed sum;
4. in each round, every party computes a share of the current univariate
   polynomial and the parties collectively open it;
5. every party checks the Sumcheck recurrence;
6. the public coin functionality samples the next field challenge for all
   parties;
7. parties jointly compute and open the masked final evaluation;
8. every party performs the final equality check; and
9. all parties accept, or reject and abort.

The masking polynomial is necessary for MPC privacy because the opened
Sumcheck messages would otherwise leak information about the shared input.

### 3.3 Multiplication verification

The main applications reduce correctness of secret-shared multiplication
vectors to a Sumcheck relation over multilinear extensions. Tailored vanishing
polynomials and a sparse random mask preserve privacy while allowing selected
evaluations to be opened. Distributed bookkeeping gives linear aggregate work
and logarithmic rounds.

In the honest-majority protocol, Shamir shares provide robustness under the
selected threshold, but intermediate product shares need not all be
authenticated. In the dishonest-majority protocol, authenticated SPDZ-style
shares, MAC checks, commitments, Beaver triples, and additional correlated
randomness constrain additive attacks and openings.

The source explicitly analyzes collusion between the corrupted contribution to
the emulated prover and the corrupted contribution to the emulated verifier.
Privacy and soundness must be proved simultaneously through simulation.

### 3.4 Ideal functionalities are theorem premises

The paper describes its protocols in hybrid models containing, among others:

- a coin-toss functionality broadcasting uniform field elements;
- commitment/opening functionality;
- random Shamir-sharing and authenticated-sharing functionality;
- Beaver-triple and authenticated-triple functionality;
- preprocessing functionality; and
- target multiplication-verification functionality.

These are not automatically realizable runtime services. The exact hybrid
functionality set, corruption threshold, setup phase, and abort behavior are
part of each theorem's semantic basis.

## 4. What the frozen model can represent

### 4.1 Virtual two-role Sumcheck projection

If the distributed machinery is deliberately abstracted away, the resulting
logical proof has the familiar two-role form:

- one prover Message for the masked claimed sum and one polynomial Message per
  round;
- one public FreshChallenge per round;
- recurrence and final-evaluation checks; and
- accept/reject terminals.

Exact field, polynomial, multilinear-extension, masking, and Sumcheck laws can
live in Foundation modules and Relations profiles. One Plan can describe an
honest virtual prover. An Analysis profile can state the classical Sumcheck
soundness experiment or a zero-knowledge theorem with exact premises.

The public coin functionality projects to PublicEnvironment at this logical
level. The projection is useful for reasoning about the proof skeleton, but it
is not the source MPC protocol or evidence for its malicious security.

### 4.2 A distributed implementation is not automatically equivalent

Some engineering deployments may distribute the computation of one logical
prover while preserving one externally observable proof transcript. Such a
deployment could be a Realization of a virtual Prover if the only requested
claim is external transcript correspondence and no per-party security property
is in scope.

The paper asks for much more. Its claims quantify corrupted subsets, protect
honest-party inputs, reason about authenticated shares and openings, and permit
abort. Those internal observations and strategies are theorem-bearing
semantics. Calling them “implementation details” would erase the proposition
being proved.

## 5. First failed mappings

### 5.1 Collapse all MPC parties into the Prover role

**Attempt.** Store the tuple of all shares in one Prover private state and let
one Plan compute every proof message.

**Failure.** The resulting role knows enough to reconstruct the entire shared
statement and witness. In the source, no individual honest party has that
knowledge, and an adversary sees only the corrupted coalition's shares and
messages. The collapse destroys the privacy experiment and gives one strategy
control over honest-party behavior.

**Disposition.** Valid only as a virtual transcript projection with explicit
nonclaims. It cannot represent the MPC theorem.

### 5.2 Collapse all MPC parties into the Verifier role

**Attempt.** Let one Verifier perform the recurrence and final checks.

**Failure.** The source has every party verify, with corrupted and honest local
views and a common abort outcome. A single verifier erases disagreement,
delivery, local state, and the corrupted verifier contribution.

**Disposition.** Virtual projection only.

### 5.3 Give one role both Prover and Verifier classes

**Attempt.** Model each physical party as a role that may emit proof messages
and challenges/checks.

**Failure.** Frozen Core roles have one class, and admission requires exactly
one Prover and one Verifier. More importantly, merely allowing two labels would
not define per-party knowledge, broadcasts, shared openings, corruptions, or
joint decision rules.

**Disposition.** A genuine multiparty regime requires a coherent role and
experiment redesign, not a new enum case.

### 5.4 Encode parties as data under one strategy

**Attempt.** Keep one Prover strategy and place a participant index on each
share/message value.

**Failure.** Indexing data does not restrict which share the strategy can read,
quantify over corrupted subsets, or preserve separate local states. The type
shape cannot supply authority and knowledge isolation.

**Disposition.** Semantic loss; reject as a full-protocol mapping.

### 5.5 Compose one two-role Core per party

**Attempt.** Give every party its own Prover/Verifier run and compose the runs.

**Failure.** The source has one synchronized shared execution: collective
openings, one public challenge sequence, all-to-all observations, shared
correlated randomness, and a common accept/abort decision. Independent
two-role runs neither establish broadcast agreement nor represent a coalition
that spans them.

**Disposition.** Existing Core composition is insufficient for the full
multiparty semantics.

### 5.6 Treat hybrid functionalities as ordinary host services

**Attempt.** Use runtime RNG, storage, and helper calls for coin toss,
commitment, and correlated sharing.

**Failure.** The exact functionalities and their adversarial interfaces are
theorem premises. Ambient services have no semantic identity, corruption
behavior, or simulation correspondence.

**Disposition.** In a future multiparty model, ideal functionalities and their
realizations require explicit experiment and composition profiles.

## 6. Why the boundary is intentional rather than a local defect

The frozen Core deliberately requires exactly one Prover, exactly one
Verifier, and at most one PublicEnvironment. The rest of the current model is
built around that choice:

- role-indexed knowledge and visibility;
- one Prover strategy decision view;
- one honest Prover Plan and its private randomness;
- message endpoint and obligation derivation;
- role-specific Interface and OIR projection;
- transcript influence and public-coin interpretation; and
- Analysis strategy, extractor, and property profiles.

Faithful multiparty support would change all of these together. Adding a role
count while leaving their laws unchanged would create a model that parses
multiparty traces but cannot state their security.

The full source protocol is therefore an **intentional finite-v0 boundary**.
This is preferable to either an unsound virtual encoding or an unresearched
cross-cutting rotation. It becomes a required redesign only if the project
charter later includes MPC security, threshold/distributed proof generation as
a semantic subject, or per-party implementation-security claims.

## 7. Requirements for a future multiparty regime

A future research package must co-design at least:

### 7.1 Protocol participants and communication

- a finite authenticated participant set;
- participant-local state and role capabilities rather than one global class;
- point-to-point, broadcast, reconstruction/opening, and delivery semantics;
- synchronous/asynchronous and abort/delivery assumptions;
- local terminal decisions plus an agreement rule; and
- exact ideal-functionality calls and return visibility.

### 7.2 Knowledge and honest construction

- participant-indexed knowledge and visibility;
- shared-value declarations whose shares have separate owners;
- correlated private randomness distributed across parties;
- joint message/opening construction from local shares;
- honest-party Plans or a distributed construction object; and
- authority-preserving reconstruction and authentication checks.

### 7.3 Adversary and Analysis

- static and adaptive corruption structures;
- threshold/monotone access structures and coalition-local views;
- one joint adversarial strategy controlling exactly corrupted participants;
- honest-party strategies and environment/scheduler interfaces;
- real/ideal simulation experiments with abort;
- hybrid-functionality composition and realization theorems; and
- separate privacy, correctness, robustness, fairness, guaranteed-output, and
  efficiency properties.

### 7.4 Interface, OIR, and Realization

- one endpoint projection per participant and functionality;
- broadcast and authenticated-channel obligations;
- setup/preprocessing distribution and lifecycle;
- local secret material and erasure/transport boundaries; and
- correspondence between the multiparty execution and any virtual proof
  transcript.

This is a regime-level program. It may ultimately select a reusable
`DistributedRealization` layer around a two-role logical proof, a generalized
Core, or two linked semantic subjects. The holdout does not preselect among
those alternatives.

## 8. Falsification matrix

| Mutation or attempted claim | Required result |
|---|---|
| Give one virtual Prover every party's share and claim MPC privacy | unsupported/semantic loss |
| Quantify one prover adversary instead of a corrupted coalition | theorem applicability refuses |
| Change honest-majority threshold to dishonest majority | protocol/theorem identity mismatch |
| Omit one hybrid functionality | support or applicability is incomplete |
| Replace the common coin with one party's unverified RNG | source correspondence is negative |
| Give each party an independent Sumcheck challenge | source correlation and transcript correspondence are negative |
| Open an unmasked round polynomial | privacy property is not applicable or is negative |
| Treat unauthenticated input shares as binding | required premise remains unanswered |
| Reuse Shamir robustness in the SPDZ-style protocol | sharing/profile mismatch |
| Hide a failed authenticated opening and continue | terminal/abort correspondence is negative |
| Let only one party verify and infer all-party acceptance | decision correspondence is negative |
| Treat a broadcast as several unrelated two-party messages | delivery/agreement semantics are absent |
| Compose independent party runs and infer one MPC execution | unsupported composition |
| Use a Realization transcript test as simulation-security evidence | evidence kind/applicability mismatch |
| Attach Theorem 5.2 to the Theorem 6.1 hybrid model | theorem source/applicability refuses |
| Infer knowledge soundness of a virtual prover from MPC authentication | unsupported conclusion |

## 9. Boundary adjudication

| Source pressure | Result | Disposition |
|---|---|---|
| Classical masked Sumcheck transcript | `ProfileOrModule` | exact two-role protocol and relation profiles |
| Public common coins at virtual level | `Native` | PublicEnvironment challenge occurrences |
| Joint proof-message computation | not faithful in one Plan | future distributed construction semantics |
| Every party verifies | not faithful in one Verifier | future participant/local-decision semantics |
| Secret shares and per-party views | semantic loss under role collapse | future participant-indexed knowledge |
| Static corrupted coalition | absent | future Analysis corruption structure |
| Security with abort | absent for multiparty source | future real/ideal experiment profile |
| Hybrid functionalities | absent as multiparty subjects | future composition/Analysis profiles |
| External virtual transcript correspondence only | potentially a Realization property | later exact construction |
| Full paper protocol and theorem | `IntentionalBoundary` | outside finite two-role v0 |

## 10. Classification and nonclaims

The portfolio's primary result is **`IntentionalBoundary`** because the named
holdout is the full multiparty protocol, not merely its virtual Sumcheck trace.
The virtual projection is `ProfileOrModule` and remains useful as an explicit
subordinate result.

No shared semantic profile rotates at this checkpoint. The holdout instead
creates a charter-level reopening condition and a future regime research
package.

This analysis does **not** establish:

- support for arbitrary participant sets, thresholds, or coalitions;
- a multiparty Core, Plan, Interface, OIR, or Realization;
- correctness of a virtual-to-distributed implementation;
- any ideal functionality or secure realization;
- privacy, soundness, malicious security, zero knowledge, fairness, or
  guaranteed output;
- the paper's communication or computation bounds;
- an executable fixture; or
- a decision that multiparty support belongs in the eventual product charter.

## 11. Retained work and reopening conditions

Retain:

1. the exact virtual Sumcheck projection as a future source-pinned profile;
2. the failed collapse encodings as regression cases;
3. the distinction between distributed implementation correspondence and
   multiparty protocol security;
4. the participant/coalition/functionality requirements above; and
5. the paper as one source in a later cross-family multiparty study, alongside
   threshold proving, distributed SNARK provers, and MPC-in-the-head.

Reopen the shared architecture only after one of these decisions:

- the project charter requires source-level MPC or coalition-security claims;
- threshold/distributed prover internals become semantic rather than purely
  external realization concerns;
- a second materially different source family selects a common participant
  and corruption model; or
- a concrete consumer cannot state a required property through a virtual
  Protocol plus an exact distributed-realization relation.

If reopened, the complete dependent identity cone must rotate. A local
`RoleClass` edit is not an admissible repair.
