# P01 Phase B Repair and Refreeze Decision

> **Kind:** Temporary R2 research and redesign decision
> **State:** The prior 62-test snapshot failed cold review on modeled causality,
> exact occurrence authority, and independent-basis closure. The staged repair,
> 69-test suite, rotated public report, separately refrozen expected projection,
> copied-checkout replay, and separate lifecycle and provenance cold rechecks
> now pass. P01 is retained at T3 for this exact finite scope.
> **Authority:** Non-normative. This page owns the selected P01 Phase B model,
> its current evidence boundary, and its reopening conditions.
> **Scope:** P01 Schnorr/Sigma only. It does not activate P02, R3, R4, or
> Stage 4B.

## 1. Decision

Phase B replaces the inconsistent documented v1 and implemented v2 candidates
with one P01-specific construction and evidence architecture:

1. one challenge-neutral Schnorr conversation Core;
2. distinct Fresh and Fiat--Shamir realizations and Protocol identities over
   that Core;
3. one strong Fiat--Shamir construction v3 whose required prefix is derived as
   `Statement` followed by the prior commitment;
4. a staged owner-local generation and relation-satisfaction lane for private
   material, with exact occurrence authority and single-use finalization;
5. a portable verification lane for public executions, proof bytes, replay,
   Statement grounding, finite Analysis, and reports;
6. disjoint semantic, artifact, validation-basis, Evidence, and local-reference
   identity families; and
7. a public report that closes over exact public fixtures, component source
   manifests, typed evidence, scope, and non-claims, but not private material,
   expected results, or a run-time pass verdict.

The implementation is in the
[P01 evaluation package](../../../../evaluation/r2-p01-schnorr/README.md).
The protocol case page records the source reconstruction and current-target
obstruction in [P01 Schnorr/Sigma](p01-schnorr-sigma.md). This page is the owner
for the Phase B decision; the other pages link here instead of repeating the
retired v1/v2 constructions.

## 2. Why the repair was necessary

Phase A found two independent blockers.

First, the prose and evaluator implemented different transcript constructions
and positive vectors. Neither could be called the frozen P01 model. More
fundamentally, the current target permits authored transcript membership and
has no mandatory path from a public `Statement` to the first challenge. That
cannot express strong Fiat--Shamir admission.

Second, the former executable derived a portable digest from a private witness
and nonce. In the toy domain that digest was an exhaustively reversible label
over only `11 * 11` candidate pairs. Different private assignments also shared
an occurrence coordinate derived from a public slot. Those were evidence and
authority defects, not claims about breaking SHA-256.

The repaired model therefore treats a conversation, a challenge realization,
a private occurrence, a public artifact, a validation basis, and an observed
evidence record as different kinds of object.

### 2.1 Cold-review reopening and repair

The first Phase B refreeze had 62 passing tests and report identity
`evidence-sha256:19629957a3e6f475d8fe0e105fbe3393338e0a6f167a4f4340fb0acb892f8a0a`.
Cold review invalidated that snapshot for three reasons:

1. a challenge-bearing invocation and caller-selected nonce reached generation
   together, so a strategy label did not establish commitment-before-challenge
   order;
2. owner-local authority retained only invocation content, allowing an equal-
   content but distinct runtime occurrence to reuse a binding; and
3. the independent-reconstruction validation basis omitted shared closed-term
   and semantic dependencies that the reconstruction actually consumed.

The repaired lifecycle is now challenge-neutral prefix, exact opaque invocation
reference, frozen precommitment, and consuming finalization. The old report
identity and expected projection are retired evidence of the failed snapshot,
not aliases for the repaired result.

### 2.2 Final cold re-review and closure

Gate 10's read-only re-review found two further closure defects before passing:

1. a typed but out-of-domain Fresh binding was rejected and consumed, yet its
   value was installed as resolvable challenge state; and
2. Python executed `p01model/__init__.py`, but the file was absent from the
   component validation bases and could change without rotating the report.

The final repair admits a completed invocation before installing challenge
state, while preserving consuming failure and the distinction between invalid
invocation refusal and a later response-stage abort. Every component basis and
the public evaluator now bind the executed package initializer, and a copied-
checkout mutation proves that changing it rotates all dependent identities.
Separate lifecycle and provenance reviewers reran the original and new
counterexamples against the final identity and reported no remaining P1, P2,
or P3 finding within the stated scope.

## 3. Selected finite model

### 3.1 Algebra and protocol

The executable profile is intentionally small:

```text
p = 23
q = 11
g = 2
C = {0,...,7}
Statement Y = 13
private witness x = 7
private nonce r = 4
commitment A = 16
```

The shared Core owns the public Statement, the ordered
`A, c, z, check, terminal` conversation, value domains, visibility, verifier
equation, and terminal routing. It does not own a Fresh sampler, a witness, or
a nonce.

`FreshRealization` binds `c` to the public environment's conditional
public-coin contract. `FiatShamirRealization` binds the challenge occurrence to
the v3 transcript construction. They produce distinct Protocol identities
while retaining one Core and honest-prover contract. The checked factorization
does not assert distributional or cryptographic equivalence. The frozen Fresh
binding is one public support point; it does not exercise or validate the
declared sampling law.

### 3.2 Fiat--Shamir construction v3

The v3 semantic tuple fixes:

| Field | Selected value |
|---|---|
| Source | Exact admitted Fresh Protocol, Fresh realization, and public-coin basis |
| Language and argument | P01 discrete-log language and three-move Schnorr argument |
| Proof flavor | Fixed-width `(A,z)` |
| Runtime authority | Application-owned public context contract |
| Transcript primitive | SHAKE128 XOF duplex using the CFRG v03 mechanics selected by P01 |
| Session derivation | Typed tag followed by a 32-byte derived session identifier |
| Required atoms | Initial `Statement Y`, then prior proof message `A` |
| Framing | Typed, length-delimited, prefix-free frames |
| Challenge | Squeeze one byte, interpret little-endian, reduce modulo eight |
| Salt and composition | `NoSalt`, `Standalone` |

The runtime tag binds the construction identity, runtime-context contract
identity, and concrete application-context bytes. Admission recomputes the
required prefix from Core meaning. Omitting `Y` or `A`, reordering them, or
changing a source kind, domain, codec, framing rule, challenge namespace,
source Fresh Protocol, application authority, or decoder fails admission.
Runtime challenge derivation re-runs construction admission, so a caller cannot
execute an unadmitted weak prefix.

The frozen public support point is:

```text
application context  zkc/p01/test-session/alpha
Statement            13
commitment           16
query length         448 bytes
query SHA-256        ccb57bf733f23917e32f91edfefc8ff82332bb30e36118f411f21caf874e4218
challenge            6
response             2
proof bytes          1002
```

A separately coded path in `independent.py` reconstructs the session, frames,
query, and challenge without calling the semantic framing, duplex, or sampling
helpers. It still consumes the admitted construction shape and finite
parameters. Its validation basis therefore binds the executed package
initializer plus `terms.py`, `semantic.py`, and `independent.py`. Byte-for-byte
agreement is implementation-diversity falsification evidence, not independent
semantic authority, CFRG
conformance, or a Fiat--Shamir theorem.

The CFRG Sigma and Fiat--Shamir drafts v03, RFC 9380, the duplex Fiat--Shamir
paper, and the QROM Fiat--Shamir paper are pinned in `cases/source-ledger.json`.
They are design pressure and theorem-boundary inputs. P01 does not implement a
CFRG ciphersuite, P-256, full-field decoding, or the CFRG proof container.

## 4. Authority and identity architecture

### 4.1 Owner-local lane

Private witness assignments, nonce material, relation satisfaction, response
plans, and read-only audit authority remain owner-local. The lifecycle is:

1. `begin_invocation` accepts a challenge-neutral `PublicInvocationPrefix` and
   creates a fresh opaque reference for that exact runtime occurrence;
2. `precommit` freezes the exact Relations satisfaction authority, witness
   occurrence, nonce, canonical `A = g^r`, `ResponsePlan`, evaluator basis, and
   local and public resource policies;
3. finalization consumes the exact invocation-reference/precommitment-handle
   pair once, then accepts a Fresh support-point binding or derives the Fiat--
   Shamir challenge from the already frozen `A`; and
4. qualification reconstructs the frozen transition read-only and replays its
   public projection without reusing or resurrecting finalization authority.

The opaque owner-local objects:

- have no semantic or artifact identity;
- reject term encoding, serialization, and portable equality;
- are bound to the exact assignment object, owner, invocation occurrence,
  precommitment, purpose, and owner generation; and
- cannot be substituted by an equal scalar, another occurrence, or another
  owner.

Equal-content prefixes may have the same portable content identity, but they
receive distinct local references and cannot share precommitment authority.
The first finalization attempt consumes its handle before inspecting a supplied
Fresh value, so a failed attempt cannot retry with another challenge. Only an
admitted completed invocation installs challenge state: a missing, malformed,
or out-of-domain Fresh binding remains unresolvable after refusal. A valid
invocation may still expose its resolved challenge if its later response stage
aborts or exceeds a public resource ceiling. Local generation uses and checks
Relations-issued satisfaction authority rather than
reimplementing the relation equation. `ResponsePlan` selects only the finite
canonical, invalid-response, or abort behavior of this evaluator; it is not a
general prover or adversary strategy language.

This lifecycle establishes ordering only inside the modeled capability flow.
It does not establish that an external caller lacked out-of-band challenge
knowledge, that the nonce was uniform or independent, that the artifact was
historically authored before a challenge, that the Fresh binding was sampled,
or that a general adversarial non-anticipation property holds.

The private fixture `cases/private-generation.json` is loaded only by
owner-local generation tests. It is never read or hashed by the public report
or runner.

### 4.2 Portable lane

The portable lane contains only public invocation data, public protocol events,
transcript receipts, proof bytes, verifier results, resource accounting, and
source-bound replay evidence. It can establish exact replay and an `Accept` or
`Reject` terminal under the named public inputs and validation basis. It cannot
establish witness possession, honest generation, Fresh sampling quality, or a
security theorem.

The FS proof interface exposes application context and Statement as external
public inputs, carries exactly `(A,z)`, and always recomputes `c`. The shared
public verifier owns the Schnorr equation and terminal route for both public
execution replay and proof verification.

Relations receives a sealed Statement view minted only after exact public
replay. Public grounding retains:

- semantic relation and instance identities;
- the exact Statement-event `ArtifactContentId`;
- the public-execution qualification `EvidenceRecordId`; and
- its own `EvidenceRecordId`.

Grounding, relation satisfaction, verifier acceptance, honest generation, and
theorem applicability remain separate judgments.

### 4.3 Identity lanes

| Lane | Examples | Meaning |
|---|---|---|
| Semantic identity | profile, Core, Protocol, construction, Interface, relation | Stable meaning under the P01 semantic regime |
| `ArtifactContentId` | public fixture bytes, proof bytes, public execution record, Statement event | Exact public bytes or canonical public content |
| `ValidationBasisId` | semantic, execution, Interface, Relations, Analysis, report/replay source manifests | Exact checker law, source closure, and bounds |
| `EvidenceRecordId` | checked execution, proof verification, grounding, case, report | A bounded observation under named operands and bases |
| Owner-local reference | witness occurrence, invocation reference, precommitment handle, local qualification | Exact nonportable authority and runtime occurrence coordinate |

Source changes rotate validation and Evidence identities without changing an
otherwise equal semantic Protocol. Public artifact changes rotate content and
dependent Evidence identities. No digest-shaped string is allowed to erase
these distinctions.

## 5. Current executable evidence

The repaired P01 suite passes 69/69 tests: 8 semantic, 27
execution/Interface, 8 provenance/diagnostics, 13 Relations/Analysis, and 13
report/replay tests. Together they cover semantic admission and CFRG
duplex byte examples, owner-local generation and authority, public execution
and proof verification, resource bounds, provenance, Relations, finite
Analysis, exact report reconstruction, expected-projection separation, source
and fixture perturbations, staged causality, exact occurrence separation,
single-use finalization, read-only audit reconstruction, and isolated copied-
checkout replay.

Before loading expected results, the public report builds 45 exact cases:

- 22 affirmative cases;
- 23 nonaffirmative cases, including strong-FS and public-coin mutations,
  malformed and rejecting proofs, public resource ceilings, Statement-
  grounding mismatch, equal-challenge rejection, and six theorem refusals;
- Fresh public replay with `c=3,z=3`;
- FS public replay with `c=6,z=2` and proof `1002`; and
- FS query bytes reproduced by the separately coded reconstruction path.

The exact finite Analysis results are:

| Measurement | Count |
|---|---:|
| Accepting transcripts | 968 |
| Unordered distinct-challenge forks | 3,388 |
| Challenge-conditioned real/simulator distribution equalities | 88 |
| Samples per side across those distributions | 968 |

Every extracted fork is validated through Relations-owned owner-local
satisfaction. The Analysis API separately refuses promotion to general special
soundness, special HVZK, HVZK, knowledge soundness, ROM Fiat--Shamir, and QROM
Fiat--Shamir.

The current source-bound report identity is:

```text
evidence-sha256:a74b746e60a3fd344f00d8673011ce53749291d51fef2e4d126a7109bc091006
```

The separately frozen expected projection has SHA-256
`0589d7aef533111dded0bc57bc8bb145a9e6abc98812903e33b278866ea29ae2`.
These identify the repaired source-bound report and oracle snapshot. They are
the exact identities that passed the bounded final cold rechecks; they are not
durable v0 identities, release designations, or security claims. Any later
evaluator, manifest, or report-source edit must rotate the dependent evidence.

The old combined v1 fixture `cases/schnorr-p01.json` and monolithic legacy
`tests/test_p01.py` have been removed. Public replay inputs, the research source
ledger, and private owner-local generation inputs now have separate files. The
tests are split by semantic, execution/Interface, provenance/diagnostics,
Relations/Analysis, and report/replay ownership.

The v3 public fixture fixes exact public disclosure, `Application` context
authority, the Fresh support point's explicit non-sampling classification, the
FS proof, public resource plan, and non-claims. It cannot author a finite-
analysis claim: the report derives that scope from the executed exhaustive
results. The v3 private sidecar is decoded under an exact test-only schema and
supplies the owner-local witness, nonce, and local resource plan; neither the
report nor the runner opens or hashes it.

## 6. Owned semantic falsification matrix and diagnostic hygiene

Gate 6 is defined by source- and architecture-bearing obligations, not by the
number of defensive branches in the evaluator. Each row below has a positive
control, a minimal falsifier, an exact first result, and maintained public-case
or unit-test evidence.

| Obligation | Positive control | Minimal falsifier and exact result | Maintained evidence |
|---|---|---|---|
| Statement influence | Admitted v3 construction: `Affirmative / transcript-construction / P01-FS-OK` | Omit `Y`: `SemanticNegative / transcript-prefix:challenge:c / P01-FS-005` | `semantic/fs-construction-admitted.v2`; `negative/fs/statement-omitted.v2` |
| Commitment influence | Admitted v3 construction: `Affirmative / transcript-construction / P01-FS-OK` | Omit `A`: `SemanticNegative / transcript-prefix:challenge:c / P01-FS-005` | `semantic/fs-construction-admitted.v2`; `negative/fs/commitment-omitted.v2` |
| Prefix order and typing | Exact `[Y,A]` prefix: `Affirmative / transcript-construction / P01-FS-OK` | Reorder: `SemanticNegative / transcript-prefix:ordered-exactness:c / P01-FS-006`; mistype or mis-codec: `SemanticNegative / transcript-atom:typed-occurrence-source / P01-FS-007` | `negative/fs/prefix-reordered.v2`; `negative/fs/atom-codec-changed.v2`; semantic mutation test |
| Fresh source, public-coin contract, and factorization | Eligible external public slot: `Affirmative / source-correspondence:public-coin-eligibility / P01-PCOIN-OK`; pair: `Affirmative / relations:fresh-fs-factorization / P01-FACT-OK` | Prover-owned challenge: `SemanticNegative / source-correspondence:public-coin-eligibility / P01-PCOIN-001`; foreign source Protocol: `Mismatch / transcript-construction:source-public-coin-basis / P01-FS-021`; altered Fresh contract: `SemanticNegative / fresh-realization:public-coin-contract / P01-FRESH-002` | `semantic/public-coin-eligible.v3`; `negative/semantic/prover-owned-challenge.v3`; factorization and source-mutation cases; semantic mutation test |
| Commitment causality | Canonical precommitment freezes `A` before modeled challenge resolution; finalized generation qualifies as `Affirmative / local-generation-qualification / P01-LOCAL-QUAL-OK` | Resolve the challenge before finalization: `Refused / local-precommitment:causality / P01-LOCAL-EXEC-002`; after finalization the same state-sensitive operation returns the positive `ChallengeReceipt` | staged owner-local generation and challenge-resolution tests |
| Proof shape, domain, and semantic rejection | Canonical proof: `Affirmative / fs-proof-verification / P01-VERIFY-OK` | Short/trailing: `Malformed / fs-proof-decoding:length / P01-PROOF-001`; out of domain: `SemanticNegative / fs-proof-decoding:field-domain / P01-PROOF-002`; well-formed false proof: `SemanticNegative / fs-proof-verification:terminal / P01-VERIFY-002` | `interface/fs-proof-accepted.v2`; four `negative/interface/*` report cases; proof boundary tests |
| Owner-local private authority | Exact assignment and owner: `Affirmative / relations:satisfaction / P01-SAT-OK` | Same-value other occurrence or cross-owner use: `Refused / owner-local-binding:relation-authority / P01-LOCAL-BIND-002` | exact-binding and Relations owner-authority tests |
| Exact invocation occurrence and single use | Exact prefix occurrence, invocation reference, and precommitment handle finalize once | Equal-content distinct occurrence, cross-store or mismatched handle: `Refused / local-precommitment:authority / P01-LOCAL-BIND-003`; second finalization: `Refused / local-precommitment:single-use / P01-LOCAL-BIND-003` | equal-content occurrence, handle-authority, and consuming-finalization tests |
| Execution-issued Statement grounding | Fresh/FS grounding: `Affirmative / relations:execution-grounding-shape / P01-GRD-SHAPE-OK` | Caller-exported value: `Malformed / relations:execution-grounding-shape:statement / P01-GRD-001`; wrong value: `Mismatch / relations:execution-grounding-shape:value / P01-GRD-008` | two `relations/*-execution-grounding.v2` cases; `negative/relations/statement-value-mismatch.v2`; grounding-authority test |
| Special-soundness precondition and finite enumeration | Exhaustive fork check: `Affirmative / analysis:finite-special-soundness:exhaustive / P01-SS-ENUM-OK` | Equal challenges: `SemanticNegative / analysis:finite-special-soundness:distinct-challenges / P01-SS-006` | `analysis/exhaustive-special-soundness-algebra.v2`; `negative/analysis/equal-challenge-fork.v3` |
| SHVZK enumeration and theorem non-promotion | Exhaustive equality: `Affirmative / analysis:finite-shvzk:exhaustive / P01-SHVZK-OK` | Six promotions: `Refused / analysis:applicability:<claim> / P01-APP-101..106` | `analysis/exhaustive-shvzk-distribution.v2`; six `analysis/theorem-refusal/*` cases |
| Public replay, proof, and local resource ceilings | Exact plans admit public replay/proof and local generation: `P01-CHECKED-OK`, `P01-VERIFY-OK`, `P01-LOCAL-QUAL-OK` | Undersized plans: `ResourceExceeded / public-replay:resources / P01-REPLAY-004`; `ResourceExceeded / fs-proof-verification:resources / P01-VERIFY-004`; `ResourceExceeded / local-generation:{resources,public-resources} / P01-LOCAL-EXEC-003` | `negative/execution/public-replay-resource-ceiling.v3`; `negative/interface/proof-verification-resource-ceiling.v3`; local resource tests |
| Source, public fixture, oracle, and root separation | Exact build, projection, and copied-root replay pass | Source mutation rotates report then yields runner `verification-failure`; oracle mutation leaves the rebuilt report unchanged then yields `verification-failure`; claim-bearing fixture and mixed-root mutations yield `runner-failure` | source-, fixture-, oracle-, and root-perturbation report/replay tests |

This closes the repaired 13-obligation matrix at the finite P01 scope. It does
not claim that these rows are complete for another protocol family or for the
final durable architecture.

Separately, the current source scan classifies 203 declared diagnostic codes
exactly once:

| Class | Count |
|---|---:|
| Affirmative | 30 |
| Constructible driver | 144 |
| Internal invariant or fault | 15 |
| Environmental | 1 |
| Retired, dead, or redundant | 13 |

This closes the classification table only. The report currently executes 39
distinct codes across 45 public cases. Neither number shows that all 144
constructible diagnostics have executable drivers, that every driver reaches
its intended first boundary, or that every boundary discharges a design
invariant. Classification and live reachability remain a separate,
nonblocking hygiene queue. They are explicitly not the denominator for T3 or
Gate 6; newly discovered semantic obligations must instead be added to the
owned matrix with an exact positive control and first-boundary falsifier.

The current instrumented P01 suite fires 68 of 203 declared codes and leaves
135 unreached. This live reachability snapshot is consistent with, but does not
strengthen, the classification or matrix-closure claims.

## 7. Source-bound report and runner

The report binds exact public fixture bytes and canonical JSON content
separately. Component-specific manifests bind sorted role-tagged paths, byte
lengths, and SHA-256 content identities for the terms, provenance, semantic,
execution, Interface, Relations, Analysis, independent reconstruction,
diagnostics, report, and runner sources used by each claim. In particular, the
independent-reconstruction basis is exactly the executed package initializer,
closed-term, semantic, and separately coded reconstruction sources; it is not
presented as a semantically independent specification.

`build_report(repo_root)` accepts neither expected results nor private inputs.
`verify_report` checks the typed lanes, recomputes case and report Evidence
identities, rejects a run-time `overall_pass` field or private-sidecar path,
and performs an exact rebuild. Only after that oracle-independent build does the
runner load and compare the separately stored expected projection.

Root binding rejects a different checkout after imports have been resolved.
A copied checkout must execute its own copied runner and import its own copied
modules. Thirteen dedicated tests now verify report construction and strict
reconstruction, post-build expected-projection comparison, source identity
rotation, exact claim-bearing public-fixture refusal, oracle non-influence,
alternate- or mixed-root refusal, and replay from a minimal copied public
packet under an isolated working directory and `PYTHONPATH`. The separately
stored expected projection is refrozen and the source-bound runner comparison
passes for the repaired report identity.

## 8. Gate decision

`Closed here` means closed for this finite implementation and present evidence,
not adopted as durable v0 semantics or generalized into a theorem.

| Gate | State | Evidence and remaining work |
|---|---|---|
| 1. Source and toy boundary | `Closed here` | Exact public source ledger and fixture bindings; toy and non-conformance scope explicit. |
| 2. One construction | `Closed here` | Only v3 remains; the semantic path and separately coded byte path agree on the 448-byte query, `c=6,z=2`, and proof `1002`. The latter is diversity evidence under a basis that includes the shared semantic source. |
| 3. Shared Core and distinct variants | `Closed here` | Fresh and FS share one neutral Core and honest-prover contract but have distinct realization and Protocol identities; factorization is checked. |
| 4. Execution and verification | `Closed here` | Challenge-neutral begin, exact precommitment, state-sensitive challenge resolution, consuming finalization, read-only audit reconstruction, Fresh/FS public replay, shared verifier, exact FS proof ABI, projection, and resource accounting are tested. This establishes only modeled capability-flow order. |
| 5. Finite Analysis | `Closed here` | Exact counts `968`, `3,388`, `88`, and `968` are executed and published with theorem non-claims. |
| 6. Owned semantic falsification matrix | `Closed here` | Thirteen source- and architecture-bearing obligations have positive controls, minimal falsifiers, exact first outcomes/boundaries/codes, and maintained report cases or tests. All-code reachability remains a separate nonblocking hygiene queue. |
| 7. Relations | `Closed here` | Relation/instance admission, exact honest-prover correspondence, execution-issued Statement grounding, local satisfaction, acceptance, and Analysis applicability are separated. |
| 8. Identity and source | `Closed here` | Typed lanes, exact opaque runtime occurrences, private non-portability, exact public artifacts, complete component manifests including the independent semantic dependencies, and source/identity perturbation checks are present at the current finite scope. |
| 9. Cold replay | `Closed here` | The rotated public-only source-bound report and refrozen expected projection pass exact reconstruction, mixed-root refusal, and minimal copied-checkout replay under an isolated process environment. |
| 10. Cold adversarial review | `Closed here` | Separate read-only lifecycle and provenance reviews reran the original counterexamples, found and drove repairs for invalid-Fresh challenge installation and the omitted package initializer, then passed the final 69-test identity with no remaining P1/P2/P3 finding in scope. |

P01 is therefore retained at T3 for this exact finite implementation and
evidence boundary. This closes Phase B, not R2: it does not activate P02, adopt
the candidate as durable v0 semantics, or advance R3, R4, or Stage 4B.

## 9. Residual trust and non-claims

The retained evidence depends on Python's interpreter and standard-library
SHA-256/SHAKE implementations, operating-system file reads and metadata,
stable checkout bytes during evaluation, and the correctness of the finite
checker code. Source manifests identify what was evaluated; they do not prove
that source correct or that a runtime faithfully executed it.

Python constructor seals, object identity, and underscore-private issuers are
architectural API boundaries, not protection against hostile reflection in the
same process. The application-context fixture binds the value used by this
report; it does not authenticate an external caller or deployment context.

The staged API establishes only precommitment-before-challenge-resolution in
its modeled capability flow. It does not prove out-of-band challenge ignorance,
nonce uniformity or independence, Fresh sampling, historical artifact-authoring
order, or general adversarial non-anticipation. `ResponsePlan` is a closed
finite evaluator control, not a general strategy language.

P01 does not claim CFRG conformance, production security, discrete-log
hardness, witness or nonce confidentiality in the toy group, malicious-
verifier zero knowledge, proof of knowledge, ROM or QROM security, secure
composition, general Sigma support, compiler correctness, or architecture-wide
sufficiency. In the 11-element toy group, `Y` and `A` themselves reveal their
exponents by enumeration; removing secret-derived public identity does not make
the toy transcript confidential.

## 10. Reopening conditions

Reopen the selected repair if any of the following occurs:

1. prose, fixture, semantic evaluator, public verifier, or independent
   reconstruction produces different v3 query bytes or positive values;
2. construction admission or runtime derivation accepts omission, reordering,
   or mistyping of `Y` or `A`;
3. a non-public-coin source interaction acquires an admitted FS realization;
4. the modeled precommitment phase resolves a challenge, accepts caller-authored
   `A`, or permits any finalization input to replace the frozen response plan,
   semantic dependencies, or resource policies;
5. private material, a local reference, or a secret-derived digest enters a
   portable identity or public report;
6. equal-value, equal-content distinct-occurrence, mismatched-handle,
   cross-store, or cross-owner substitution authorizes private satisfaction or
   generation;
7. proof verification and public replay disagree on challenge, verifier check,
   or terminal;
8. public Statement grounding can be minted without a replay-checked execution;
9. source or public-fixture mutation leaves every dependent validation and
   Evidence identity unchanged;
10. expected results influence report construction or enter the report ID;
11. copied-checkout replay resolves code or fixtures outside the copy; or
12. a finalized precommitment can be consumed again, retried with a different
    Fresh challenge, or resurrected by qualification;
13. a component basis omits the executed package initializer, or the
    independent-reconstruction validation basis omits `terms.py`, `semantic.py`,
    or `independent.py`; or
14. finite results or diagnostic classification are promoted beyond their
    stated evidence strength.
