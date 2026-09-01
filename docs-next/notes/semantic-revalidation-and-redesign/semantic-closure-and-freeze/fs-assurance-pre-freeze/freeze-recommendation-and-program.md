# Fiat--Shamir Freeze Recommendation and Research Program

> **Kind:** Temporary decision and dependency-ordered execution program
> **Original audit baseline:** 808ec2d575da126f1d5cb22ad050ca52696dd75e
> **Synchronized freeze checkpoint:** a1585b2
> **Decision:** Preserve the no-rotation semantic freeze; route remaining
> assurance work through existing owners and Stage 4B gates
> **Authority:** None

## 1. Executive recommendation

The Fiat--Shamir research program finds no reason to reopen the semantic
ownership freeze recorded at a1585b2.

This is a conditional architectural conclusion:

- the canonical PIR construction remains structurally strong and explicitly
  noncryptographic;
- Interface and Relations close every Statement represented in the admitted
  Core, with application-level completeness retained as an external premise;
- Analysis can express the missing encoding, transition, sampler, process,
  source-property, theorem, and quantitative questions;
- OIR preserves the complete selected static contract;
- dynamic OIR, provider, parser, lowering, and deployment remain explicit
  Stage 4B activation gates; and
- classical ROM, BCS/RBR, duplex ideal-permutation, concrete-instantiation,
  and QROM results remain different profile families.

The freeze would need to reopen if a constructive counterexample shows that a
required obligation is unrepresentable, ownerless, multiply owned, erased by
identity/projection, or permitted to fall through to partial success. The
attack-first model and live audit found no such counterexample.

This recommendation does **not** approve a production Fiat--Shamir
implementation or assert a cryptographic theorem.

## 2. Concurrency and freeze chronology

The research began in the isolated codex/fs-assurance-pre-freeze worktree at
808ec2d, before the portfolio adjudication was committed. While the audit was
running, the design branch committed a1585b2, which:

- completed the holdout portfolio;
- froze the seventeen-profile candidate without identity rotation; and
- opened a separate post-freeze research program.

The isolated branch was then fast-forwarded to a1585b2. The FS findings are
therefore both:

1. a pre-freeze architecture pressure test against the 808ec2d semantic
   surfaces; and
2. a post-decision independent check that found no FS reason to rotate the
   a1585b2 freeze.

The main worktree's unrelated untracked finite-cover research was not read as
authority, modified, staged, or absorbed.

## 3. Candidate decision comparison

| Candidate | Strength | Decisive failure | Decision |
|---|---|---|---|
| Formally verify only the noninteractive verifier | Can strongly establish implementation refinement to a specification | Cannot establish specification completeness, source property, theorem applicability, primitive model, or external Statement closure | Reject as complete assurance; retain as L9 technique |
| Introduce one FSKernel/transcript authority | Centralizes one verdict and implementation hook | Collapses interaction, relation, property, projection, and realization ownership; turns nonclaims into ambiguous authority | Reject |
| Treat PIR strong-FS structure as security | Prevents many omission/order bugs early | Structural exactness survives a lossy adapter, biased sampler, or wrong theorem | Reject |
| Keep owner-separated assurance and add reusable Analysis profiles | Preserves exact responsibility and fail-closed outcomes; accommodates several theorem regimes | Requires explicit joins and more precise UI/reporting | Select |
| Defer every FS question until implementation | Avoids immediate profile work | Risks freezing away required coordinates and rediscovering semantics as backend accidents | Reject |
| Delay all FS research until semantic redesign completes | Avoids concurrent documents | FS pressure can identify ownership/identity defects only before or at freeze | Rejected by chronology; isolated pressure was the correct approach |

The selected design is not the most compact diagram. It is the only candidate
that classifies all sixteen attack families without granting one layer
authority to answer another layer's question.

## 4. Current go/no-go matrix

| Gate | Current evidence | Status | Decision effect |
|---|---|---|---|
| One owner for logical challenge chronology | InteractiveCore plus canonical FS derived actions | Go | Preserve PIR owner |
| Exact pre-draw prefix and negative mutations | DerivedPrefix/runtime receipt equality; K2 and focused controls | Go | No transcript-root redesign |
| Protocol-specific Last-Challenge dependency | Reduction required-publication law plus full Core chronology | Go, relative to accurately modeled dependency | Require source-specific reduction semantics |
| Complete represented Statement route | Interface exact binding set plus Relations whole selected surface | Go | Preserve owner split |
| Complete external application Statement | Must be supplied as closed manifest/correspondence premise | Conditional | Mandatory premise for strong/adaptive claim; no inference |
| Encoding and concrete transition binding | Exact targets are representable; no generic affirmative result | Conditional | No freeze block; blocks concrete security activation |
| Sampler and retry theorem compatibility | Precise AFK special case; reusable family absent | Conditional | No freeze block; blocks unsupported theorem use |
| Oracle-process and source theorem | Precise selected Analysis lane; per-family results incomplete | Conditional | Unsupported/CannotAnswer allowed; no silent claim |
| Static OIR preservation | Exact bounded canonical projection | Go for supported family | Preserve fields and exact equality |
| Dynamic OIR and RealizesOir | Explicit Stage 4B scaffold only | No-go for endpoint activation | Does not block semantic freeze |
| Duplex endpoint/theorem | Recognized sibling; theorem inactive and OIR Unsupported | No-go for duplex activation | Correct fail-closed state |
| QROM | Distinct required regime; no active profile | No-go for QROM claim | Classical result must not upgrade |
| Production deployment | No provider/parser/session/threat-model approval | No-go | No production claim |

The resulting decision is **semantic freeze go, security/runtime activation
no-go until the relevant conditional gates are affirmative**.

## 5. Freeze invariants to retain

The frozen candidate must continue to satisfy:

1. Protocol equals InteractiveCore plus a challenge interpretation.
2. Canonical FS derives frames and prefixes from the admitted Core; callers do
   not author transcript membership.
3. Runtime compares the complete transition-input receipt log with
   DerivedPrefix, not only a digest, state value, token, or required subset.
4. RequiredInfluence is derived and may be strengthened by exact
   reduction/module laws, never weakened by callers.
5. Every declared Statement binding enters its scope-opening prefix.
6. Interface and Relations compare an exact complete represented Statement
   domain.
7. PIR continues to disclaim injectivity, collision resistance, entropy,
   distribution, oracle behavior, theorem truth, parser, and provider
   correctness.
8. Analysis results name exact subject, adversary, experiment, source
   property, theorem, assumptions, query bound, loss, and target property.
9. OIR retains every selected FS coordinate; nontrivial rewrites use an
   explicit refinement profile.
10. Realization admits no candidate from build success or vectors alone.
11. Unsupported and CannotAnswer cannot become affirmative fallback paths.
12. Compiler and deployment policy consume qualified results without changing
    their meaning.

Violation of items 1--11 is a semantic reopening trigger. Item 12 is a product
and policy conformance trigger.

## 6. Immediate actions

### 6.1 At this checkpoint

Complete this package with:

- exact source ledger and hashes;
- theory and explanation chapter;
- attack/obligation matrix;
- live target and historical-finding audit;
- candidate Analysis and Stage 4B contract;
- bounded executable pressure instrument;
- aggregate validation with final exit status; and
- one committed isolated-worktree handoff.

### 6.2 Before temporary-package deletion

Route retained conclusions into durable owners:

| Retained conclusion | Durable destination |
|---|---|
| Application-level closed Statement premise | Interface/Relations contract or exact consumer-intake contract |
| PIR structural-versus-cryptographic nonimplication | Canonical FS nonclaim and Analysis source-view contract |
| Reusable encoding/transition/sampler/process questions | Analysis profile publication |
| Static-to-dynamic FS handoff | OIR Stage 4B entry contract |
| SSA/token lowering boundary | Target OIR/Realization profile, not PIR |
| Parser/end-of-input and provider qualification | Realization target contract |
| Classical/duplex/QROM separation | Analysis property-family routing |
| Claim gates and residual assumptions | Compiler/deployment policy |

The package itself remains temporary and should be deleted only after the
retained requirements are reconstructible from those owners.

### 6.3 Cross-lane review update

The design lane should submit the CLR-1 through CLR-3 reassessment to the
separate verification lane. Only that lane's agreed workflow may change those
rows from Open to Proposed-resolved, Rebutted, or deleted. This research
package supplies evidence but does not grade its own closure claims.

## 7. Large research program

The FS program is a vertical assurance track through the existing
[Post-Freeze Research Program](../../post-freeze-research-program/README.md).
It should not create a competing roadmap. Its work packages align as follows.

### WP0 — Baseline, source ledger, and architecture falsification

**State:** complete in this package.

Deliverables:

- exact current-owner reconstruction;
- sixteen-family attack taxonomy;
- ten-layer finite model with same-boundary controls;
- source snapshot hashes and live advisory locators;
- no-rotation decision and explicit nonclaims.

Exit:

- focused gate green;
- existing semantic gates show no regression;
- exact baseline and concurrent delta recorded.

### WP1 — Durable assurance-profile design

**Owner:** Analysis, consuming PIR and Relations views.

Tasks:

1. Specify the closed Analysis read manifest.
2. Publish reusable query-encoding, transition-binding, sampler, and
   oracle-process profile contracts.
3. Define exact joins with interactive source property, theorem validation,
   applicability, and quantitative transport.
4. Define profile variants for classical RO, BCS/RBR, duplex, QROM, and
   concrete instantiation.
5. Add exact outcome/failure behavior and independently reconstructible
   profile preimages.

Required falsifiers:

- copied or stale round table;
- missing owner view;
- wrong Statement boundary;
- encoding alias;
- sampler bias/exhaustion substitution;
- process-marginal substitution;
- source-property substitution;
- theorem-version or quantifier mismatch;
- omitted loss or residual assumption.

Exit:

- one finite positive subject;
- one nontrivial negative per subquestion;
- independent profile reconstruction;
- no shared upstream identity rotation unless an exact counterexample demands
  it.

### WP2 — Source-property and theorem validation lanes

**Owner:** Analysis.

Run independent lanes rather than one generic FS proof:

| Lane | Subject | Required result |
|---|---|---|
| AFK classical | Current selected three-move and later multi-round subjects | Exact source property, adaptive RO process, applicability, and loss |
| BCS/RBR | Commitment-compiled logical IOPs | Structural compiler correspondence plus source restoration/RBR and commitment assumptions |
| FRI-related | Exact FRI/WHIR/Circle subjects | Source-pinned RBR or alternative theorem; no transfer from family resemblance |
| Duplex | Exact sibling construction | Source theorem validation, codecs, salt, permutation/inverse model, applicability |
| QROM | Selected in-scope protocols only | Quantum adversary/query ABI, theorem validation, applicability, loss |
| Concrete hash/sponge | Named primitive/adapter profile | Explicit reduction, assumption, or bounded deployment residual |

Each lane may close as Affirmative, Negative, Unsupported, or CannotAnswer.
Only an exact Affirmative result enters a security claim.

### WP3 — Encoding and transition laboratory

**Owners:** Analysis for properties; independent verification for falsifiers;
Realization later for concrete providers.

Build a reusable adversarial corpus for:

- variable and fixed-length framing;
- optional fields and absent/default values;
- field and integer canonical ranges;
- endianness and sign;
- base/radix and limb conversion;
- modular reduction;
- floor/ceiling limb counts;
- high-bit preservation;
- padding and suffix ambiguity;
- rate-boundary behavior;
- empty and zero-length input;
- session, instance, namespace, and protocol separation.

Methods:

- exhaustive finite-domain alias search;
- property-based mutation and shrinking;
- SMT/finite-field counterexample search where exact;
- algebraic injectivity proofs for bounded adapters;
- differential checks against concrete providers;
- proof-assistant formalization for stable small codecs.

Exit is per adapter/profile. No aggregate “no collisions found” result is
promoted to cryptographic binding.

### WP4 — Dynamic OIR semantics

**Owner:** OIR.

Define:

- dynamic state and receipt types;
- absorb/squeeze/advance/decode operations;
- guard/path-sensitive state threading;
- retry, namespace, and failure semantics;
- challenge use and terminal behavior;
- proof-value and parser interface;
- explicit relation between static graph laws and dynamic executions.

Compare:

1. canonical exact dynamic equality for a reference interpreter;
2. a trace/refinement relation for rescheduling-free lowerings; and
3. a more general refinement profile only when an optimizer requires it.

Exit:

- one independent OIR interpreter;
- exact positive traces;
- stale-state, forked-state, reordered-effect, changed-namespace,
  changed-retry, and changed-failure mutations;
- no token or trace becomes source authority.

### WP5 — SSA and target lowering

**Owner:** Realization target profile, consuming OIR.

Implement state-threaded SSA:

- one SSA definition for each transcript state;
- exact typed frame values;
- explicit pre/post state for absorb and squeeze;
- challenge and acceptance values;
- explicit retry control flow;
- optional target-local linear token for effects;
- no ambient mutable transcript singleton;
- no caller-authored prefix list.

Compare:

- pure state threading;
- state plus effect token;
- region-scoped transcript effect;
- explicit provider call graph.

Selection should follow target semantics and checker simplicity. A token is
selected only when it makes an otherwise implicit effect order explicit.

Exit:

- target verifier and prover endpoints lower;
- exact query-index vectors pass;
- negative stale/fork/reorder/substitute mutations fail;
- token erasure or duplication is checked when tokens are used.

### WP6 — Parser, provider, and RealizesOir

**Owner:** Realization.

Tasks:

1. Publish proof ABI and canonical serializer/parser laws.
2. Require exact end-of-input and canonical range checks.
3. Bind every abstract transcript requirement to one concrete provider.
4. Define target-specific RealizesOir over queries, state, challenges,
   retries, failures, parser behavior, terminal results, and effects.
5. Select translation validation, verified producer correspondence, or an
   explicit trusted-producer residual.
6. Build differential and adversarial conformance suites.

Exit:

- an exact affirmative RealizesOir result for one target;
- independent parser and provider mutation failures;
- retained assumptions visible in the admitted realization.

### WP7 — Duplex endpoint activation

**Dependencies:** WP1 profile family, transcript/endpoint completion in the
post-freeze program, and source-theorem validation.

Tasks:

- close construction-material Plan and public-setup intake;
- own salt placement and proof-tuple parsing;
- relate wire codecs to transcript encoders;
- project and execute mutable duplex state;
- validate primitive and inverse-query model;
- qualify sampler/fiber behavior;
- activate theorem only after independent source validation.

An operational endpoint may precede a theorem result if labeled
structural-only. A theorem may not activate against a construction that differs
from its source.

### WP8 — QROM program

**Dependencies:** a concrete selected protocol and classical source mapping.

Tasks:

- define quantum query capability and resource model;
- validate the selected multi-round measure/reprogram theorem;
- map zkc logical query indices into its oracle model;
- carry ordered extraction and query-loss terms;
- mechanize theorem fragments where feasible;
- retain classical and quantum judgments side by side.

Exit:

- exact subject-specific QROM property or explicit Unsupported/CannotAnswer;
- no “post-quantum hash therefore QROM” shortcut.

### WP9 — Deployment and claim policy

**Owners:** Realization and consumer policy.

Define claim levels:

| Level | Minimum evidence | Permitted language |
|---|---|---|
| S0 structural | PIR construction plus represented Statement correspondence | Structurally admitted canonical FS |
| S1 model-qualified | S0 plus Analysis encoding, transition, sampler, process, source property, theorem and bound | Exact named property in exact ideal/concrete model |
| S2 endpoint-qualified | S1 plus OIR projection and RealizesOir | Exact target implements the qualified subject under retained assumptions |
| S3 deployment-approved | S2 plus ciphersuite, session, resources, parser, threat model, operations, and policy | Named deployment approved for named use |

Reports must never shorten S0 to “secure FS,” S1 to “implementation secure,”
or S2 to “production ready.”

## 8. Dependency graph

~~~text
WP0 audit
  |
  +--> WP1 reusable Analysis profiles
  |       |
  |       +--> WP2 theorem lanes
  |       +--> WP3 encoding/transition lab
  |       +--> WP7 duplex theorem intake
  |       +--> WP8 QROM
  |
  +--> WP4 dynamic OIR
          |
          +--> WP5 SSA lowering
                  |
                  +--> WP6 parser/provider/RealizesOir
                              |
                              +--> WP9 deployment policy

WP2 + WP3 + WP6 feed the S1/S2 claim join.
~~~

WP2 and WP4 can proceed concurrently after WP1 fixes their interfaces.
WP5 must not pre-author dynamic semantics that WP4 has not selected. WP7
depends on the separate transcript-completion package because the current OIR
correctly refuses duplex.

## 9. Worktree strategy

Separate worktrees are recommended when lanes need different build states or
edit overlapping semantic packages. The purpose is isolation and reviewable
handoff, not parallel edits to the same authority.

### 9.1 Recommended lanes

| Worktree | Scope | Typical paths |
|---|---|---|
| FS integration | Routing, package synthesis, durable owner handoffs | temporary FS package and owner indexes |
| Analysis design | WP1/WP2 profiles, theorem sources, Analysis evaluators | docs-next/analysis, Analysis profile publication/evaluation |
| Transition verification | WP3 independent alias/sampler/process falsifiers | evaluation instruments and private review results |
| OIR/Realization | WP4--WP6 dynamic semantics, lowerings, validators | docs-next/oir, docs-next/realization, target evaluators |
| Duplex/QROM research | Source validation and regime-specific prototypes | isolated notes/evaluation until owner intake is fixed |

Do not let design and independent-verification lanes edit the same evaluator
simultaneously. If one lane must hand a path across, name that exception and
have the other lane review it before the next checkpoint.

### 9.2 Checkpoint protocol

Every handoff should:

1. inspect status and recent log before writing;
2. name the exact baseline commit;
3. run the checks proportional to the changed layer;
4. commit all in-scope work;
5. report intentionally dirty paths, including none;
6. identify claims, nonclaims, Negative results, and pending final exits;
7. let the receiving lane reconstruct the result from sources and tests; and
8. merge only committed checkpoints.

Do not transfer an unexplained dirty worktree, copy files between lanes
without history, or absorb unrelated main-worktree changes.

### 9.3 When one shared worktree is better

Use one alternating shared worktree when:

- two sessions are sequentially refining the same profile;
- the next step needs the exact build state of the prior step; and
- each handoff can be committed and validated.

Use separate worktrees when:

- semantic design and independent falsification run concurrently;
- a long-running theorem/checker experiment needs a stable baseline;
- one target lowering changes build dependencies; or
- unrelated post-freeze packages are already dirty.

## 10. Validation ladder

Run checks in increasing scope:

1. file/schema parsing and focused unit tests;
2. owner-local profile/evaluator gate;
3. directly dependent K2/K3 gate;
4. semantic aggregate;
5. uncapped aggregate when the package reaches integration;
6. one bounded independent falsification pass;
7. final status/log/diff review and commit.

Every reported command must include final exit status. A long-running process
that emitted many passing cases and then disappeared is incomplete evidence
until rerun to final exit.

Validation output must label:

- implementation or model behavior;
- bounded positive/negative Evidence;
- qualified semantic judgment;
- theorem/source validation;
- target realization;
- deployment policy.

One label cannot stand in for another.

## 11. Program risks

| Risk | Failure mode | Mitigation |
|---|---|---|
| Assurance-kernel creep | One join starts redefining foreign-owner facts | Make the join consume exact capabilities/results; retain owner-specific failures |
| Test-to-theorem promotion | Finite aliases absent, so injectivity/security is claimed | Record domain and evidence kind; require proof or exact exhaustive finite domain |
| Citation-to-applicability promotion | A paper name fills source-property/theorem slots | Separate source validation and applicability results |
| Structure-to-binding promotion | DerivedPrefix is described as hash binding | Preserve PIR nonclaim and transition-binding profile |
| Token authority creep | Lowering token becomes transcript membership source | Derive state/token chain from OIR only; source comparison remains independent |
| Classical/QROM confusion | Primitive choice is used to upgrade the proof model | Distinct profile IDs and mandatory QROM premises |
| Duplex/canonical conflation | Headers/namespaces or raw codecs are silently substituted | Separate construction and endpoint profiles; exact source correspondence |
| Parser omission | Verifier math is correct but alternate/trailing proof bytes pass | Exact proof ABI, canonical parse, end-of-input, negative corpus |
| Wrong-spec verification | Refinement proves an incomplete source | Join independently qualified source, theorem, and application-manifest results |
| Concurrent work contamination | Freeze or post-freeze worktree absorbs unrelated edits | Isolated worktrees, committed checkpoints, explicit baseline delta |

## 12. Reopening conditions

Reopen the semantic freeze only on reproduced evidence that:

- an in-scope protocol cannot derive its challenge chronology from
  InteractiveCore without an authored transcript list;
- a theorem-relevant public fact cannot be represented as Statement, binding,
  message, Oracle interaction, reduction publication, module frame, or exact
  relation correspondence under the existing owners;
- exact query/encoding/sampler/process obligations cannot be stated in
  Analysis without moving foreign meaning;
- OIR identity/projection necessarily erases a semantic FS coordinate;
- Realization cannot define preservation without changing OIR/source meaning;
- fail-closed Unsupported/CannotAnswer semantics are impossible for a needed
  family; or
- a constructive protocol/source contradicts the canonical-versus-duplex
  family separation.

Do not reopen because a theorem is hard, a concrete provider is unavailable,
an endpoint is unimplemented, a profile returns Unsupported, or a deployment
cannot yet be approved.

## 13. Completion criteria

This research package is complete when:

- all seven English chapters and both machine-readable ledgers are present;
- the focused evaluator and selected existing gates finish with final status;
- source and attack ledgers parse;
- links, formatting, and whitespace checks pass;
- the a1585b2 synchronization is recorded;
- the branch has one committed checkpoint with no unexplained dirty paths; and
- the final handoff states the exact freeze result, residual gaps, and
  nonclaims.

The larger research program closes only when every WP1--WP9 package is
completed, explicitly deferred with reopening conditions, or routed into the
product roadmap; every retained meaning has one durable owner; every activated
claim has its complete evidence chain; and this temporary package can be
deleted.

## 14. Final decision boundary

The semantic redesign did not need to wait for Fiat--Shamir research, and the
Fiat--Shamir research did not need to wait for every post-freeze
implementation detail. Running the audit in an isolated worktree before and
across the freeze was the correct sequencing:

- structural/ownership counterexamples could still influence the freeze;
- no such counterexample was found;
- property and implementation gaps are now typed rather than forgotten; and
- post-freeze work can proceed against stable owner boundaries.

The resulting claim is deliberately narrow:

> The frozen architecture is adequate to host a complete Fiat--Shamir
> assurance program and structurally prevents the selected logical
> omission/order families relative to an accurately formed Core. It does not
> yet establish concrete Fiat--Shamir security or endpoint correctness.
