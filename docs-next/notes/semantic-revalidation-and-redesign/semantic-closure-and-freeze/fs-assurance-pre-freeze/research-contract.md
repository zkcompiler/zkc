# Fiat--Shamir Assurance Research Contract

> **Kind:** Temporary pre-freeze research contract
> **State:** Complete; synchronized to `a1585b2`; all selected validation
> components have final exit status
> **Authority:** None

## Decision question

Does the selected semantic redesign represent Fiat--Shamir in a way that:

1. structurally prevents the major transcript-omission, ordering, and weak-FS
   bug families;
2. can state every additional encoding, concrete-transition, distribution,
   theorem, projection, and realization obligation needed for a justified
   security claim;
3. fails closed when one of those obligations is absent;
4. remains compatible with BCS/IOP, multi-round, duplex-sponge, and QROM
   theorem families without conflating them; and
5. should influence the semantic freeze now rather than be deferred until
   after a redesign is fixed?

## Fixed baseline and concurrency boundary

The research branch is `codex/fs-assurance-pre-freeze`, formed from commit
`808ec2d575da126f1d5cb22ad050ca52696dd75e`. The separate worktree prevents the
program from absorbing uncommitted portfolio-adjudication work in the primary
checkout. During the audit the design branch committed the no-rotation freeze
decision at `a1585b2`; this isolated branch fast-forwarded to that checkpoint
without absorbing the primary checkout's unrelated untracked post-freeze work.

This package may edit temporary research notes, bounded falsifiers, and their
routing indexes. It does not activate Stage 4B, rotate a published profile,
change a durable semantic owner, or claim current compiler/runtime support.

## Candidate architectures

The review compares five shapes:

1. **Verifier-only verification.** Formally verify the noninteractive verifier
   and treat that result as complete FS assurance.
2. **One FS authority kernel.** Add a transcript/token/root owner that controls
   interaction, encoding, state, theorem, projection, and implementation.
3. **PIR-only strong FS.** Treat exact `DerivedPrefix` and
   `RequiredInfluence` as sufficient security evidence.
4. **Owner-separated assurance chain.** Keep structural semantics in PIR,
   correspondence in Relations, properties and theorems in Analysis, static
   preservation in OIR, and provider/execution conformance in Realization.
5. **Implementation-first deferral.** Freeze without recording the assurance
   chain and rediscover requirements during Stage 4B.

Candidate 4 is selected. Candidate 1 proves too little when the specification,
codec, theorem assumptions, or primitive model is wrong. Candidates 2 and 3
collapse different judgments into one authority. Candidate 5 risks making
Stage 4B requirements appear as accidental implementation details after the
semantic interfaces are already frozen.

## Research method

The program uses four independent evidence modes:

1. **Primary-source reconstruction.** Pin exact papers/drafts; separate theorem
   statements, prerequisite notions, concrete bounds, implementation guidance,
   and open limitations.
2. **Live target audit.** Read the durable PIR, Relations, Analysis, OIR, and
   Realization owners and their profile-publication paths, not only project
   summaries.
3. **Attack-first falsification.** Pressure each candidate with weak FS,
   Frozen Heart, last-challenge, missing-message, ambiguous-encoding,
   variable-length sponge, limb/radix/truncation, sampler-bias, BCS-premise,
   QROM-upgrade, parser, and lowering mutations.
4. **Claim-lattice review.** Keep implementation behavior, finite evidence,
   semantic judgment, theorem truth, cryptographic property, and deployment
   approval distinct.

## Evidence levels

| Level | Meaning | Permitted conclusion |
|---|---|---|
| Source snapshot | Exact source bytes or a dated live incident page | What the source states at that snapshot |
| Structural reconstruction | Owner documents agree on types, identity, lifecycle, and qualified outcomes | The target can represent/refuse the named structure |
| Bounded positive control | One finite model accepts the selected case | The selected finite case is formable in that model |
| Bounded counterexample | Two distinct selected inputs alias or one mutation is accepted/rejected incorrectly | The candidate property is false for that finite construction |
| Theorem-source validation | Exact proposition and proof are independently validated | The source theorem may enter applicability checking |
| Qualified Analysis judgment | Exact premises, model, theorem, loss, and target are joined | Only the named property for the named subject/regime |
| Projection/realization result | Exact target-specific preservation/conformance checker is affirmative | Only the named target relation under retained assumptions |
| Deployment approval | Consumer policy accepts the complete evidence/assumption set | Only the named deployment and threat model |

No lower level is silently promoted to a higher one.

## Required pressure cases

The executable package must include at least:

- an authored weak schedule that is internally exact yet fails closed external
  Statement correspondence;
- omission, duplication, substitution, and reordering of typed prefix frames;
- omitted final proof elements before a batching challenge;
- ambiguous frame concatenation;
- length-free trailing-zero aliases and high-bit truncation;
- exact-uniform, biased, and conditional-with-failure sampler controls;
- session, instance, and namespace separation;
- static OIR field substitution;
- weak realization query indexing and incomplete parser consumption;
- a BCS label without the required interactive source property;
- a formal-verifier result without theorem and process premises; and
- refusal to promote a classical ROM result to QROM.

Every negative has a same-boundary positive control. Advisory-shaped finite
witnesses must not be labeled exploit reproductions.

## Exit criteria

The package closes when:

1. the primary-source ledger and attack taxonomy are complete;
2. every assurance layer has one current or proposed durable owner;
3. each historical cross-lane finding is closed, narrowed, or retained with an
   exact blocker;
4. an executable falsifier demonstrates at least one cross-layer nonimplication;
5. the freeze recommendation distinguishes semantic blockers from Stage 4B
   activation blockers;
6. the focused evaluator, existing K2/K3 gates, and appropriate aggregate
   validation complete with final exit status;
7. the branch is synchronized with, or explicitly delta-scoped against, the
   portfolio freeze checkpoint; and
8. a committed handoff names all residual assumptions and nonclaims.
