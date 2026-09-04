# F0-V3C: entry contract for the finite canonical-framed subject and its executor

> **Kind:** entry contract (formal-assurance research, Fiat--Shamir family)
> **State:** Proposed 2026-09-04 as the prerequisite of the first Fiat--Shamir
> provider interpretation; it produces the executable reference that the
> family pages have only as static determinacy today.
> **Authority:** None. A contract fixes what a lane must deliver and what a
> result may claim; it changes no owner page.

## 1. The question

Can the migrated canonical-framed owner text
(`docs-next/pir/fiat-shamir.md`) be executed, not only projected: does one
admitted transcript construction over the finite Schnorr Core form an FS
Protocol whose every honest run and every verifier input is generated and
replayed under Sections 4, 6, 7, 9, and 10 of that page by two independent
paths, with the six-lane outcome partition and the receipts the page states,
and with no choice left to the executor?

Today the family texts are covered by the F0-V3 and F0-V3B packages, which
project view bodies and check their determinacy, and by the holdouts, which
adjudicate carriers statically. The k2 reference instrument executes
Fiat--Shamir runs, but over its own witness-local profiles and its own
SHA-256 fixture, not the migrated text. Without an executor of the migrated
text there is no reference for a provider interpretation of a Fiat--Shamir
Protocol, and no evidence that the frame, namespace, draw, and receipt laws
compose into runs at all.

## 2. The subject

- The finite Schnorr Core already admitted by the target-core package
  (`evaluation/formal-source-target-core-f1r1b`, Core
  `zkcidv0:pir.interactive-core:0e767c0c...`, statements, witnesses, and
  nonces in the field of three elements), so that the FS Protocol shares its
  Core with the Fresh Protocol the provider interpretations use.
- One `TranscriptConstruction` over that Core: transcript state and byte
  types, an initial state, `absorb`, `squeeze_bytes`, and `advance_state` as
  `PIRAlgorithmUse`s over portable algorithms in the Foundation's language
  (Section 5 of `docs-next/foundation/executable-foundations.md`: a
  canonical term over admitted primitives with an evaluation contract),
  one `pir.fs-application-domain` declaration, the sampling-exhausted
  failure, and one `ChallengeRule` for the single challenge with
  `draw_bytes`, `maximum_draws`, `accept`, and `decode`. The transition
  suite may be a toy, chosen so that its meaning is fixed by its terms
  alone; it need not be a cryptographic hash, and the lane records that a
  toy suite is a correspondence instrument, not a security instrument.
- The FS Protocol formed by `AdmitFS` (Section 9.1) and the checked
  same-Core construction against the Fresh Schnorr Protocol (Section 10).

## 3. What the lane delivers

A package `evaluation/formal-source-fs-runtime-f0v3c/` with a note
`f0v3c-fs-runtime.md`, in the shape of the earlier formal-source packages:

1. **Admission.** The construction and the FS Protocol admitted under the
   migrated text with their identities frozen; the same-Core construction
   checked with its `StructurallyConstructed` conclusion and identity maps.
2. **Execution.** An executor of Section 9.2 that drives the Core engine
   with the resolver's hooks: the initialization and condition frames of
   Section 4 in the stated order, the exact `ChallengeNamespace` of Section 6,
   the draw loop of Section 7 with its `DrawReceipt`s, the `FSChallengeReceipt`
   on success, and the `FSSamplingFailureReceipt` inside an
   `InterpretationFailed` record on exhaustion. Every honest run over the
   finite domain (statement, witness, nonce) and every verifier input over
   the finite transcript domain is executed; the completed records and the
   lane in which each run ends are frozen.
3. **Replay.** Section 9.3 as the second path, implemented independently of
   the executor, comparing the closed `CompletedProtocolRecord` variant with
   exact field exhaustion; both paths must agree on every run.
4. **Views.** The `CanonicalFramedExecutionViewBody` of the FS Protocol and
   the construction views the F0-V3B package projects, reproduced from the
   admitted subject and compared with that package's projection where the
   subjects coincide.
5. **Outcome partition.** The six lanes as the page states them, with the
   count of runs per lane; whether sampling exhaustion occurs on the domain
   is a measured fact, not a parameter choice hidden in the suite; if it
   occurs, the runs are frozen in the interpretation-failure lane with their
   receipts.
6. **Derivation function.** The exact function from (challenge, statement,
   transcript prefix) to the derived challenge value or exhaustion, exported
   as a table over the finite domain, because the provider interpretation
   that follows instantiates ArkLib's abstract Fiat--Shamir oracle with it.
7. **Findings.** One frozen finding per clause with a stable code prefixed
   `F0V3C`; every place the page underdetermines the execution is a
   `CannotAnswer` with the exact section and line and a proposed delta,
   never a silent choice.

## 4. Independence and trust

The executor and the replay path share only the Foundation's canonical
encoding and the admitted portable algorithms; the frames, namespaces,
receipts, and lane decisions are implemented twice. The residual trust items
are the Foundation's K1 encoding, the portable-algorithm evaluator, and the
finite domain's size.

## 5. Acceptance

`Affirmative/F0V3C-A-FS-RUNTIME` only when admission, execution, replay, and
the view reproduction hold on the whole finite domain with both paths in
agreement and no underdetermination recorded; `CannotAnswer` with the exact
clause otherwise. The result establishes that the migrated canonical-framed
text executes deterministically on one finite subject. It establishes no
security of the transition suite, no theorem, no provider correspondence,
and no statement about the duplex-sponge profile, whose executor is a
separate contract with the same shape.

## 6. What follows

F2-O4, the first Fiat--Shamir provider interpretation: ArkLib's
`Reduction.fiatShamir` of the reduction the F2-O3 round generated, with the
abstract `fsChallengeOracle` instantiated by this contract's derivation
function, compared against the frozen runs on the same finite domain, with
the provider's declaration derived from its execution model as the ArkLib
round did. It cannot start before this contract's derivation table exists.
