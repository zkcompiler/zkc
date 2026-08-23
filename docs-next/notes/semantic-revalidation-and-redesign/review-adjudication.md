# R1 Review Adjudication

> **Document kind:** Temporary falsification and adjudication record
> **Document state:** Active
> **Owner:** `project`, with the affected semantic owners
> **Authority:** None. This record classifies evidence and recovers design
> obligations; it selects no replacement model and changes no durable target.
> **Input boundary:** The two review inputs and live checkout frozen in
> [R0](baseline.md). Private prose is not reproduced here.
> **Disposition:** Absorb accepted decisions, invariants, rationale, and open
> work into exact durable owners, then delete this record.

## 1. Method and status language

Every review claim was reconstructed against the live target, current
specification, implementation, tests, and, where necessary, primary sources.
Reviewer conclusions and reviewer repair proposals were evaluated separately.

| Status | Meaning |
|---|---|
| `Confirmed` | The material claim survives direct reconstruction. |
| `PartiallyConfirmed` | A narrower defect survives, but the original scope, mechanism, or severity does not. |
| `Rebutted` | A live counterexample or authority rule defeats the claim as stated. |
| `Open` | The fact is real but whether it is a defect depends on a design decision or evidence not yet obtained. |
| `SupersededByBroaderFinding` | A more fundamental missing contract subsumes the local symptom. |

R1 is a classification gate, not a patch pass. `Confirmed` does not accept the
reviewer's proposed repair, and `Rebutted` does not prove that the surrounding
design is optimal.

## 2. Executive result

The selected architecture is coherent as a parametric schema, but it is not
yet an independently implementable v0. Its strongest structural separations
survive falsification without selecting their final representation:

- an explicit checked relationship between Fresh and Fiat--Shamir Protocols;
  the current same-Core construction remains a favored inhabitant, while
  related-distinct-Core and bisimulation-style constructions remain open;
- PublicEnvironment ownership of public challenges;
- explicit cycle breakers such as `BindConstructionSelfId` and
  `AnalysisGoalId`;
- Protocol, Interface, Plan, Relation, Analysis, and Compiler as distinct
  semantic subjects;
- semantic-basis versus validation-basis separation;
- property families without unsound subtype implications; and
- refusal to install one universal transition algebra.

The blocking issue is closure. Identity and checked relations depend on
regimes, values, algorithms, ABIs, totality evidence, transcript obligations,
strategies, grounding equations, and fact schemas that are named but not
constructibly defined. The model also lacks a distinct quantitative lane for
lossy identity projection. These are missing definitions and laws, not a
demonstrated contradiction in the core factorization.

## 3. Decisions that survive, with pressure still attached

| Decision | R1 result | Remaining pressure |
|---|---|---|
| `Protocol = InteractiveCore + ChallengeInterpretation`, with a checked Fresh/FS relationship | Structural factorization survives; literal same-Core sharing remains a favored hypothesis, not an R1 selection | Strong-FS construction must bind the statement and preserve the declared Fresh/FS semantic relation; R2 must compare identical-Core, related-distinct-Core, and bisimulation-style inhabitants. |
| PublicEnvironment owns declared public randomness | Survives, but is insufficient | Derive public-coin eligibility over the whole verifier-to-prover interaction and exclude verifier-private dependencies, not merely private randomness declarations. |
| `BindConstructionSelfId` | Survives as the current cycle-free inhabitant | State the acyclic self-binding invariant first, then compare this placeholder/instruction with any equally exact cycle-free construction. |
| `AnalysisGoalId` | Survives | Close the surrounding regime, proposition, and correspondence ABIs. |
| Semantic basis / validation basis | Survives | Prove exact read closure and adequacy for each consumer. |
| Interface / Plan split | Survives | Rename or split open structural coverage from closed executable realization. |
| No property subtype lattice | Survives | Instantiate the property families against causal executions and primary theorems. |
| No universal transition algebra | Survives | Extract only genuinely identical Foundation mechanisms. |
| Challenge prefix as a checked equality | Partially survives | Equality is exact only after required transcript sources are derived independently of author-selected observation bits. |

## 4. Blocking and high-impact findings

### 4.1 Fiat--Shamir and adversarial execution

| ID | Finding | Status | R1 judgment |
|---|---|---|---|
| FS-1 | Strong statement binding is syntactically impossible | `PartiallyConfirmed` | A public Statement value can be routed through an artificial Wire+Transcript `Message`, so literal impossibility is false. There is no faithful, first-class, complete statement-initialization law. Under the current same-Core inhabitant that law must preserve the Core; other Fresh/FS relations must state and check their corresponding preservation law. |
| FS-2 | Required prover material may be authored as Wire-only | `Confirmed` | Prefix folding is exact only for events already declared Transcript. No round, reduction, or oracle rule derives which earlier material a later challenge must bind. |
| FS-3 | The current segment-scoped statement rule has no target expression | `Confirmed` | The target has only initial invocation inputs and no dynamic statement occurrence or segment scope. Whether v0 needs global-static or adaptive statement scope remains open. |
| FS-4 | Challenge-domain uniqueness has no target law | `SupersededByBroaderFinding` | `SqueezeAndSampleRule` has no exact ABI or injective challenge discriminator, so a local string-domain rule cannot yet be stated meaningfully. |
| FS-5 | A non-public-coin Core can pass FS admission | `Confirmed` | The randomness algebra excludes a verifier-private `RandomnessDecl`, but not verifier-private behavior. A verifier may consume `PrivateToRole(Verifier)` invocation data and send a `PublicVerifierMessage` whose payload is Wire-only; FS maps it to `NoTranscriptAction`, and neither Core nor FS admission rejects the dependency. Public-coin eligibility must cover the full proof-interaction view. |
| FS-6 | Structural binding was intentionally moved wholly to Analysis | `Open` | No such decision is recorded. R1 recommends PIR own structural completeness and Analysis own theorem applicability, adversary models, and loss. |
| STRAT-1 | Execution consumes traces but has no causal prover strategy | `Confirmed` | A whole trace may correlate an early move with future randomness. PIR exposes no visible-history/legal-move relation and Analysis cannot ground its adversary classes in `ExecuteProtocol`. |
| STRAT-2 | No soundness statement can be written at all | `PartiallyConfirmed` | Abstract Analysis propositions can be written or imported. Endogenous soundness, knowledge, RBR, and state-restoration claims are not grounded in the Protocol execution semantics. |

The target evidence is concentrated in
[`protocol-model.md`](../../pir/protocol-model.md) and
[`fiat-shamir-and-composition.md`](../../pir/fiat-shamir-and-composition.md).
The current authoritative system already derives required proof prefixes and
has negative E211, E212, E214, and E216 cases in `docs/spec/kernel.md`,
`SealBattery.cpp`, `ReductionClosure.cpp`, and
`test/Transforms/pir-seal-invalid.mlir`.

The [CFRG Fiat--Shamir draft](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-fiat-shamir)
corroborates the missing engineering profile: the encoded instance is absorbed
after initialization and before prover messages, prior prover messages feed
later challenges, and omitting statement material is treated as weak FS. This
source supports the invariant; it does not by itself select zkc's exact event
algebra.

### 4.2 Identity and executable foundations

| ID | Finding | Status | R1 judgment |
|---|---|---|---|
| ID-1 | `SemanticRegimeId` has no construction or support law | `Confirmed` | Regime responsibilities are described, but no exact identity derivation, meaning, support, equality, compatibility, or declared static-versus-first-class lane exists. A first-class acquired regime additionally lacks authentication, admission, and lifecycle laws; a static regime instead lacks an exact version/change law. |
| ID-2 | `ClosedFiniteTerm` is undefined | `Confirmed` | Three durable pages repeat a one-line tuple, without grammar, typing, evaluator, equality, failure, kind signature, or resource discipline. |
| ID-3 | Declared totality evidence is not checkable | `Confirmed` | No evidence algebra, proposition, checker, trust root, identity effect, or rejection rule distinguishes a declaration from established totality. |
| ID-4 | ABI is wholly absent | `PartiallyConfirmed` | Some capability ABIs are explicit. Generic algorithm, Interface, Relation, proof, and endpoint uses are overloaded and inconsistently resolved. |
| ID-5 | `CanonicalSemanticValue` is undefined | `Confirmed` | Values enter identity, guards, invocation, Interface assignment, and Relations without domain-indexed membership, unique bytes/equality, or malformed-value behavior. |
| ID-6 | Claim/reduction/check contract routing is named but not defined | `Confirmed` | No typed equations connect producer, claim parameters, reduction inputs/outputs, side inputs, and check inputs. |
| ID-7 | View adequacy is circular or absent | `PartiallyConfirmed` | Source/consumer ownership and read closures exist. The exact coverage judgment, schema, missing/extra behavior, and checker inputs do not. |
| ID-8 | `SqueezeAndSampleRule` is wholly undefined | `PartiallyConfirmed` | Its role and failure seam exist, but its state transition, domain inputs, rejection/retry behavior, namespace, and canonical ABI do not. |

The identity architecture therefore remains a viable design family, but its
parameters do not yet determine bytes, evaluation, equality, support, or
admission. Foundation may own small common envelopes only after extraction;
PIR and Relations must continue to own their domain predicates.

### 4.3 Relations and quantitative loss

| ID | Finding | Status | R1 judgment |
|---|---|---|---|
| REL-1 | Committed-object grounding equations are absent | `Confirmed` | The operation names algorithms and says it checks binding-owned equations, but no typed operands, equation set, equality, or evaluation order exists. |
| REL-2 | Artifact fact/schema/selector vocabulary is absent | `Confirmed` | Fact and selector names are consumed without formation, canonical encoding, typing, selection, absence, multiplicity, equality, or adapter/profile compatibility laws. |
| REL-3 | `CorrespondenceRegime` is not constructibly reachable | `Confirmed` | Operations require an admitted regime, yet no body, ID, meaning, support, compatibility, or cold-replay path determines it. If retained as first-class, authentication, admission, and capability construction are missing; if made static, exact versioning and support are missing. |
| REL-4 | Public and witness exhaustive-image clauses are impossible | `PartiallyConfirmed` | Public exhaustiveness is a coherent stronger question over Statement ports. Witness exhaustiveness wrongly includes all private inputs and all prover-obligation outputs rather than an explicit relation-facing witness surface. |
| REL-5 | A bijective value bridge forbids the current lossy anchor projection | `PartiallyConfirmed` | The target never explicitly routes anchors through that bridge, so there is no internal contradiction. It has no separate directional projection algebra or loss channel despite Relations claiming anchor ownership. |
| REL-6 | Result binding establishes semantic result correspondence | `Rebutted` | The page explicitly disclaims that result. The real problem is that its reference-shape check duplicates binding admission and adds no meaningful later fact. |

R1 rejects the tempting repair “weaken every value bridge.” Whole-domain
semantic equivalence should remain a total bijection. A lossless embedding is
a second lane: injective in the forward direction, equipped with an exact image
predicate, and invertible on that image. A lossy projection is a third subject:
a one-way identity/transcript-material mapping with a collision relation,
occurrence accounting, and an Analysis-owned quantitative loss. The current
authoritative specification names the 256-to-216-bit anchor loss as
`Adv^CR[sha256-216]`, but its game quantifies byte preimages while the anchor
authority exposes only opaque values and no preimage rule. The target lacks the
projection contract, and the current reduction from anchor collision to the
named game is itself ungrounded.

### 4.4 Resource behavior and document closure

| ID | Finding | Status | R1 judgment |
|---|---|---|---|
| COST-1 | Canonical ROBDD guards put unbounded work in identity/admission | `Confirmed` | Fixed ordering gives canonicity, not compactness. Stored and derived diagrams can be exponential; implication and exclusivity add derived work. This is an operational v0 risk, not a logical contradiction. |
| DOC-1 | Durable Realization semantics depend on temporary notes | `Confirmed` | Durable Realization consumes `BelowOirPlanBasis` and `CheckedBelowOirPlanPlacement` without a complete durable owner. The inactive Stage 4B entry note adds provisional laws but itself defers the complete signature, outcome, and replay contracts. This is a cutover blocker while Stage 4B remains inactive. |
| DOC-2 | The durable manifest already violates exactly-once enumeration | `Rebutted` | The live manifest exactly enumerates all 37 durable pages. Semantic closure, not enumeration, is defective. |
| DOC-3 | The target is a second normative truth | `Rebutted` | Every `docs-next` authority boundary defers to `docs/`. |
| DOC-4 | The deletion contract relies on temporary-note preimages absent from Git history | `Confirmed` | At the R0 snapshot, all temporary notes were untracked and 73,206 lines under `docs-next` were untracked. This is preservation/process risk, not semantic authority; later working-tree counts are intentionally treated as fluid. |

Bryant's original [OBDD paper](https://people.eecs.berkeley.edu/~russell/classes/cs289/f04/readings/Bryant%3A1986.pdf)
confirms worst-case exponential representation. R3 must compare bounded ROBDD,
bounded syntax plus certificates, and derived-witness designs against real and
adversarial fixtures rather than choose from prose alone.

## 5. Claimed regressions against the current design

| ID | Claim | Status | R1 judgment |
|---|---|---|---|
| REG-1 | Replacing the token chain with ordinals is necessarily worse | `Open` | It trades MLIR's native SSA checks for representation-neutral canonical references. The net result must be measured with carrier round trips and invalid fixtures. |
| REG-2 | MLIR is useless in the target canonical layer | `PartiallyConfirmed` | “Locations are absent” is literally invalid because every MLIR operation has a location. The broader carrier/workbench value remains open and cannot be inferred from how much canonical trivia is erased. |
| REG-3 | `artifact_verify` has no target semantic home | `Confirmed` | The current row is implemented and identity-bearing; the target rejected its bundled meaning but has not replaced bounded imported verification with a closed semantic subject. |
| REG-4 | Loops, recursion, and dynamic events are absent | `PartiallyConfirmed` | The finite Core deliberately forbids them. Whether bounded unrolling is sufficient for v0, or a new recurrence/descent subject is needed, requires real witnesses. |
| REG-5 | No oracle-message object prevents native IOP/IOR/BCS modeling | `PartiallyConfirmed` | Finite unrolling can encode some interactions, so “no correspondence is possible” is too absolute. Native oracle publication, query access, BCS commitment/opening, and salting cannot be expressed faithfully. |
| REG-6 | Cost has no semantic owner | `Rebutted` | The producer owns raw observation meaning/completeness, Evidence owns provenance and uncertainty, Analysis owns typed cost inference, and Compiler owns objective comparison and selection. Concrete v0 cost profiles remain uninstantiated. |
| REG-7 | Cryptographic citations disappeared from durable Analysis | `Confirmed` | Analysis uses source-specific notions and theorem shapes but contains no external citations. Temporary research citations do not close a durable theorem ledger. |
| REG-8 | `Persistent` silently restores unrestricted contraction | `PartiallyConfirmed` | Persistence is explicit and the Core schedule is finite, so it is not an ambient structural rule. Property transport still needs an exact use-count/accounting law. |

The official [MLIR documentation](https://mlir.llvm.org/docs/Tutorials/Toy/Ch-2/)
confirms that every operation carries a mandatory location and also documents
the extensible operations, structural constraints, ODS, verification, and
rewrite infrastructure that may justify MLIR as a workbench carrier. R1
therefore corrects one impossible sentence but does not remove MLIR.

ArkLib's current [public repository](https://github.com/Verified-zkEVM/ArkLib)
explicitly models oracle messages, IORs, interactive BCS, and Fiat--Shamir as
separate layers. It is strong pressure for the oracle-object fork, not an
authority that zkc must mirror.

## 6. Method and process findings

| ID | Claim | Status | R1 judgment |
|---|---|---|---|
| M-1 | No evidence can end the research program | `PartiallyConfirmed` | Explicit exit gates and reopening conditions exist. The method lacks a first-class failed-gate artifact, independent witness requirement, and bounded decision rule; “no failure is not generative research” is not itself an infinite loop. |
| M-2 | Validation was entirely self-graded | `PartiallyConfirmed` | Requirement and verdict were often authored together and most audits lack independent executable witnesses. Frozen hashes still match; Stage 3 downstream-index drift was expected after Stage 4A, not a false historical CLEAN claim. |
| M-3 | The required real-protocol portfolio was never run | `Confirmed` | Scenario records contain synthetic models and incidental R1CS/Sigma text, but no actual FRI, KZG, Sumcheck, Schnorr, GKR, or recursion instantiation. The principal composition fixture declares no claims or reductions, so its claim-quiescence check is vacuous. Literal case-insensitive zero counts were overstated; the substantive absence is real. |
| M-4 | Existing oracle and ArkLib assets were not used to validate the target | `Confirmed` | The current-system conformance twin and pinned formal corpus appear in research notes but do not test clean-room target implementation or real inhabitants. |
| M-5 | Candidate comparisons were not equal-resolution | `PartiallyConfirmed` | Stages 1--3 were broadly balanced; Stage 4A was not. Earlier decisions legitimately constrain local candidates, but R3 must reopen them when the new evidence attacks those premises. |
| M-6 | The corpus duplicates its own target | `Confirmed` | Temporary target copies and promoted pages substantially overlap, while shared mechanisms remain unextracted. R5 must absorb conclusions rather than retain research narration. |
| M-7 | Governance is internally inconsistent | `Confirmed` | At amendment time governance required every individual temporary note to appear exactly once, but the inventory had nine package rows for the eighty then-existing disposable notes; nineteen of thirty-seven durable pages used states outside the declared state vocabulary; and the guard checked only tracked public-doc paths, so it did not preserve the untracked incubation record. The durable manifest itself remained exact. |
| M-8 | The target is disconnected from implementation planning | `PartiallyConfirmed` | Four gap ledgers contain 2,216 lines and substantial current correspondence. Actionable migration/work chunks are absent, but that deferral is intentional while the ideal model remains unsettled. Feasibility evidence must not become a compatibility constraint. |

The R0 snapshot contains 51,934 temporary lines and 23,833 durable lines.
Temporary volume is acceptable only as an actively shrinking research record;
it is not a defense of the durable surface. The durable target is already
larger than the current specification and repeats lifecycle, outcome, identity,
and replay machinery. R5 will normalize by semantic ownership, not by arbitrary
line quotas.

The review's authority-banner and non-claim-density measurements are useful
signals of defensive, process-heavy writing, but they are not semantic
failures. Their final disposition is `Open` until R5 tests whether a cold reader
can reconstruct exact claims and non-claims from a substantially smaller
durable surface.

## 7. Prior-art adjudication

| Claim | Status | R1 judgment |
|---|---|---|
| Protocol-level IR vocabulary does not exist elsewhere | `Rebutted` | Wizard-IOP and its compiler layers are a direct counterexample to that broad framing. |
| Wizard-IOP proves zkc's architecture unoriginal | `Rebutted` | The source establishes a protocol/compiler system, not the absence or presence of zkc's exact stable-identity, independent-admission, Fresh/FS-pair, or Interface/Plan/Relation contracts. Those comparative claims require R3. |
| Wizard-IOP has run in production since 2023 | `PartiallyConfirmed` | Linea's own 2023 launch and prover explanations establish operational use of the prover architecture. They do not establish uninterrupted deployment of one unchanged internal Wizard layer, so the stronger continuity claim remains unproven. |
| The durable landscape and Analysis citation trail are too thin | `Confirmed` | Relevant Wizard-IOP, transcript, IOR, formalization, and theorem sources exist only in temporary or private research, while durable Analysis has no source ledger. |

The [Linea prover paper](https://eprint.iacr.org/2022/1633) describes
Wizard-IOP, Arcane and UniEval compiler stages, PIOPs, and recursive proof
compression; the [live protocol tree](https://github.com/Consensys/linea-monorepo/tree/main/prover/protocol)
contains dedicated compiler, query, and wizard modules. Linea's own
[prover explanation](https://linea.build/blog/the-linea-prover-for-a-very-smart-high-schooler)
and [2023 mainnet-alpha announcement](https://linea.build/blog/the-next-step-in-lineas-journey-mainnet-alpha-is-here)
support bounded operational-use claims. This narrows the external framing. It
does not settle zkc's precise contribution claims or prove continuity of a
particular internal layer.

## 8. Current-system findings checked during review

These findings concern the authoritative shipped design and implementation,
not the ideal target. They are recorded for routing only; R1 makes no code or
current-spec change.

| ID | Status | Independently reconstructed finding |
|---|---|---|
| CUR-1 | `Rebutted` | `ArtifactVerifyOp` is diagnosed with E235, marks the walk invalid, and returns before `deriveObligations`; a negative test pins graceful refusal. The missing derivation case remains relevant only under CUR-8 if the event later becomes projectable. |
| CUR-2 | `Open` | PIR labels are excluded from PIR identity while OIR `statement_labels` are deliberately identity-bearing in the current specifications. That current asymmetry is not a reconstructed inconsistency; whether a replacement architecture should retain it, and under what explicit naming contract, remains open. |
| CUR-3 | `Confirmed` | The normative exhaustive domain-tag list omits live value-profile, relation-contract, and compiler configuration tags; generic compiler tags in the specification also do not match the implementation vocabulary. |
| CUR-4 | `Confirmed` | In the configured-compiler `ExactRef` lane, the specification describes an object while C++ and the Python twin encode an array; parity between implementations is not conformance to that normative row. |
| CUR-5 | `Confirmed` | The canonical challenge row in `carrier.md` contains both a label and a scalar tail that the encoders omit or shape differently under the same document's label-exclusion rule. |
| CUR-6 | `Rebutted` | The seven source-envelope sections and six sealed-entry families are distinct, explicitly enumerated subjects; their different counts are not an inconsistency. |
| CUR-7 | `PartiallyConfirmed` | Preprocessed-index terminology is stale or ambiguous after value-profile and seal evolution. The checked evidence does not establish a runtime unsoundness. |
| CUR-8 | `Confirmed` | `COV_obl` is a normative seal-derived conjunct, but `SealBattery::run` never derives it; only `pir-project` does, and that derivation switch has no `ArtifactVerifyOp` case. |
| CUR-9 | `Confirmed` | `BoundRelationAnchorCount` hard-codes the field name `contract`, so it misses the current R1CS relation's `a`, `b`, and `c` anchors; the test covers only the contract-shaped case. |
| CUR-10 | `Confirmed` | The named `sha256-216` game quantifies byte preimages, while current anchor authority treats anchors as opaque and supplies no anchor-preimage rule. The current quantitative term is therefore not yet grounded in the asserted anchor-collision reduction. |

These belong in the current implementation/specification gap process. Fixing
them is not authorized by this architecture-review cycle unless separately
requested.

## 9. Secondary identity and checked-relation patterns

| ID | Claim | Status | R1 judgment |
|---|---|---|---|
| S-1 | `composition_context` reaches FS challenges without sufficient justification | `Open` | The mechanism is real and may be semantic domain separation or provenance leakage. A replay threat, theorem premise, or interoperability counterexample must decide it. |
| S-2 | `FSConstructionMaps` is information-free and cannot fail | `PartiallyConfirmed` | Maps are deterministic consequences and should probably be derived. Malformed or mismatched proposals can fail, so the checker is not logically vacuous. |
| S-3 | `PlanRealizes` can only return positive | `Rebutted` | It has real coverage, map, domain, read, and randomness negative cases. An all-hole plan may pass because the result explicitly means structural coverage, so the name and hole frontier overclaim. |
| S-4 | `ApplicationBinding` enters identity and has no consumer | `Rebutted` | Relations consumes it to ground exact application-event inputs. Stable reference, duplicate, and sequence-order laws remain missing. |
| S-5 | `external_outcomes` sequence order changes identity without changing behavior | `Confirmed` | The semantics is terminal-keyed and no consumer observes enumeration order. Use a keyed collection or justify observable order. |
| S-6 | Migration size should decide the target model | `Rebutted` | Migration is evidence for feasibility and staging, never a constraint on selecting the ideal semantics. It is measured after semantic selection. |

The useful cross-cutting diagnosis is conditional, not universal:

1. an identity field or ordering needs an authorized observation, stable
   reference namespace, or stated domain-separation invariant; and
2. a semantic affirmative/negative relation needs an exact postcondition plus
   a meaningful admitted negative; deterministic derivation or conformance may
   instead reject a typed mismatch or malformed certificate without pretending
   that the constructor's canonical output was an authored semantic choice.

`ApplicationBinding` and `PlanRealizes` show why those are tests rather than
automatic convictions.

## 10. Review repair proposals are hypotheses

R1 does not adopt the proposed minimal patches mechanically. In particular:

- making `ObservePublicValue` Transcript-visible does not by itself prove
  exact Statement coverage or preserve the Fresh Core interaction;
- adding a `ProverStrategy` name without visible histories, legal moves,
  causal generation, and an auditable execution/replay relation would not
  close causality;
- weakening a whole-domain semantic-value bijection would conflate full
  equivalence, lossless embedding, and lossy commitment projection;
- adding oracle messages without query semantics, commitment/opening
  transformation, and composition would create a name, not an IOR layer;
- retaining a ROBDD with an undocumented practical-size assumption would not
  create a portable admission contract; and
- replacing balanced alternatives with one full proposal and one selectively
  developed opponent is itself only a process candidate; comparisons must be
  equally resolved at every fact capable of changing the decision, not equally
  long by quota; and
- amendment-only migration would let the current implementation constrain the
  ideal target, contrary to the cycle's scope.

Each is an R2/R3 candidate only after executable pressure establishes the
required invariant and negative boundary.

## 11. R1 conclusion

The external review was highly productive and its central closure diagnosis is
valid. It also contains material overstatements: literal FS inexpressibility,
impossible public correspondence, manifest failure, two normative truths, no
cost owner, vacuous Plan/Application checks, and historical audit drift.
Correcting those overstatements strengthens the redesign because the next
stage can attack exact missing contracts rather than repairing claims the live
model never made. The cold validation also reversed the internal rebuttal of
non-public-coin admission with a concrete verifier-private-data counterexample;
that reversal is part of the gate result, not an editorial footnote.

R1 does not select a revised semantic model. Its output is the companion
[invariant ledger](invariant-ledger.md), the open redesign forks, and a bounded
independent validation request. The first cold pass and its required
corrections are recorded in the [validation outcome](validation-outcome.md).
R2 remains inactive until a fresh follow-up validates the amended record.
