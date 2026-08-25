# Semantic Kernel Closure Audit and Execution Plan

> **Document kind:** Temporary architecture audit and execution control record
> **Document state:** Active
> **Owner:** `project`, coordinating `foundation`, `pir`, `relations`, and the
> minimal consumer seams
> **Authority:** None. This page neither ratifies target semantics nor changes
> the authority of `docs/`, Stage 4B, or any implementation.
> **Audited snapshot:** `docs/semantic-redesign` at `d91ce6b`, 2026-08-25
> **Disposition:** Absorb the selected freeze boundary and work order into
> durable project owners, then delete this page with the revalidation package.

## 1. Verdict

The redesign has a credible and sufficiently researched **architectural
spine**. Open-ended architecture discovery should stop. Work should now move to
bounded semantic closure, real-protocol pressure, and implementation-facing
falsification.

The exact PIR semantic kernel is **not yet frozen or independently
implementable**. Its central factorization has not been contradicted, but
several definitions, laws, regressions, and consumer seams remain open.
“Stage 1--4A complete” records historical research-package selection at the
then-current resolution; it does not mean that the integrated kernel is closed.

The execution model should be a small global skeleton followed by
dependency-ordered vertical slices. The current `docs/` and implementation
remain authoritative until an explicit cutover.

**Current execution position:** K0 completed on 2026-08-25 and bounded K1
executable foundations completed on 2026-08-26. K2 Protocol/FS closure is
next; the integrated kernel is not frozen. The R2 protocol-witness track
remains an evidence source; a P02 probe may inform an earlier question, but
P02 cannot close its portfolio gate before K1--K3 establish the substrate it
is meant to test. Stage 4B remains inactive.

## 2. Stable architecture spine

Carry these choices forward unless a named falsifier fires or a real protocol
cannot inhabit them without semantic loss, authority duplication, or an opaque
escape:

1. Protocol meaning is centered on a finite verifier-observable
   `InteractiveCore`, not on one compiler, proof container, MLIR pass graph, or
   prover implementation.
2. `Protocol = InteractiveCore + ChallengeInterpretation` separates the
   interaction from Fresh or Fiat--Shamir challenge realization. A checked
   Fresh/FS relation is required; literal same-Core sharing remains the leading
   inhabitant rather than an axiom.
3. `ProtocolInterface` fixes external meaning and `ProverPlan` supplies prover
   construction choices without changing verifier-visible Protocol behavior.
4. Authentication, admission, execution, Relations, property Analysis,
   compilation legality, OIR projection, Realization, and Evidence reliance are
   distinct judgments with no downstream authority backflow.
5. Source domains export narrow immutable views; consumers own their additional
   propositions. No universal fact root or transition algebra substitutes for
   domain-owned checked relations.
6. Portable semantic identity is independent of process state and rich MLIR
   authoring structure. MLIR remains a workbench and canonical carrier, not the
   abstract semantic model.

No additional broad survey is required to justify this spine. Research from
this point is question-driven and may revise the exact algebra while preserving
these separations.

## 3. Integrated closure audit

Every executable falsifier below must include an unchanged same-boundary
positive control, as required by the
[non-regression baseline](invariant-ledger.md#7-target-owes-shipped-non-regression-baseline).
A pure reopening condition is not itself a closure test.

| Area | Result | Closing owner | Executable falsifier or gate |
|---|---|---|---|
| Subject and authority factorization | Coherent | Project and PIR | Reopen if a bounded protocol needs ambient state, a shadow Protocol schema, or Interface/Plan variation changes a Protocol-only observation. |
| Regime, value, portable-function ABI, typed-failure, totality, and bounded-evaluation foundations | K1 standalone closed; K3 extraction and integration open | Foundation owns the selected substrate; PIR, Relations, Analysis, and OIR own their exact semantic bodies and use-site admission | The independent identity/value oracle must agree with the K1 reference model, while the term evaluator exercises function steps, typed failures, totality, and bounds. Reopen K1 if exact law/vector parity breaks or a consumer requires an owner-specific escape or general virtual machine. K3 must demonstrate two aligned consumer extractions; a second term evaluator remains independent-freeze evidence rather than credited K1 evidence. |
| Core execution | Open | PIR execution structure; Analysis strategy classes | An honest online execution and replay must agree, while a trace whose early prover move depends on a future challenge must replay but fail strategy generation. |
| Strong Fiat--Shamir structure | Open regression | PIR structural admission | Run [J1](invariant-ledger.md#71-semantic-guarantees): target acceptance of an omitted/late Statement, Wire-only required proof message, wrong prefix, reused challenge namespace, or verifier-private influence fails the gate. |
| Fresh/FS relation | Promising, not frozen | PIR construction; Analysis theorem applicability | A native Fresh/FS FRI or IOR pair must preserve one declaration through structural maps; a mismatched map, context, or related-Core claim must fail at the declared relation rather than disappear into Analysis. |
| Core algebra and extension model | Open selections | PIR | Run each registered Core/extension fork on a shared substrate whose output can differ; the unchanged supported base vocabulary is the positive control. A locally supported extension that rotates unrelated meaning, an unknown constructor that admits, or a rejected control fails the gate. |
| Relations boundary | Open co-design seam | PIR surfaces, Relations semantics, Analysis loss | A relation-bound R1CS/AIR or Sumcheck fixture must distinguish Statement, Witness, private nonwitness, grounding, lossless bridge, and priced lossy projection; an opaque carrier escape or unpriced projection fails. |
| Analysis boundary | Partially stable | Analysis, reading PIR-owned views | Instantiate one primary-source FS theorem over causal target execution and one relation-bound property; wrong model, strategy, correspondence, hypothesis, or loss occurrence must change the qualified result. |
| OIR boundary | Inactive but relevant | PIR source obligations; OIR projection relation | Project both roles, then drop one required effect, add phantom provenance, change a discharge family, and exercise the bounded imported-verification shape with typed `Unsupported` where projection remains unimplemented. Local validity must not survive as source-relative correctness. |
| Compiler, Realization, and Evidence | Deferrable | Their later domain owners | They remain outside kernel closure unless a concrete feasibility/cost counterexample shows that a frozen source fact is insufficient; no downstream result may add Protocol meaning by backflow. |
| Documentation and protocol evidence | Open | Project governance and exact evidence producer | Hide `notes/`, run manifest/link/symbol-owner reconstruction, and cold-implement the frozen kernel; separately complete the differentiated protocol portfolio at its assigned strengths. Any missing definition, hidden dependency, or self-authored success fact fails. |

No contradiction found in this audit invalidates the central factorization.
The failure is closure: some exact-looking identities and judgments depend on
symbols whose formation, evaluation, comparison, cost, or read law is absent.
The current target is a detailed candidate schema, not yet a complete v0
specification.

The audited evidence instruments remain reproducible: P01 passes 69 tests and
its source-bound replay, while the repaired FRI-grinding witness passes 39 tests
and its expected semantic replay. The live coverage instrument nevertheless
classifies only 3 of 21 tracked invariants as boundary-covered, with 13 partial
and 5 uncovered. That authored coverage map is a review aid rather than a
semantic verdict, but it independently supports the freeze decision above.

## 4. Kernel closure boundary

The [invariant ledger](invariant-ledger.md) remains the single obligation
owner. Before semantic-kernel freeze it must close these dependency groups:

1. **Executable foundations:** regime identity/support; canonical typed values;
   kind-safe ABIs; executable codecs, samplers, and algorithms; checkable
   totality; named malformed/failure behavior; and bounded identity/admission
   work.
2. **Strong FS and public coins:** derive `RequiredInfluence` from Core-owned
   Statement, proof-round, reduction, or oracle contracts; route every scoped
   Statement occurrence into initialization; require exact prefix satisfaction;
   close challenge namespaces and squeeze/sample semantics; and reject every
   verifier-private influence on the transformed interaction.
3. **Causal execution:** expose visible histories, legal prover moves, private
   state/randomness, and permitted oracle reads; define execution as a relation
   parameterized by strategy, invocation, and verifier/public coins; retain
   replay as an audit relation rather than treating one trace as a strategy.
4. **Exact Core choices:** settle party cardinality, effect/extension
   architecture, observation versus knowledge, terminal and failure planes,
   prover nonproduction, claim usage, reduction saturation, and failure
   precedence through their registered falsifiers.
5. **Minimum Relations and consumer seams:** define Statement/Witness surfaces,
   reachable correspondence regimes, fact and grounding algebras, lossless and
   priced-lossy bridges, directional result meaning, and source-owned views read
   by Relations, FS Analysis, and OIR projection.
6. **Non-regression and document closure:** enumerate every guarantee the target
   owes the shipped design with one owner and falsifier; remeasure changed
   encodings; price new capabilities; and remove undefined required symbols and
   temporary semantic dependencies.

The exact pre-freeze questions are frozen in the invariant ledger's
[minimum consumer question set](invariant-ledger.md#8-minimum-pre-freeze-consumer-questions).
It freezes required questions, not the current target's answers. Adding,
removing, or answering one through ambient carrier access reopens K0.

The unfinished domains have different upstream force:

| Domain | What must be co-designed before PIR freeze | What remains downstream |
|---|---|---|
| Relations | Statement/Witness ports, claim routes, grounding inputs, bridge and loss occurrences | Relation families and judgments over frozen views |
| Analysis | Causal history/strategy seam, shared FS declarations, theorem coordinates, loss occurrences | Property families, models, theorems, and bounds |
| OIR | Complete read contract for ports, effects, failures, obligations, and optional Plan fields | OIR programs and projection relations |
| Compiler | Feasibility or cost counterexamples only | Production, checked change consumption, assessment, and selection |
| Realization and Evidence | None | Implementations, observations, provenance, appraisal, and reliance |

After freeze, an already derivable fact may widen a checked PIR-owned view
without changing Protocol identity. A consumer-local fact stays outside PIR. A
new fact that changes Protocol observation, execution, or identity requires an
explicit kernel reopening, witness, and regime decision.

## 5. Execution plan

### K0 — Freeze contract and regression baseline — complete 2026-08-25

- add one target-owes-shipped section to the invariant ledger;
- reconcile historical stage labels with the integrated closure gate;
- give every open finding one owner and one executable falsifier; and
- freeze the minimum Relations, Analysis, and OIR questions PIR must answer.

K0 closed those control obligations in the
[non-regression baseline](invariant-ledger.md#7-target-owes-shipped-non-regression-baseline),
[consumer question set](invariant-ledger.md#8-minimum-pre-freeze-consumer-questions),
and this page's owner/falsifier audit. It selected no K1 representation and
does not count any unrun falsifier as passed.

### K1 — Executable foundations — complete 2026-08-26

- select the regime, canonical-value, finite-algorithm, ABI, totality, failure,
  and resource model;
- implement a representation-neutral reference evaluator and identity oracle;
  and
- run round trips plus wrong-kind, noncanonical, partial, unsupported, and
  exhausted negatives.

K1 selected the bounded executable foundation specified by
[`foundation/executable-foundations.md`](../../foundation/executable-foundations.md)
and exercised it through 116 passing checks: 90 reference/parity checks and 26
independent-oracle checks. The independent implementation boundary covers
canonical values and identity, not term evaluation. The package deliberately
does not claim a fully serialized request decoder, a second term evaluator,
Protocol/Fiat--Shamir closure, consumer closure, implementation adoption, or
kernel freeze. Those boundaries advance to K2 and K3 rather than being hidden
inside the K1 result.

### K2 — Protocol and FS kernel

- add causal strategy-generated execution;
- close Statement/Witness occurrences, required influence, initialization and
  prefixes, public-coin eligibility, and the squeeze/sample ABI;
- resolve the registered Core and extension choices on shared substrates; and
- exercise every strong-FS and shipped non-regression row at structural
  admission rather than assuming it in Analysis.

### K3 — Minimum consumer co-design

- finish the minimum Relations algebra and Protocol correspondence;
- make FS construction, theorem applicability, and property transport read one
  identified source declaration;
- close Analysis's strategy/history and quantitative-loss inputs; and
- close OIR's projection-obligation view without activating Stage 4B.

### K4 — Bounded protocol portfolio

- run P02 native FRI/IOR at T3 first because it decides oracle,
  commitment/opening, extension, and residual/terminal questions;
- complete the selected P03--P10, V01--V05, and H01--H05 cases at their assigned
  T1--T3 strengths, promoting only when a shared decision remains ambiguous;
- require decisive abstractions to have a positive inhabitant and a well-formed
  negative at the intended first boundary; and
- retain failed witnesses and exact non-claims.

### K5 — Independent freeze

- cold-review only the candidate durable documents, reference evaluator,
  witnesses, and regression ledger;
- freeze the smallest closed kernel plus its consumer read contracts;
- move remaining capabilities to explicit extension boundaries; and
- only then authorize normative drafting or implementation replacement.

### D1 onward — Vertical integration

1. Implement the new canonical PIR, authentication/admission, and source-view
   adapters alongside the current authoritative lane.
2. Adapt the current Soundness Kernel as the first Analysis family through its
   representation-neutral sealed view. Unsupported new-lane analyses remain
   explicit; there is no silent fallback.
3. Bring up Schnorr, native FRI/IOR, and relation-bound Sumcheck/GKR slices
   through PIR, Relations, FS, Analysis, and their narrow downstream seams.
4. Add Analysis families incrementally, then reconnect Compiler. Activate OIR
   and Realization only through a separate Stage 4B decision.
5. After semantic stabilization, deduplicate and absorb the documentation,
   delete temporary notes, re-synthesize the architecture, and run final
   cutover review.

## 6. Kernel freeze gate

Freeze PIR only when:

1. two independent implementations derive identical identities, admission
   results, and source views from the same durable inputs;
2. every required regime, value, algorithm, ABI, totality claim, failure, and
   bound is defined without temporary notes or ambient lookup;
3. every admitted FS protocol structurally binds all scoped Statement and
   required prover/oracle material before each challenge;
4. execution is strategy-generated, public-coin eligible where required, and
   separated from replay/audit;
5. Relations can express exact grounding, witness correspondence, lossless
   bridges, and priced lossy projections over the frozen surface;
6. FS construction, theorem applicability, property transport, Relations, and
   OIR read one source declaration through adequate views;
7. the differentiated protocol portfolio passes at its assigned strengths
   without opaque escapes or self-authored success facts; and
8. every target-owes-shipped guarantee passes its falsifier, every new
   capability names its price, and a cold reader can reconstruct the kernel
   after hiding `notes/`.

Failure reopens only the affected dependency cone unless it contradicts a
stable architecture choice. Absence of a discovered failure is not a pass.

## 7. Direct completion answer and nonclaims

PIR research is complete enough at the **architectural level** to stop broad,
unbounded redesign and begin closure. It is not complete enough at the **exact
semantic level** to call the core final, freeze identities, or replace the
current implementation wholesale.

Most unfinished downstream choices should not materially alter PIR. Full
property catalogs, compiler policies, realization providers, and evidence
appraisal are genuinely downstream. The minimum Relations surface, FS-facing
Analysis contract, and OIR read boundary still carry legitimate upstream
pressure; closing those three seams is what makes later no-backflow real.

This audit establishes no protocol security, theorem applicability,
implementation conformance, protocol-family support, migration schedule, or
normative cutover. Delete it after the freeze boundary and execution order have
durable owners and no remaining plan depends on this package.
