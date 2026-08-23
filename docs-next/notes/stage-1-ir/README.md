# Reopened Stage 1: Protocol IR architecture research

> **Document kind:** Temporary work-package charter
> **Document state:** Complete; awaiting later absorption
> **Provisional owner:** `project`
> **Authority:** None. This package records the research that informed the
> selected non-normative [Protocol IR Architecture](../../project/protocol-ir-architecture.md).
> It does not amend the current specifications, perform normative cutover, or
> authorize implementation work or Stage 2 execution.
> **Disposition:** Promote reviewed conclusions into their exact durable
> owners, record durable decisions and rejected alternatives where useful,
> reconcile dependent stages, and then delete this package.

## 1. Central question

Stage 1 is reopened around one question:

> If zkc's Protocol IR were designed from first principles for zero-knowledge
> protocol compilation today, what division of semantic model, MLIR dialects,
> canonical forms, identities, carriers, views, and compatibility boundaries
> would be best?

The answer must be native to zkc. Mature IR systems are evidence about design
forces, successful mechanisms, accumulated constraints, and long-term costs.
They are not templates and cannot decide the result by analogy.

## 2. Why Stage 1 is reopened

The prior Stage 1 lifecycle work produced a coherent and useful first
hypothesis. It distinguished Protocol from carrier context, resolved versus
admitted content, semantic authority from opaque reference, and immutable
capability from serialized data. It also selected PIR as the sole supported v0
carrier, kept the abstract Protocol owner under `pir/`, and declined a second
public semantic schema.

Those conclusions were reached before a sufficiently broad comparative study
of mature IR architecture, compatibility history, protocol-specific theory,
and proof-system-adjacent representations. Subsequent discussion exposed a
credible larger design space:

- a single lifecycle-aware PIR dialect;
- separate authoring and canonical Protocol dialects, both in MLIR;
- a stable portable Protocol dialect beside a more freely evolving optimizing
  dialect;
- a carrier-independent semantic package with MLIR adapters;
- consumer-specific projections over one canonical PIR subject; and
- mixtures of these choices at different lifecycle boundaries.

This is enough to trigger the reopening rule in the design program: a credible
alternative may enable materially greater capability, and the current
factorization has not yet survived an independent clean-room comparison.

The earlier result remains the **baseline candidate**. It is not silently
rewritten, treated as a failed design, or inherited as a constraint.

## 3. Scope

This package owns research and convergence for:

- the abstract Protocol subject and its relation to concrete representations;
- Open, normalized, closed, sealed, persisted, decoded, and admitted forms;
- authoring IR versus canonical semantic IR;
- MLIR's role as workbench, representation, transport, or interchange layer;
- dialect granularity and legal mixed-dialect states;
- Protocol identity, canonicalization, semantic version, and carrier version;
- extensibility, unknown content, contracts, profiles, and dependency closure;
- transformation classes and their preservation or refinement obligations;
- statement, witness, endpoint, and human-facing interface ownership;
- immutable consumer views and independent-checker surfaces;
- composition, recursion, linking, and multi-level lowering pressure; and
- the latest responsible point for stable external compatibility.

It inspects relation ingress, Analysis, Compiler, OIR, Realization, and formal
models only as consumers or pressure sources. Their complete schemas remain
owned by later packages.

## 4. Non-goals

This package does not:

- preserve an existing representation merely to reduce migration cost;
- replace MLIR merely to obtain implementation-language neutrality;
- choose Rust, C++, an IDL, JSON, or another serialization technology before
  the semantic and lifecycle roles are selected;
- equate interoperability with a second manually synchronized object model;
- design a universal IR for relations, protocols, endpoints, and machines;
- perform a vulnerability review or make a security claim;
- ratify Stage 2 transition contracts while their source subjects are open;
- change implementation code; or
- treat documentation volume or number of surveyed systems as completion.

Migration feasibility will be recorded after candidate comparison, but it is
not an input that may deform the selected ideal model.

## 5. Provisional boundary contract for parallel research

Independent research tracks begin from the following facts and open choices.

### 5.1 Intended zkc subject, provisionally stable

zkc is a compiler for already formed zero-knowledge protocols above relation,
circuit, and AIR representations. A Protocol currently couples:

```text
an ordered transcript/effect spine
                 +
a typed claim and reduction flow graph
```

It can be checked, transformed, analyzed under explicit conditional rules, and
projected into asymmetric prover and verifier endpoints. These intended
capabilities are design pressures, not endorsements of their current encoding.

### 5.2 Current implementation, observed but not authoritative

The checkout currently uses:

- MLIR dialects for PIR and OIR;
- C++ for sealing, admission, canonical encoding, analysis, and compiler
  control;
- immutable admitted PIR capabilities at consumer boundaries;
- consumer-specific owned C++ views for Soundness and compiler observations;
- PIR-to-PIR checked transforms that reopen, transform, reseal, and re-admit;
- PIR-to-OIR projection inside MLIR; and
- a canonical OIR document consumed by C++, Python, and Rust implementations.

Research must account for this feasibility evidence without allowing it to
define the clean-room target.

### 5.3 Decisions deliberately open

- whether canonical Protocol representation remains PIR/MLIR;
- whether Open and Sealed forms belong to one dialect;
- whether a separate portable or versioned Protocol dialect is justified;
- whether the current canonical identity projection should remain non-ingress;
- whether `pir/` or a representation-neutral `protocol/` owns semantics;
- whether a complete carrier-independent runtime object should exist;
- whether independent checking consumes PIR, a portable profile, a fact view,
  or a proof/certificate;
- how Protocol interface data enters identity;
- how semantic language revisions relate to content identities;
- which extension points are closed, versioned, negotiated, or lowered away;
  and
- which transformation laws must be intrinsic to the IR architecture.

No research track may ratify one of these choices independently.

## 6. Research order

The package uses six ordered activities.

### Activity A: derive zkc-native design forces

Reconstruct intended semantics, current specifications, implementation seams,
consumer needs, theoretical constraints, and capability opportunities before
using external analogies. The working ledger is
[Zkc-native Design Forces](zkc-design-forces.md).

### Activity B: study representative IR histories

Select cases by distinct pressure rather than fame or superficial similarity.
The initial portfolio is:

| Family | Initial cases | Main pressure under study |
|---|---|---|
| Portable semantic/interchange IR | StableHLO/VHLO, SPIR-V, ONNX | Semantic specification, stable subset, serialization, compatibility, extensibility |
| Multi-level MLIR compiler | CIRCT, IREE, upstream MLIR | Dialect granularity, progressive lowering, effects, legality, internal versus public IR |
| Long-lived language/IR contract | LLVM IR/bitcode, WebAssembly, one justified comparison | Semantic evolution, validation, target environment, difficult legacy decisions |
| ZK and proof-adjacent IR | LLZK, zkLLVM, CirC, ACIR/Brillig, Cairo Sierra/CASM, selected R1CS/AIR systems | Relation/protocol boundary, witness and backend binding, proof-specific abstraction |
| Protocol and transformation theory | Interactive/trace semantics, Fiat--Shamir structure, effects, session/choreography models, translation validation | Laws that ordinary SSA or functional equivalence cannot express |

The portfolio may be narrowed, expanded, or replace a weakly documented case.
Coverage is sufficient when additional cases stop adding a material design
pressure, mechanism, failure mode, or alternative.

### Activity C: extract cross-case pressures

For each observed strength or pain point, ask:

1. Which original goal produced the decision?
2. Is the claimed pain documented, directly observable, or inferred?
3. Is it inherent to the domain, introduced by representation, or caused by an
   installed base?
4. Would zkc face the same force?
5. What is the limit of the analogy?
6. What decision could PIR make earlier or differently?

### Activity D: build independent candidate architectures

At minimum compare:

1. **Lifecycle-aware single PIR dialect.** Open and Sealed Protocol forms share
   one canonical MLIR dialect and zkc-owned identity projection.
2. **Construction dialects to canonical PIR.** Flexible authoring and imported
   forms fully lower into a smaller closed Protocol dialect before sealing.
3. **Optimizing PIR plus portable Protocol dialect.** An internal transformation
   dialect converts to a stable semantic/interchange dialect with its own
   compatibility contract.
4. **Carrier-independent semantic object plus adapters.** A non-MLIR canonical
   model or package owns runtime meaning while PIR is one authoring and
   transformation adapter.
5. **Consumer-view architecture.** One canonical PIR subject remains central,
   while independent consumers receive minimal authenticated projections
   rather than a universal second model.

Candidates may be combined only after their independent costs and excluded
capabilities are understood.

### Activity E: attack candidates with protocol-specific scenarios

The common scenario portfolio is extended with focused counterexamples:

- two authoring forms that should denote one Protocol;
- two identical Protocol cores with different external interfaces;
- transcript reorderings that preserve SSA use-def structure but change
  challenge semantics;
- a compiler transform that improves cost while weakening a conditional bound;
- one verifier projection and several prover construction plans;
- linked protocols with domain-separation and challenge-dependency pressure;
- opaque relation anchors whose interpretation belongs upstream;
- a future independent checker that should not import the optimizing compiler;
- a new extension unknown to an older consumer; and
- a semantically unchanged artifact crossing a carrier or dialect revision.

### Activity F: converge and promote

Select a target only after producer/consumer review. Record rejected alternatives,
reversal conditions, and the latest responsible point for deferred
compatibility work. Then update durable Protocol, carrier, architecture, and
decision owners and rebuild the Stage 2 entry contract.

## 7. Evidence and source discipline

Every case-study statement must be labeled or written unambiguously as one of:

- **source fact:** stated by a primary paper, official specification, RFC,
  maintained documentation, or implementation contract;
- **implementation observation:** directly reconstructed from source or tests;
- **historical report:** a maintainer-authored explanation of why a mechanism
  exists;
- **design inference:** our explanation or counterfactual conclusion;
- **PIR transfer:** a proposed lesson for zkc; or
- **analogy limit:** a reason the source system cannot decide the PIR question.

Pain points require evidence. A compatibility mechanism is not called a design
mistake merely because it is complex; it may be the successful cost of a large
ecosystem. Repository popularity, project reputation, and current adoption do
not count as semantic evidence.

Primary sources are preferred. Secondary surveys may locate material but do
not support a final architectural conclusion when a specification, paper,
source contract, RFC, or maintainer record is available.

## 8. Case-study contract

Every case dossier answers the following where applicable:

```text
semantic subject and non-subjects
original goals and consumers
authoring, internal, canonical, and interchange forms
validation and admission model
identity, text, binary, schema, and semantic versioning
extension and unknown-content policy
dialect or level decomposition
legal mixed-form states and conversion boundaries
effect, state, order, and environment representation
transformation and preservation model
composition and external dependency model
independent implementation and formalization surface
documented strengths
documented or observable pain points
installed-base constraints and compatibility mechanisms
counterfactual redesign inference
PIR-transfer hypotheses
limits of analogy
primary sources
```

The dossier should identify absence rather than invent an answer. A system that
does not model interactive protocols is still useful evidence for a narrower
question such as versioning or stable dialect design.

## 9. Evaluation axes

The common design-research axes remain binding. This package additionally
emphasizes:

- fidelity to ordered interactive effects;
- explicit claim-flow and transcript coupling;
- preservation of Fiat--Shamir dependencies and framing;
- separation of structural validity from conditional property judgments;
- verifier/prover projection coherence;
- compiler search and transform-checking leverage;
- authoring freedom versus canonical minimality;
- semantic, carrier, dialect, and producer version separation;
- compatibility cost paid only at a real external boundary;
- minimal trusted surface for independent checking;
- ability to compose protocols and carry obligations; and
- avoidance of a manually synchronized shadow IR.

Migration cost is reported after semantic comparison and cannot compensate for
an identity, authority, or semantic defect.

## 10. Outputs and gates

The reopened package must produce:

```text
zkc-native design-force ledger
current-model and implementation correspondence dossier
case-study portfolio with source and analogy limits
cross-case pressure and pain-point matrix
theory-derived semantic laws and counterexamples
independent candidate architectures
scenario and falsification results
preferred target or explicit deferral
rejected alternatives and reversal conditions
current-to-target gap map
revised Stage 2 entry contract
temporary-note absorption record
```

The previous Stage 1 exit condition was replaced by this discovery gate:

1. zkc-native forces have been derived without external templates;
2. every selected case adds a named design pressure or is removed;
3. documented pain and our inference are visibly separated;
4. at least four materially distinct architecture candidates are concrete;
5. protocol-specific scenarios expose their different consequences; and
6. another reviewer can challenge both source selection and transfer logic.

No absence of a counterexample and no successful current test suite closes
this package. The gate was satisfied through the recorded source portfolio,
equal-resolution candidate instantiations, hard-gate scenario evaluation, and
independent adversarial review.

## 11. Relationship to dependent work

The [Candidate Protocol Subject and Lifecycle](../../pir/protocol-lifecycle.md)
remains the baseline candidate and source of previously discovered
distinctions. Its selected carrier and ownership conclusions are superseded by
the durable [Protocol IR Architecture](../../project/protocol-ir-architecture.md).

At Stage 1 closure, the
[Stage 2 Transition and Bridge Charter](../stage-2-transition-and-bridge-charter.md)
remained paused. Stage 2 was subsequently activated and completed on
2026-08-22 through its separate
[research package](../stage-2-transitions/README.md). Its selected durable
result is the
[Transition and Bridge Architecture](../../project/transition-and-bridge-architecture.md),
and Stage 3 was subsequently activated at its bounded Stage 3.0 charter and
intake gate.

The [MLIR Carrier Assessment](../mlir-carrier-assessment.md) becomes one prior
candidate dossier. Its recommendation is not inherited by this package.

## 12. Deletion trigger

Delete this package when:

- the selected semantic and representation architecture is complete in its
  durable owners;
- durable decisions retain the necessary comparative rationale;
- rejected alternatives and reconsideration triggers are preserved where
  useful;
- dependent Stage 2 inputs have been reconciled;
- deferred external-compatibility work has an exact trigger and owner; and
- no durable page depends on this temporary package.

## 13. Final research state — 2026-08-22

Completed in the restart pass:

- the previous Stage 1 result is explicitly retained as a baseline candidate,
  not an inherited conclusion;
- Stage 2 was held paused during Stage 1 without discarding its observations
  and counterexamples;
- the zkc-native [design-force ledger](zkc-design-forces.md) is established;
- the [current zkc correspondence dossier](cases/current-zkc-correspondence.md)
  reconstructs subject, identity, lifecycle, consumer, and MLIR boundaries;
- the [case portfolio](cases/README.md) covers portable, multi-level,
  long-lived, ZK-adjacent, and protocol-theory pressures;
- the [first-wave synthesis](cross-case-synthesis.md) separates
  candidate-independent conclusions, genuine conflicts, orthogonal design
  axes, and the initial candidate portfolio;
- [Candidate Instantiations](candidate-instantiations.md) gives A, B, and D
  the same semantic subject and evaluates E as a complement;
- [Scenario Results](scenario-results.md) attacks the candidates with all
  twelve protocol-specific cases and explicit falsifiers;
- the [Convergence Record](convergence.md) resolves the subject, identity,
  ordering, effect, carrier, checker, and compatibility axes;
- the [Current-to-target Gap Map](current-to-target-gap.md) records the
  architecture delta without treating migration cost as a selection input;
- the [Absorption Record](absorption-record.md) records durable promotions,
  remaining normative destinations, and why temporary notes are retained; and
- the durable [Protocol IR Architecture](../../project/protocol-ir-architecture.md)
  records the selected Stage 1 target and the exact Stage 2 entry contract.

The selected target is a language-independent semantic model carried by a
distinct small closed canonical PIR level in MLIR, with rich authoring forms
upstream, regime-qualified compositional identities, a total schedule inside
`InteractiveCore`, dependent `ProtocolInterfaceId`, separate `ProverPlanId`,
purpose-specific views, and no complete portable compatibility representation
until a concrete external trigger exists.

Stages 1--3 are complete. Stage 3 consumed these selected contracts and
promoted the exact Protocol/PIR-and-Relations target. This Stage 1 package
remains under `notes/` only to preserve research traceability until its
evidence and rationale are fully absorbed during later normative
consolidation.
