# Accepted standalone implementation interfaces

The sole execution carrier is upstream `PFunctor.FreeM`; its sole probability reading is VCVio `PFunctor.FreeM.runKernel` over `PFunctor.KernelHandler`. There is no new protocol syntax or evaluator. Private state and answers are sampled jointly. Exact installation reuses `KernelHandler.CouplingContract`.

Namespace: `ProtocolProof`. Package imports pinned VCVio, PolyFun and Mathlib, never existing zkc modules.

## Core module assignments

- `Semantics/Quantitative.lean`: `opExpectation handler : OpSpec P (S → ENNReal)` and `runExpectation handler program post state`; proved equality `wpFold_eq_runExpectation`. The main measurable-postcondition bridge supports arbitrary measurable state and final-result spaces; operation answers are countable with measurable singletons. Only the unrestricted-postcondition specialization additionally requires countable state and final-result spaces with measurable singletons. The root closure uses the measurable bridge and retains its generality.
- `Components/Contract.lean`: upper and lower contract rules over existing `wpFold`; bind, branch, arbitrary finite iteration and concrete local-to-global semantic bounds. No new execution AST.
- `Components/Installation.lean`: whole adaptive-client event/expectation transport from upstream local coupling contracts; free-handler installation and explicit initial-state coverage. Interface/state relations are explicit. Use existing coupling results, not a new coupling implementation.
- `Semantics/System.lean`: normalized operation handlers and initial laws, with a generic mass-one experiment constructor.
- `Components/Representation.lean`: total, possibly non-injective state maps installed from full local joint-law commutation and initial pushforward.
- `Semantics/Experiment.lean`: complete normalized laws, fixed measurable observations, and environment reindexing.
- `Semantics/Access.lean`: public-input/typed-service algorithm execution; weighted-call bounds reuse PolyFun's `OpSpec.charge` and `wpFold`.
- `Claims/Problem.lean`: promise regions, optional witness relations and explicit population predicates.
- `Claims/Quantitative.lean`: reusable upper/lower event requests.
- `Claims/Soundness.lean`, `Completeness.lean`, `Recovery.lean`: separate fixed property meanings over those event requests.
- `Claims/View.lean`: mathematical statistical view comparison and exact-law closure.
- `Claims/Request.lean`: import surface for the preceding unary/view definitions, not another implementation.
- `Claims/Extraction.lean`: request-fixed acceptance-to-extraction guarantee, access execution and weighted-call bound.
- `Claims/Simulation.lean`: request-fixed simulator, statistical or selected-observer comparison, and weighted-call bound.
- `Claims/Receipt.lean`: built-in versus custom claim constructors, exact meanings, closed and conditional evidence.
- `Claims/Diagnostics.lean`: inhabited/empty/unchecked admission error and finite/infinite resource-budget assessments.
- `Claims/Closure.lean`: top-level closure assembling local installation, initial correspondence, mathematical bound and fixed observation transfer.

- `Claims/Assembly.lean`: identity and map-based connection constructors.
- `Claims/Transfer.lean`: statistical upper game transfer with explicit environment translation, losses and composition.

All public statements must expose countability, measurability, normalization and premises actually needed. No `sorry`, custom axioms, unchecked equality tests or whole-request theorem stored as local evidence.

## Module and reduction conventions

Definitions used as the public meaning of a request, a fixed experiment, or a structural
resource fold are exposed with Lean 4.35's `@[expose]`. This permits downstream unfolding and
kernel conversion without duplicating a second model. Mathematical proof bodies need no such
policy. Proposition names (`Holds`, `Meaning`, `CallsBounded`, `IsCanonical`) are capitalized;
computations and constructors use lower camel case. No compatibility aliases remain.

The full request, not a property-name string, indexes `Receipt`. `ConditionalReceipt claim P`
contains `P → claim.Meaning`; only `close` supplied with a proof of `P` produces a closed receipt.
No route attribution participates in this typing decision. These are logical interfaces, not
a completed report generator or proof-search engine.
