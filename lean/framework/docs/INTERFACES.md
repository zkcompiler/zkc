# Accepted standalone implementation interfaces

The sole execution carrier is upstream `PFunctor.FreeM`; its sole probability reading is VCVio `PFunctor.FreeM.runKernel` over `PFunctor.KernelHandler`. There is no new protocol syntax or evaluator. Private state and answers are sampled jointly. Exact installation reuses `KernelHandler.CouplingContract`.

Namespace: `ProtocolProof`. Package imports pinned VCVio, PolyFun and Mathlib, never existing zkc modules.

## Core module assignments

- `Semantics/Quantitative.lean`: `opExpectation handler : OpSpec P (S → ENNReal)` and `runExpectation handler program post state`; proved equality `wpFold_eq_runExpectation`. The main measurable-postcondition bridge supports arbitrary measurable state and final-result spaces; operation answers are countable with measurable singletons. Only the unrestricted-postcondition specialization additionally requires countable state and final-result spaces with measurable singletons. The root closure uses the measurable bridge and retains its generality.
- `Components/Contract.lean`: upper and lower contract rules over existing `wpFold`; bind, branch, arbitrary finite iteration and concrete local-to-global semantic bounds. No new execution AST.
- `Components/Installation.lean`: whole adaptive-client event/expectation transport from upstream local coupling contracts; free-handler installation and explicit initial-state coverage. Interface/state relations are explicit. Use existing coupling results, not a new coupling implementation.
- `Semantics/System.lean`: normalized operation handlers and initial laws, with a generic mass-one experiment constructor.
- `Components/Representation.lean`: total, possibly non-injective state maps installed from full local joint-law commutation and initial pushforward.
- `Claims/Request.lean`: normalized fixed experiments and separate canonical soundness/completeness requests.
- `Claims/Closure.lean`: top-level closure assembling local installation, initial correspondence, mathematical bound and fixed observation transfer.

- `Claims/Assembly.lean`: identity and map-based connection constructors.
- `Claims/Transfer.lean`: statistical upper game transfer with explicit environment translation, losses and composition; exact-view transport.

All public statements must expose countability, measurability, normalization and premises actually needed. No `sorry`, custom axioms, unchecked equality tests or whole-request theorem stored as local evidence.
