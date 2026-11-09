# Shared program and proof implementation

Packages 1 and 2 of the selected architecture are implemented on
`codex/program-proof-foundation`. This is the common foundation before imported-protocol
adoption and the Package 3 construction engine. The current physical/module owners
follow [the formal architecture](../../docs/architecture.md).

## Package ownership

`lean/program` owns the canonical Process, Outcome, Execution, Stop and generic Region
with Lean/Std-only core imports; shared mathematical support may use Mathlib. Existing `PIR` and `Zkc.Source` declaration namespaces
are retained for the original definitions; no forwarding modules or aliases remain.
The concrete `lean/ir` and mathematical `lean/protocol` packages depend independently
on this foundation. `lean/verification` is the integration consumer of both. Package locks, ownership checks,
import policy and source-only reproduction use this same dependency graph.

## One public execution model

All public programs, contracts, extraction and simulation access use Process. The internal
encoding reuses upstream FreeM kernel execution and quantitative reasoning. The encoding
preserves monadic execution, returned and stopped outcomes, reached state and ordered events.
Probability laws are normalized on the whole initial measure; failure is not conditioned away.
Public execution equations, expectation adequacy and deterministic Dirac agreement connect the
probability interpretation to the shared execution meaning.

## Installation, representation and composition

Same-interface `Installation` requires local joint-law coupling and initial coverage.
`InterpretationContract` covers deterministic operation-to-Process implementation and transitive
full-record correspondence. `ServiceInstallation` extends this to probabilistic implementations
at a different interface, using one local law for each operation and a whole-initial-law coupling.
Its substitution theorem applies to arbitrary adaptive callers, including repeated and nested
calls. The implementation is fixed before checking the client.

Upper/lower contracts provide bind, branch, consequence and finite/nested iteration. They expose
stopped-branch obligations explicitly. The common root evidence combines fixed subject binding,
installation, mathematics, initial budget and terminal observation implication. UpperTransfer and
LowerTransfer separately compose proved statistical game changes with explicit losses.

## Complete model clients

- AdaptiveChecks: finite algebraic challenge checks, adaptive histories, nested round counts,
  soundness bounds and honest completeness through the common roots.
- OracleProximity: a frozen two-cell table and arbitrary repeated sampling, exact accepting
  probability, canonical soundness and completeness requests through those same roots.
- SharedState: persistent challenge/counter state and observation-sensitive representation;
  independent-round reasoning is not assumed.
- ServiceDecoding: a probabilistic word service, total bit decoder and malformed-input failure;
  one installed local law covers two call sites and arbitrary nested callers.
- InterpretationModels and property/execution/contract/transfer controls: full-record composition,
  request-fixed access, unconditional mass, every stop reason and rejected weakened obligations.

These are complete small model claims, not claims about imported Sumcheck, FRI or GKR artifacts.
Companions still supply mathematical operation laws, representations, invariants and terminal
facts. The generic theorems remove repeated structural proofs; selecting and applying them is
ordinary Lean authoring until Package 3 provides checked construction.

## Validation and next boundary

See VALIDATION.md for the exact build, exhaustive private-body audit, boundary checks and
independent review. Shared-program extraction preserves the original declaration bodies and
existing protected-statement lock. Concrete semantic-consumer checks cover the moved imports;
no new native/compiled protocol assurance is inferred from model validation.

Package 3 supplies the constructor and companion obligation reporting. Package 4 consolidates
mathematical libraries and concrete integration ownership. Neither is included in this unit.
