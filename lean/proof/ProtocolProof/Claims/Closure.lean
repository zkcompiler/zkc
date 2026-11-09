module

public import ProtocolProof.Components.Contract
public import ProtocolProof.Components.Installation
public import ProtocolProof.Internal.Closure

/-!
# Process-facing root closure

Evidence is indexed by the request and the fixed Process client. Complete local operation
installation, whole initial-law coverage, mathematical contracts and property-directed
terminal comparison are assembled by the existing checked backend root theorem.
-/

public section
open PIR MeasureTheory PFunctor

namespace ProtocolProof
variable {E : Type} {I : Signature} {S T L M A : Type}
  [∀ op, MeasurableSpace (I.Reply op)]
  [∀ op, Countable (I.Reply op)] [∀ op, MeasurableSingletonClass (I.Reply op)]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace L] [MeasurableSpace M]
  [MeasurableSpace A]

/-- Substantive local and mathematical obligations for the request's fixed upper event. -/
structure UpperEvidence (request : UpperRequest E (Execution S L A))
    (actual : System E I S L) (model : System E I T M) (client : E → Process I A)
    (related : E → (S × List L) → (T × List M) → Prop) where
  subject : request.experiment = actual.experiment client
  installation : Installation actual model request.admissible related
  spec : E → OperationSpec I T M
  local_bound : ∀ e, request.admissible e → ∀ operation continuation,
    opExpectation (model.accumulatedOperations e) operation continuation ≤
      spec e operation continuation
  model_event : E → Set (Execution T M A)
  measurable_event : ∀ e, MeasurableSet (model_event e)
  terminal : ∀ e, request.admissible e → ∀ outcome actualState modelState,
    related e actualState modelState →
    (⟨outcome, actualState.1, actualState.2⟩ : Execution S L A) ∈ request.event →
      (⟨outcome, modelState.1, modelState.2⟩ : Execution T M A) ∈ model_event e
  potential : E → (T × List M) → ENNReal
  mathematics : ∀ e, request.admissible e →
    UpperBound (spec e) (client e)
      (fun outcome state ↦ (model_event e).indicator 1 ⟨outcome, state.1, state.2⟩) (potential e)
  budget : ∀ e, request.admissible e →
    (∫⁻ state, potential e state ∂model.initialWithEvents e) ≤ request.bound e

/-- Completeness reverses both contract and event implications, retaining every stopped path. -/
structure LowerEvidence (request : LowerRequest E (Execution S L A))
    (actual : System E I S L) (model : System E I T M) (client : E → Process I A)
    (related : E → (S × List L) → (T × List M) → Prop) where
  subject : request.experiment = actual.experiment client
  installation : Installation actual model request.admissible related
  spec : E → OperationSpec I T M
  local_bound : ∀ e, request.admissible e → ∀ operation continuation,
    spec e operation continuation ≤ opExpectation (model.accumulatedOperations e)
      operation continuation
  model_event : E → Set (Execution T M A)
  measurable_event : ∀ e, MeasurableSet (model_event e)
  terminal : ∀ e, request.admissible e → ∀ outcome actualState modelState,
    related e actualState modelState →
    (⟨outcome, modelState.1, modelState.2⟩ : Execution T M A) ∈ model_event e →
      (⟨outcome, actualState.1, actualState.2⟩ : Execution S L A) ∈ request.event
  potential : E → (T × List M) → ENNReal
  mathematics : ∀ e, request.admissible e →
    LowerBound (spec e) (client e)
      (fun outcome state ↦ (model_event e).indicator 1 ⟨outcome, state.1, state.2⟩) (potential e)
  budget : ∀ e, request.admissible e →
    request.bound e ≤ ∫⁻ state, potential e state ∂model.initialWithEvents e

/-- Assemble public local obligations using the existing upper root, with no claim substitution. -/
theorem UpperEvidence.establish {request : UpperRequest E (Execution S L A)}
    {actual : System E I S L} {model : System E I T M} {client : E → Process I A}
    {related : E → (S × List L) → (T × List M) → Prop}
    (evidence : UpperEvidence request actual model client related) : request.Holds := by
  let backendRequest : UpperRequest E (Outcome A × (S × List L)) := {
    experiment := (Internal.backendSystem actual).experiment (fun e ↦ Internal.encode (client e))
    admissible := request.admissible
    event := Execution.measurableEquiv.symm ⁻¹' request.event
    measurable_event := request.measurable_event.preimage
      Execution.measurableEquiv.symm.measurable
    bound := request.bound }
  have backendEvidence : Internal.UpperEvidence backendRequest (Internal.backendSystem actual) (Internal.backendSystem model)
      (fun e ↦ Internal.encode (client e)) related := {
    subject := rfl
    connection := ⟨evidence.installation.operations, evidence.installation.initial⟩
    spec := evidence.spec
    local_bound := evidence.local_bound
    model_event := fun e ↦ Execution.measurableEquiv.symm ⁻¹' evidence.model_event e
    measurable_event := fun e ↦ (evidence.measurable_event e).preimage
      Execution.measurableEquiv.symm.measurable
    terminal := evidence.terminal
    potential := evidence.potential
    mathematics := evidence.mathematics
    budget := evidence.budget }
  intro e he
  rw [evidence.subject]
  change ((((Internal.backendSystem actual).experiment (fun e ↦ Internal.encode (client e))).run e).map
    Execution.measurableEquiv.symm) request.event ≤ request.bound e
  rw [Measure.map_apply Execution.measurableEquiv.symm.measurable request.measurable_event]
  exact backendEvidence.establish e he

/-- Reuse the lower root with the opposite, property-correct terminal implication. -/
theorem LowerEvidence.establish {request : LowerRequest E (Execution S L A)}
    {actual : System E I S L} {model : System E I T M} {client : E → Process I A}
    {related : E → (S × List L) → (T × List M) → Prop}
    (evidence : LowerEvidence request actual model client related) : request.Holds := by
  let backendRequest : LowerRequest E (Outcome A × (S × List L)) := {
    experiment := (Internal.backendSystem actual).experiment (fun e ↦ Internal.encode (client e))
    admissible := request.admissible
    event := Execution.measurableEquiv.symm ⁻¹' request.event
    measurable_event := request.measurable_event.preimage
      Execution.measurableEquiv.symm.measurable
    bound := request.bound }
  have backendEvidence : Internal.LowerEvidence backendRequest (Internal.backendSystem actual) (Internal.backendSystem model)
      (fun e ↦ Internal.encode (client e)) related := {
    subject := rfl
    connection := ⟨evidence.installation.operations, evidence.installation.initial⟩
    spec := evidence.spec
    local_bound := evidence.local_bound
    model_event := fun e ↦ Execution.measurableEquiv.symm ⁻¹' evidence.model_event e
    measurable_event := fun e ↦ (evidence.measurable_event e).preimage
      Execution.measurableEquiv.symm.measurable
    terminal := evidence.terminal
    potential := evidence.potential
    mathematics := evidence.mathematics
    budget := evidence.budget }
  intro e he
  rw [evidence.subject]
  change request.bound e ≤
    ((((Internal.backendSystem actual).experiment (fun e ↦ Internal.encode (client e))).run e).map
      Execution.measurableEquiv.symm) request.event
  rw [Measure.map_apply Execution.measurableEquiv.symm.measurable request.measurable_event]
  exact backendEvidence.establish e he

end ProtocolProof
