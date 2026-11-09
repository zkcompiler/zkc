module

public import ProtocolProof.Semantics.System
public import ProtocolProof.Claims.Request
public import ProtocolProof.Components.Contract
public import ProtocolProof.Components.Installation

/-!
# Top-level closure from local facts

The fixed request is the index, not a field chosen by evidence. The common connection contains
only operation-level installations and initial-state coverage. The mathematical part contains
compositional contracts and a bound on their initial potential. Neither record contains the
requested whole-experiment conclusion.

`subject` binds the request to this standalone execution. It is reflexivity for requests built
from `System.experiment`. A later compiler adapter must prove this binding for its fixed subject;
that adapter is deliberately outside this package.
-/

public section

open MeasureTheory PFunctor
open scoped ENNReal

universe uE uA uB uS uT uX

namespace ProtocolProof

variable {E : Type uE} {P : PFunctor.{uA, uB}} {S : Type uS} {T : Type uT}
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [MeasurableSpace T]

/-- One set of local laws, reusable for every client of this component interface. -/
structure Connection (actual : System E P S) (model : System E P T)
    (admissible : E → Prop) (related : E → S → T → Prop) where
  operations : ∀ environment, admissible environment →
    KernelHandler.CouplingContract (actual.operations environment) (model.operations environment)
      (related environment)
  initial : ∀ environment, admissible environment →
    ExpectationWP.CouplingPost (actual.initial environment) (model.initial environment)
      (related environment)

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  {X : Type uX} [MeasurableSpace X]

/-- Local installation, mathematical contracts and event transport for a fixed upper request. -/
structure UpperEvidence (request : UpperRequest E (X × S))
    (actual : System E P S) (model : System E P T) (client : E → FreeM P X)
    (related : E → S → T → Prop) where
  subject : request.experiment = actual.experiment client
  connection : Connection actual model request.admissible related
  spec : E → OpSpec P (T → ENNReal)
  local_bound : ∀ e, request.admissible e → ∀ operation continuation,
    opExpectation (model.operations e) operation continuation ≤ spec e operation continuation
  model_event : E → Set (X × T)
  measurable_event : ∀ e, MeasurableSet (model_event e)
  terminal : ∀ e, request.admissible e → ∀ value actualState modelState,
    related e actualState modelState →
    (value, actualState) ∈ request.event → (value, modelState) ∈ model_event e
  potential : E → T → ENNReal
  mathematics : ∀ e, request.admissible e →
    UpperBound (spec e) (client e)
      (fun value state ↦ (model_event e).indicator 1 (value, state)) (potential e)
  budget : ∀ e, request.admissible e →
    (∫⁻ state, potential e state ∂model.initial e) ≤ request.bound e

/-- Completeness reverses both quantitative and observation directions, retaining full mass. -/
structure LowerEvidence (request : LowerRequest E (X × S))
    (actual : System E P S) (model : System E P T) (client : E → FreeM P X)
    (related : E → S → T → Prop) where
  subject : request.experiment = actual.experiment client
  connection : Connection actual model request.admissible related
  spec : E → OpSpec P (T → ENNReal)
  local_bound : ∀ e, request.admissible e → ∀ operation continuation,
    spec e operation continuation ≤ opExpectation (model.operations e) operation continuation
  model_event : E → Set (X × T)
  measurable_event : ∀ e, MeasurableSet (model_event e)
  terminal : ∀ e, request.admissible e → ∀ value actualState modelState,
    related e actualState modelState →
    (value, modelState) ∈ model_event e → (value, actualState) ∈ request.event
  potential : E → T → ENNReal
  mathematics : ∀ e, request.admissible e →
    LowerBound (spec e) (client e)
      (fun value state ↦ (model_event e).indicator 1 (value, state)) (potential e)
  budget : ∀ e, request.admissible e →
    request.bound e ≤ ∫⁻ state, potential e state ∂model.initial e

/-- Close an upper request using the common structural theorem and the composed mathematics. -/
theorem UpperEvidence.establish {request : UpperRequest E (X × S)}
    {actual : System E P S} {model : System E P T} {client : E → FreeM P X}
    {related : E → S → T → Prop}
    (evidence : UpperEvidence request actual model client related) : request.Holds := by
  intro environment hadmitted
  rw [evidence.subject]
  exact (Installation.event_le (evidence.connection.operations environment hadmitted)
    (evidence.connection.initial environment hadmitted) (client environment)
    request.event (evidence.model_event environment) request.measurable_event
    (evidence.measurable_event environment) (evidence.terminal environment hadmitted)).trans
      (UpperBound.closed_event_le (model.operations environment)
        (evidence.local_bound environment hadmitted) (evidence.model_event environment)
        (evidence.measurable_event environment) (evidence.mathematics environment hadmitted)
        (model.initial environment) (evidence.budget environment hadmitted))

/-- The same installation supports a lower request, with the property's correct direction. -/
theorem LowerEvidence.establish {request : LowerRequest E (X × S)}
    {actual : System E P S} {model : System E P T} {client : E → FreeM P X}
    {related : E → S → T → Prop}
    (evidence : LowerEvidence request actual model client related) : request.Holds := by
  intro environment hadmitted
  rw [evidence.subject]
  exact (LowerBound.le_closed_event (model.operations environment)
    (evidence.local_bound environment hadmitted) (evidence.model_event environment)
    (evidence.measurable_event environment) (evidence.mathematics environment hadmitted)
    (model.initial environment) (evidence.budget environment hadmitted)).trans
      (Installation.event_ge (evidence.connection.operations environment hadmitted)
        (evidence.connection.initial environment hadmitted) (client environment)
        request.event (evidence.model_event environment) request.measurable_event
        (evidence.measurable_event environment) (evidence.terminal environment hadmitted))

end ProtocolProof
