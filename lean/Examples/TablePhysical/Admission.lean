import Examples.TablePhysical.Checking
import Examples.TableProtocol.Admission

/-! Phase admission at the logical provider-call boundary of physical execution.
The physical simulation is valid for every logical handler, so it can retain the
existing interaction audit without assigning phases to coarse physical requests.
-/

set_option autoImplicit false
namespace TablePhysical.Admission
open TableProtocol Zkc.Source Zkc.Realization PhaseAdmission

/-- Instrument actual logical calls inside physical operations. Preparation and
scalar reads do not invent provider calls or phase transitions. -/
def run {S E : Type} (logicalHandler : PIR.Handler Protocol.protocolInterface S E)
    {Γ : List Ty} {ty : Ty} (program : Region language Γ ty)
    (env : Environment Value Γ) (state : State (TableProtocol.Admission.Phase × S)) :=
  (program.denote meaning env).run
    (handler (PIR.ExecutionPath.handler TableProtocol.Admission.interaction logicalHandler)) state

end TablePhysical.Admission

namespace TablePhysical.Checked
open TableProtocol Zkc.Source Zkc.Realization PhaseAdmission

variable {Γ : List Ty} {ty : Ty}
    {source : RawRegion Ty Protocol.Operation} {candidate : RawRegion Ty Operation}
    (checked : Checked Γ ty source candidate)
    (actual : Region language Γ ty)
    (decoded : candidate.elaborate (language := language) Γ ty = .ok actual)
    (certificate : Certificate TableProtocol.Admission.Phase)
    (starts exits : List TableProtocol.Admission.Phase)
    (accepted : checkRegion TableProtocol.Admission.policy checked.logical certificate starts = some exits)
    {S E : Type} (logicalHandler : PIR.Handler Protocol.protocolInterface S E)
    (a : Environment TableProtocol.Value Γ) (b : Environment Value Γ)
    (phase : TableProtocol.Admission.Phase) (state : S)
    (physicalState : State (TableProtocol.Admission.Phase × S))
    (states : (phase, state) = physicalState.logical)
    (inputs : representation.Environments a (phase, state) b physicalState)
    (initial : Covered TableProtocol.Admission.summaryLaws starts phase)

include decoded states inputs in
/-- The same checked candidate retains complete phase instrumentation, even on
stopped calls and for a handler different from the deterministic trace fixture. -/
theorem audit_correct :
    representation.Results (fun event => [event]) (fun event => [event])
      (phase, state) physicalState
      ((checked.logical.denote Protocol.meaning a).run
        (PIR.ExecutionPath.handler TableProtocol.Admission.interaction logicalHandler) (phase, state))
      (Admission.run logicalHandler actual b physicalState) := by
  exact checked.correct (PIR.ExecutionPath.handler TableProtocol.Admission.interaction logicalHandler)
    actual decoded a b (phase, state) physicalState states inputs

include decoded states inputs accepted initial in
theorem calls_permitted :
    ∀ before call, Sum.inl (before, call) ∈
      (Admission.run logicalHandler actual b physicalState).events →
      TableProtocol.Admission.interaction.enabled before call := by
  have related := checked.audit_correct actual decoded logicalHandler a b phase state physicalState states inputs
  have events := related.events
  simp only [PIR.observeEvents, List.flatMap_singleton'] at events
  rw [← events]
  exact PIR.ExecutionPath.calls_permitted TableProtocol.Admission.interaction logicalHandler
    _ phase state
    (checkRegion_sound TableProtocol.Admission.policy Protocol.meaning
      TableProtocol.Admission.interaction TableProtocol.Admission.summaryLaws checked.logical
      certificate starts exits accepted a phase initial).1

include decoded states inputs accepted initial in
theorem return_permitted (value : Value ty)
    (returned : (Admission.run logicalHandler actual b physicalState).outcome = .returned value) :
    Covered TableProtocol.Admission.summaryLaws exits
      (Admission.run logicalHandler actual b physicalState).state.logical.1 := by
  have related := checked.audit_correct actual decoded logicalHandler a b phase state physicalState states inputs
  have outcome := related.outcome
  cases original : ((checked.logical.denote Protocol.meaning a).run
      (PIR.ExecutionPath.handler TableProtocol.Admission.interaction logicalHandler) (phase, state)).outcome with
  | stopped reason =>
    have impossible := (congrArg₂ (PIR.Outcome.Relates _) original returned).mp outcome
    exact False.elim impossible
  | returned logicalValue =>
    have covered := PIR.Boundary.actual_return TableProtocol.Admission.interaction _ logicalHandler
      _ phase state
      (checkRegion_sound TableProtocol.Admission.policy Protocol.meaning
        TableProtocol.Admission.interaction TableProtocol.Admission.summaryLaws checked.logical
        certificate starts exits accepted a phase initial).2 logicalValue original
    exact (congrArg (Covered TableProtocol.Admission.summaryLaws exits)
      (congrArg Prod.fst related.state.1)).mp covered

end TablePhysical.Checked
