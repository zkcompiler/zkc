module

public import Zkc.Construction.ConnectionFrame
public import Zkc.Construction.ConnectionRouting
public import Zkc.Construction.DomainViewLaws

@[expose] public section

/-! Local alignment rules for the actual source actions and constructed views.
All arguments, stops, typed replies and physical appends remain explicit. These
rules are structural; they make no assumptions about provider distributions.
-/
set_option autoImplicit false
noncomputable section
namespace Zkc.Construction.Original
open Zkc.Source Zkc.Source.Structured
variable {carriers : Carriers}

/-- A receive retains its source state and appends exactly one nominal value. -/
def Received (ty : Ty) (state : State carriers) (environment : Domain.Environment carriers)
    (source : carriers.Value ty × State carriers) (target : Domain.Environment carriers) : Prop :=
  source.2 = state ∧ ∃ physical, Domain.Value.encode ty source.1 = some physical ∧
    target = environment ++ [physical]

/-- Generic plain receive, for either role and every nominal data type. The
route is authenticated against the source; every typed peer reply is covered. -/
def Simulation.plainReceive (routing : Routing) (state : State carriers)
    (ty : Ty) (site : String) (sender : Nat) (origin : Origin)
    (route : routing.message state.frames site sender routing.self = some origin)
    (data : ty.isService = false) (environment : Domain.Environment carriers) :
    Simulation (Received ty state environment) (fun _ frame => frame = environment)
      (receivePlain routing state ty site sender)
      (Domain.View.receive site site (routing.context.role sender) ty [.data ty] environment) := by
  simp only [receivePlain, data, Bool.false_eq_true, ↓reduceIte]
  change Simulation _ _
    (match routing.message state.frames site sender routing.self with
    | none => .halt .refused
    | some _ => .call (.receive ty site site (routing.context.role sender))
        (fun value => .done (value, state))) _
  rw [route]
  rw [Domain.View.receive_eq site (routing.context.role sender) ty environment
    (by simp [Domain.dataType, data])]
  apply Simulation.call
  intro value
  apply Classical.choice
  obtain ⟨physical, encoded⟩ := Domain.Value.encode_exists (carriers := carriers)
    (by simp [Domain.dataType, data]) value
  have sorts : Domain.sortsMatch [.data ty] [physical] = true := by
    simp [Domain.sortsMatch, Domain.Value.encode_sort encoded]
  refine ⟨?_⟩
  simp only [encoded, Domain.View.append, sorts, ↓reduceIte]
  exact .done ⟨rfl, physical, encoded, rfl⟩

/-- A checked receive extends the normal-form frame without another tuple or
history proof for the particular protocol. -/
theorem Received.frame {model : DomainModel} {scope : NormalForm.Scope}
    {binders : NormalForm.Binders model scope} {layout : ConnectionFrame.Layout scope}
    {ty : Ty} {state : State model.toCarriers} {environment target : Domain.Environment model.toCarriers}
    {source : model.Value ty × State model.toCarriers}
    (returned : Received ty state environment source target)
    (related : ConnectionFrame.Holds model binders state.history layout environment) :
    ConnectionFrame.Holds model (.cons source.1 binders) source.2.history
      (layout.map (ConnectionFrame.Cell.rename (target := .value ty :: scope) .there) ++
        [.data (.present (.var .here))]) target := by
  obtain ⟨same, physical, encoded, appended⟩ := returned
  rw [same, appended]
  exact related.bindData source.1 encoded

/-- A plain send preserves the complete source state and physical frame.
Nominal payload equality is derived from the actual operand encoding. -/
def Simulation.plainSend (routing : Routing) (state : State carriers)
    (ty : Ty) (site : String) (receiver : Nat) (value : carriers.Value ty) (origin : Origin)
    (route : routing.message state.frames site routing.self receiver = some origin)
    (environment : Domain.Environment carriers) (reference : Nat) (payload : Domain.Payload carriers)
    (encoded : Domain.Payload.ofValue ty value = some payload)
    (read : environment[reference]? = some (.data payload)) :
    Simulation (fun source final => source = ((), state) ∧ final = environment)
      (fun _ frame => frame = environment)
      (sendPlain routing state ty site receiver value)
      (Domain.View.send site site (routing.context.role receiver) reference [] environment) := by
  simp only [sendPlain, encoded]
  change Simulation _ _
    (match routing.message state.frames site routing.self receiver, some payload with
    | some _, some value => .call (.send site site (routing.context.role receiver) value)
        (fun _ => .done ((), state))
    | _, _ => .halt .refused) _
  rw [route]
  rw [Domain.View.send_eq site (routing.context.role receiver) reference environment payload read]
  exact .call _ (fun _ => .done ⟨rfl, rfl⟩)

/-- Guard alignment compares the actual source Boolean with the actual SSA
operand. False is preserved as rejection, not a discarded proof obligation. -/
def Simulation.guard (state : State carriers) (condition : Bool)
    (environment : Domain.Environment carriers) (reference : Nat)
    (read : environment[reference]? = some (.data (.boolean condition))) :
    Simulation (fun source final => source = ((), state) ∧ final = environment)
      (fun _ frame => frame = environment)
      (if condition then .done ((), state) else .halt .reject)
      (Domain.View.guard reference [] environment) := by
  rw [Domain.View.guard_eq reference environment condition read]
  cases condition
  · exact .halt .reject
  · exact .done ⟨rfl, rfl⟩

end Zkc.Construction.Original
