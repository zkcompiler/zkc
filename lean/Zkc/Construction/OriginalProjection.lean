module

public import Zkc.Construction.OriginalSimulation

@[expose] public section

/-! The original-derived fold never emits physical SSA checkpoints. Thus its
source projection recovers the exact original fold, while the paired view
retains the certified constructed frames for complete runtime transport. -/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers} {A : Type}

private theorem queryField_forget (state : State carriers) (origin : Origin) (field : String) :
    (queryField state origin field).interpret forgetCheckpoints = queryField state origin field := by
  unfold queryField
  split <;> rfl

private theorem record_forget (state : State carriers) (origin : Origin) (payload : Domain.Payload carriers) :
    (record state origin payload).interpret forgetCheckpoints = record state origin payload := rfl

private theorem receive_forget (routing : Routing) (state : State carriers) (ty : Structured.Ty)
    (site : String) (sender : Nat) :
    (receive routing state ty site sender).interpret forgetCheckpoints =
      receive routing state ty site sender := by
  cases mode : routing.mode with
  | producer =>
      dsimp only [receive]
      simp only [mode]
      cases ty <;> try rfl
      dsimp only
      split
      · rfl
      · simp only [PIR.Process.interpret_bind, queryField_forget]
        congr 1
  | validator =>
      dsimp only [receive]
      simp only [mode]
      split
      · rfl
      · simp only [PIR.Process.interpret, forgetCheckpoints, PIR.Process.bind]
        congr 1
        funext value
        split
        · rfl
        · simp only [PIR.Process.interpret_bind, record_forget, PIR.Process.interpret]

private theorem send_forget (routing : Routing) (state : State carriers) (ty : Structured.Ty)
    (site : String) (receiver : Nat) (value : carriers.Value ty) :
    (send routing state ty site receiver value).interpret forgetCheckpoints =
      send routing state ty site receiver value := by
  cases mode : routing.mode <;> simp only [send, mode]
  all_goals split <;> rfl

private theorem query_forget (routing : Routing) (state : State carriers)
    (site field : String) (handle : Nat) :
    (query routing state site field handle).interpret forgetCheckpoints =
      query routing state site field handle := by
  unfold query
  split
  · exact queryField_forget _ _ _
  · split
    · split <;> rfl
    · rfl

/-- Every original effect expands to non-checkpoint nominal effects only. -/
theorem operations_forget (routing : Routing)
    (operation : (Structured.Occurrence.signature carriers).Op) (state : State carriers) :
    (operations routing operation state).interpret forgetCheckpoints = operations routing operation state := by
  cases operation with
  | enter => rfl
  | leave => simp only [operations]; split <;> rfl
  | action action =>
      cases action with
      | receive => exact receive_forget _ _ _ _ _
      | send => exact send_forget _ _ _ _ _ _
      | query site field args =>
          cases args with
          | cons handle tail => cases tail; exact query_forget _ _ _ _ _

/-- Erasing physical checkpoints is the identity on the complete original fold,
including original values, construction state, all replies and all stops. -/
theorem fold_forget (routing : Routing)
    (source : PIR.Process (Structured.Occurrence.signature carriers) A) (state : State carriers) :
    (fold routing source state).interpret forgetCheckpoints = fold routing source state := by
  unfold fold
  rw [PIR.Process.interpretState_interchange]
  congr 1
  funext operation current
  exact operations_forget routing operation current

/-- A certified paired view projects to the exact construction of the original,
not just to a checkpoint-erased source chosen from compiled instructions. -/
theorem Simulation.original_source {B : Type}
    {returns : (A × State carriers) → B → Prop}
    {live : PIR.Process (Domain.effects carriers) (A × State carriers) → Domain.Environment carriers → Prop}
    (routing : Routing) (source : PIR.Process (Structured.Occurrence.signature carriers) A)
    (state : State carriers) {target : PIR.Process (Domain.effects carriers) B}
    (derivation : Simulation returns live (fold routing source state) target) :
    (derivation.paired.bind (fun pair => .done pair.1)).interpret forgetCheckpoints =
      fold routing source state :=
  derivation.source.trans (fold_forget routing source state)

end Zkc.Construction.Original
