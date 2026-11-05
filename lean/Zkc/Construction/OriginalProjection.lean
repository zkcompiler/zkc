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

private theorem requestValue_forget (origin : Origin) (request : Request)
    (effect : (Domain.effects carriers).Op) :
    (Domain.requestValue origin request effect).interpret forgetCheckpoints =
      Domain.requestValue origin request effect := by
  unfold Domain.requestValue
  split <;> try rfl
  split <;> try rfl
  cases effect <;> try rfl
  all_goals
    simp only [PIR.Process.interpret, forgetCheckpoints, PIR.Process.bind]
    congr 1
    funext reply
    split <;> rfl

private theorem queryRequest_forget (state : State carriers) (origin : Origin)
    (request : Request) :
    (queryRequest state origin request).interpret forgetCheckpoints =
      queryRequest state origin request := by
  simp only [queryRequest, PIR.Process.interpret_bind, requestValue_forget,
    PIR.Process.interpret]

private theorem receiveRequest_forget (routing : Routing) (state : State carriers)
    (ty : Structured.Ty) (site : String) (sender : Nat) :
    (receiveRequest routing state ty site sender).interpret forgetCheckpoints =
      receiveRequest routing state ty site sender := by
  unfold receiveRequest
  split <;> try rfl
  split <;> try rfl
  simp only [PIR.Process.interpret_bind, queryRequest_forget]
  congr 1
  funext result
  split <;> rfl

private theorem receive_forget (routing : Routing) (state : State carriers) (ty : Structured.Ty)
    (site : String) (sender : Nat) :
    (receive routing state ty site sender).interpret forgetCheckpoints =
      receive routing state ty site sender := by
  cases mode : routing.mode with
  | producer =>
      dsimp only [receive]
      simp only [mode]
      cases ty <;> try rfl
      case field field =>
        dsimp only
        split
        · rfl
        · simp only [PIR.Process.interpret_bind, queryField_forget]
          congr 1
      case index => exact receiveRequest_forget _ _ _ _ _
      case indices => exact receiveRequest_forget _ _ _ _ _
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

private theorem service_forget (routing : Routing) (state : State carriers)
    (site contract : String) (request : Request) (handle : Nat) :
    (service routing state site contract request handle).interpret forgetCheckpoints =
      service routing state site contract request handle := by
  unfold service
  split
  · exact queryRequest_forget _ _ _
  · split <;> try rfl
    split <;> try rfl
    simp only [PIR.Process.interpret_bind, requestValue_forget, PIR.Process.interpret]

/-- Every original effect expands to non-checkpoint nominal effects only. -/
theorem operations_forget (routing : Routing)
    (operation : (Structured.Occurrence.signature carriers).Op) (state : State carriers) :
    (operations routing operation state).interpret forgetCheckpoints = operations routing operation state := by
  cases operation with
  | enter => rfl
  | leave => simp only [operations]; split <;> rfl
  | action action =>
      cases action with
      | receive =>
          cases profile : routing.context.profile with
          | fiatShamir _ => simpa only [operations, profile] using receive_forget routing state _ _ _
          | plain =>
              simp only [operations, profile, receivePlain]
              split
              · rfl
              · split <;> rfl
      | send =>
          cases profile : routing.context.profile with
          | fiatShamir _ => simpa only [operations, profile] using send_forget routing state _ _ _ _
          | plain =>
              simp only [operations, profile, sendPlain]
              split <;> rfl
      | query site operation args =>
          cases operation with
          | draw field =>
              cases args with
              | cons handle tail => cases tail; exact query_forget _ _ _ _ _
          | sampleIndex contract =>
              cases args with
              | cons handle tail =>
                  cases tail with
                  | cons bound tail => cases tail; exact service_forget _ _ _ _ _ _
          | sampleIndices contract =>
              cases args with
              | cons handle tail =>
                  cases tail with
                  | cons bound tail =>
                      cases tail with
                      | cons count tail => cases tail; exact service_forget _ _ _ _ _ _

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
