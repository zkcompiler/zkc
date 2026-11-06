module

public import Zkc.Semantics.HandlerReturn
public import Zkc.Source.Structured.OracleForwarding
public import Zkc.Source.Structured.OracleLocalAction

@[expose] public section

/-! Logical forwarding under an arbitrary publication experiment. The source
frame may advance. Its immutable table, provider state and query count stay
fixed, even on stops. Any returned handles must belong to the input pair. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.ReceiverForwarding
open Zkc
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}
  {m : Type → Type} [Monad m] [LawfulMonad m]
  (oracles : List (CheckedOracle snapshot domains math))
  (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
  (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
  (publish : PIR.MonadHandler m (OraclePublication.Interface model) S E)
  (original : OracleRuntimeState model snapshot domains math S)

abbrev Keeps {A : Type} (process : PIR.Process (OracleProtocol.Interface model) A) (value : A) :=
  PIR.Process.ReturnsUnder (OraclePublication.actionM model oracles ordinary base publish)
    (fun state ↦ state.oracle = original) process value

theorem mark (source observed : String) :
    Keeps oracles ordinary base publish original (.call (.mark source observed) .done) () := by
  apply PIR.Process.ReturnsUnder.action
  intro state same
  rw [OraclePublication.actionM_local _ _ _ _ _ _ rfl]
  simp only [OracleProtocol.handler]
  split <;> apply MonadicPostcondition.pure
  · exact ⟨same, by intro _ eq; cases eq⟩
  · exact ⟨same, by simp⟩

private theorem checked (request : OracleRequest model.toCarriers)
    (closed : OraclePublication.localAction (.oracle request) = true)
    (value : (oracleInterface model.toCarriers).Reply request)
    (localLaw : ∀ location,
      let result := OracleExecution.operation model oracles (OracleProcess.refusingBase (E := E))
        location request.self request.roles request.operation request.arguments original
      result.state = original ∧ ∀ out, result.outcome = .returned out → out = value) :
    Keeps oracles ordinary base publish original (.call (.oracle request) .done) value := by
  apply PIR.Process.ReturnsUnder.action
  intro state same
  rw [OraclePublication.actionM_local _ _ _ _ _ _ closed]
  apply MonadicPostcondition.pure
  simp only [OracleProtocol.handler]
  split
  · exact ⟨same, by intro _ eq; cases eq⟩
  · simp only [same]
    exact localLaw _

variable (location : OracleLocation) (roles : Nat → Nat) (sort : OracleLogicalSort)
  (holder : Nat) (receivers : List Nat) (anchors : model.Value sort.type)
  (other : original.self ≠ roles holder) (receives : original.self ∈ receivers.map roles)

include other receives in
theorem input (bounds : List (String × Nat)) :
    Keeps oracles ordinary base publish original
      (.call (.oracle ⟨.input sort holder receivers bounds, location, original.self, roles,
        .cons none (.cons (some (ProtocolValue.ofConcrete sort.type anchors)) .nil)⟩) .done)
      (.cons (some (ProtocolValue.ofConcrete sort.type anchors)) .nil) := by
  apply checked _ _ _ _ _ _ rfl
  intro actual
  dsimp only
  rw [OracleExecution.receiver_input original oracles OracleProcess.refusingBase actual roles sort
    holder receivers anchors other receives bounds]
  split
  · exact ⟨rfl, fun _ eq ↦ (PIR.Outcome.returned.inj eq).symm⟩
  · exact ⟨rfl, by intro _ eq; cases eq⟩

include other receives in
theorem components :
    Keeps oracles ordinary base publish original
      (.call (.oracle ⟨.components sort holder receivers, location, original.self, roles,
        .cons (some (ProtocolValue.ofConcrete sort.type anchors)) .nil⟩) .done)
      (.cons none (.cons (some (ProtocolValue.ofConcrete sort.type anchors)) .nil)) := by
  apply checked _ _ _ _ _ _ rfl
  intro actual
  dsimp only
  rw [OracleExecution.receiver_components original oracles OracleProcess.refusingBase actual roles sort
    holder receivers anchors other receives]
  split
  · exact ⟨rfl, fun _ eq ↦ (PIR.Outcome.returned.inj eq).symm⟩
  · exact ⟨rfl, by intro _ eq; cases eq⟩

end Zkc.Source.Structured.ReceiverForwarding
