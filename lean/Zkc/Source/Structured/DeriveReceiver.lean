module

public import Zkc.Source.Structured.ReceiverForwarding

@[expose] public section

/-! Discharge transparent marks and logical handle transfers on a process
derived from its source. The operation supplies its own location, scope and
reply ABI. Every other action needs a separate handler law. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.ReceiverForwarding

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  {oracles : List (CheckedOracle snapshot domains math)}
  {ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E}
  {base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E}
  {publish : PIR.MonadHandler m (OraclePublication.Interface model) S E}
  {original : OracleRuntimeState model snapshot domains math S}

theorem inputAt {location : OracleLocation} {roles : Nat → Nat} {sort : OracleLogicalSort}
    {holder self : Nat} {receivers : List Nat} {anchors : model.Value sort.type}
    {bounds : List (String × Nat)} (role : original.self = self)
    (other : self ≠ roles holder) (receives : self ∈ receivers.map roles) :
    Keeps oracles ordinary base publish original
      (.call (.oracle ⟨.input sort holder receivers bounds, location, self, roles,
        .cons none (.cons (some (ProtocolValue.ofConcrete sort.type anchors)) .nil)⟩) .done)
      (.cons (some (ProtocolValue.ofConcrete sort.type anchors)) .nil) := by
  cases role
  exact input oracles ordinary base publish original location roles sort holder receivers anchors other receives bounds

theorem componentsAt {location : OracleLocation} {roles : Nat → Nat} {sort : OracleLogicalSort}
    {holder self : Nat} {receivers : List Nat} {anchors : model.Value sort.type}
    (role : original.self = self) (other : self ≠ roles holder) (receives : self ∈ receivers.map roles) :
    Keeps oracles ordinary base publish original
      (.call (.oracle ⟨.components sort holder receivers, location, self, roles,
        .cons (some (ProtocolValue.ofConcrete sort.type anchors)) .nil⟩) .done)
      (.cons none (.cons (some (ProtocolValue.ofConcrete sort.type anchors)) .nil)) := by
  cases role
  exact components oracles ordinary base publish original location roles sort holder receivers anchors other receives

/-- Solve the returned SSA tuple by following each reached reply. Missing
action laws and incorrect result associations leave unsolved obligations. -/
macro "derive_receiver_returns " os:term:max ord:term:max base:term:max pub:term:max
    original:term:max role:term:max : tactic => `(tactic|
  (repeat' (apply PIR.Process.ReturnsUnder.call
            first
            | exact Zkc.Source.Structured.ReceiverForwarding.mark $os $ord $base $pub $original _ _
            | with_unfolding_all apply Zkc.Source.Structured.ReceiverForwarding.inputAt (oracles := $os) (ordinary := $ord) (base := $base) (publish := $pub) $role <;> (apply of_decide_eq_true; rfl)
            | with_unfolding_all apply Zkc.Source.Structured.ReceiverForwarding.componentsAt (oracles := $os) (ordinary := $ord) (base := $base) (publish := $pub) $role <;> (apply of_decide_eq_true; rfl))
   apply PIR.Process.ReturnsUnder.done))

end Zkc.Source.Structured.ReceiverForwarding
