module

public import Zkc.Source.Structured.OracleInvariant
public import Zkc.Source.Structured.ProtocolCalculation

@[expose] public section

/-! A returned, visible virtual installation selects the checked declaration
and saves its actual captures above the old registry. Failed validation and
duplicate construction cannot supply a handle. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.OracleExecution
attribute [local implicit_reducible] OracleOp.arguments OracleOp.results
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}

theorem capturesPresent_embed {types : List Ty} (values : Values model.Value types) :
    capturesPresent (ProtocolValue.embedComponents (carriers := model.toCarriers) values.present) = some values := by
  induction values with
  | nil => rfl
  | @cons ty rest value tail ih =>
    change ((ProtocolValue.ofConcrete ty value).toConcrete >>= fun concrete ↦
      capturesPresent (ProtocolValue.embedComponents tail.present) >>= fun values ↦
        some (Values.cons concrete values)) = _
    rw [ProtocolValue.toConcrete_ofConcrete]
    change (capturesPresent (ProtocolValue.embedComponents tail.present) >>= fun values ↦ some (Values.cons value values)) = _
    rw [ih]
    rfl

theorem virtual_returned (oracles : List (CheckedOracle snapshot domains math))
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (checked : CheckedOracle snapshot domains math) (sig : OracleSignature)
    (selected : oracles.find? (fun entry ↦ entry.declaration.signature == sig) = some checked)
    (same : checked.declaration.signature = sig) (site : OracleLocation) (roles : Nat → Nat)
    (holder : Nat) (receivers : List Nat) (values : Values model.Value sig.inputs.dropLast)
    (rows : Nat) (declared : declaredRows sig values = some rows)
    (before : OracleRuntimeState model snapshot domains math S)
    (self : Nat) (active : self = before.self)
    (visible : OracleStore.visible before.self (roles holder) (receivers.map roles) = true) :
    let result := operation model oracles base site self roles (.virtual sig holder receivers)
      (ProtocolValue.embedComponents values.present) before
    let table : OracleStoredTable model snapshot domains math sig.kind.answer :=
      ⟨site.anchor, rows, roles holder, receivers.map roles,
        .virtual checked (congrArg (fun signature ↦ signature.kind.answer) same)
          ((congrArg (fun signature ↦ signature.inputs.dropLast) same).symm ▸ values)⟩
    ∀ reply, result.outcome = .returned reply →
      reply = .cons (some (ProtocolValue.ofConcrete (.oracle sig.kind) site.anchor)) .nil ∧
      result.state = {before with entries := ⟨sig.kind.answer, table⟩ :: before.entries} := by
  subst sig self
  have active : (before.self != before.self) = false := by simp
  simp only [operation, active, Bool.false_eq_true, ↓reduceIte, visible, Bool.not_true, selected,
    ↓reduceDIte]
  rw [capturesPresent_embed (model := model) values]
  dsimp only
  rw [declared]
  dsimp only
  split
  · intro _ eq; cases eq
  · split
    · intro _ eq; cases eq
    · rename_i entries inserted
      have extended := (OracleStore.insert_some inserted).1
      intro reply success
      exact ⟨(PIR.Outcome.returned.inj success).symm, congrArg (fun es ↦ {before with entries := es}) extended⟩

end Zkc.Source.Structured.OracleExecution
