module

public import Zkc.Source.Structured.CommonCoordinate

@[expose] public section

/-! Readback of certified ordinary slices at the actual optional Oracle value boundary.
All operation equations use the existing calculation semantics. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.CommonCoordinate
open NormalForm

variable {model : DomainModel} {scope : Scope}

/-- Only known symbols constrain a runtime component. Unknown is not absence. -/
def Matches {types : List Ty} (symbols : Symbols scope types)
    (observations : Observations model scope)
    (values : Values (Component (ProtocolValue model.toCarriers)) types) : Prop :=
  ∀ {ty} (position : Var types ty) (term : Expression scope ty),
    symbols.get position = some term →
      (values.get position).bind ProtocolValue.toConcrete = observe model term observations

theorem matches_unknown {types : List Ty} (observations : Observations model scope)
    (values : Values (Component (ProtocolValue model.toCarriers)) types) :
    Matches (unknown scope types) observations values := by
  intro ty position term known
  have absent := Values.get_absent (V := Expression scope) position
  rw [unknown, absent] at known
  contradiction

/-- Scalar index values cannot contain a deferred logical data view. -/
theorem index_concrete_at {type : Ty} (value : ProtocolValue model.toCarriers type)
    (same : type = .index) :
    ∃ index : model.Value type, value = ProtocolValue.ofConcrete type index := by
  cases value with
  | concrete atomic value =>
    cases same
    exact ⟨value, by simp only [ProtocolValue.ofConcrete]⟩
  | @deferred sort view =>
    cases sort with
    | sequence => contradiction
    | singleton kind =>
      cases kind with
      | table row rows => cases row <;> contradiction
  | product => contradiction
  | sequence => contradiction

theorem index_concrete (value : ProtocolValue model.toCarriers .index) :
    ∃ index : Nat, value = ProtocolValue.ofConcrete .index index :=
  index_concrete_at value rfl

/-- The exact optional scalar operation, including skipped absent operands. -/
def scalarValues (model : DomainModel) (op : Op) (allowed : scalar op = true)
    (args : Values (Component model.Value) op.arguments) : Values (Component model.Value) op.results :=
  match RoleFamily.sequence args with
  | none => Values.absent model.Value op.results
  | some values => (op.evalTotal model (scalar_total allowed) values).present

set_option maxHeartbeats 2400000 in
set_option linter.unusedSimpArgs false in
theorem scalar_operation {I : PIR.Signature}
    (demand : OracleDataDemandInterpretation model.toCarriers I) (self : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers I)
    (helpers : ProtocolCalculation.Tables model.toCarriers I)
    (op : Op) (allowed : scalar op = true)
    (args : Values (Component (ProtocolValue model.toCarriers)) op.arguments) :
    ProtocolCalculation.operation model demand self ordinary helpers op args =
      .done (ProtocolValue.embedComponents
        (scalarValues model op allowed (ProtocolValue.concreteComponents args))) := by
  cases op <;> simp only [scalar, Bool.false_eq_true] at allowed
  case indexConstant => cases args; rfl
  case indexPowerOfTwo =>
    cases args with | cons first rest =>
      cases rest with | cons second tail =>
        cases tail
        cases first with
        | none =>
          cases second with
          | none => rfl
          | some second =>
            obtain ⟨b, rfl⟩ := index_concrete second
            rfl
        | some first =>
          obtain ⟨a, rfl⟩ := index_concrete first
          cases second with
          | none =>
            change ProtocolCalculation.strict model demand self ordinary .indexPowerOfTwo
              (ProtocolValue.embedComponents (.cons (some a) (.cons none .nil))) rfl = _
            erw [ProtocolCalculation.strict_embed]
            dsimp only [Op.arguments, Op.results, Op.regions]
            simp only [Evaluation.componentOperationOn, strictComponent, Evaluation.meaningOn,
              Evaluation.operationOn, RoleFamily.sequence, scalarValues, Op.evalTotal,
              ProtocolValue.concreteComponents, ProtocolValue.toConcrete_ofConcrete,
              Option.bind_some, Option.bind_none, Values.absent, Values.present,
              ProtocolValue.embedComponents, PIR.Process.bind]
            rfl
          | some second =>
            obtain ⟨b, rfl⟩ := index_concrete second
            change ProtocolCalculation.strict model demand self ordinary .indexPowerOfTwo
              (ProtocolValue.embedComponents (.cons (some a) (.cons (some b) .nil))) rfl = _
            erw [ProtocolCalculation.strict_embed]
            dsimp only [Op.arguments, Op.results, Op.regions]
            simp only [Evaluation.componentOperationOn, strictComponent, Evaluation.meaningOn,
              Evaluation.operationOn, RoleFamily.sequence, scalarValues, Op.evalTotal,
              ProtocolValue.concreteComponents, ProtocolValue.toConcrete_ofConcrete,
              Option.bind_some, Option.bind_none, Values.absent, Values.present,
              ProtocolValue.embedComponents, PIR.Process.bind]
            rfl

  case indexWrappingAdd =>
    cases args with | cons first rest =>
      cases rest with | cons second tail =>
        cases tail
        cases first with
        | none =>
          cases second with
          | none => rfl
          | some second =>
            obtain ⟨b, rfl⟩ := index_concrete second
            rfl
        | some first =>
          obtain ⟨a, rfl⟩ := index_concrete first
          cases second with
          | none =>
            change ProtocolCalculation.strict model demand self ordinary .indexWrappingAdd
              (ProtocolValue.embedComponents (.cons (some a) (.cons none .nil))) rfl = _
            erw [ProtocolCalculation.strict_embed]
            dsimp only [Op.arguments, Op.results, Op.regions]
            simp only [Evaluation.componentOperationOn, strictComponent, Evaluation.meaningOn,
              Evaluation.operationOn, RoleFamily.sequence, scalarValues, Op.evalTotal,
              ProtocolValue.concreteComponents, ProtocolValue.toConcrete_ofConcrete,
              Option.bind_some, Option.bind_none, Values.absent, Values.present,
              ProtocolValue.embedComponents, PIR.Process.bind]
            rfl
          | some second =>
            obtain ⟨b, rfl⟩ := index_concrete second
            change ProtocolCalculation.strict model demand self ordinary .indexWrappingAdd
              (ProtocolValue.embedComponents (.cons (some a) (.cons (some b) .nil))) rfl = _
            erw [ProtocolCalculation.strict_embed]
            dsimp only [Op.arguments, Op.results, Op.regions]
            simp only [Evaluation.componentOperationOn, strictComponent, Evaluation.meaningOn,
              Evaluation.operationOn, RoleFamily.sequence, scalarValues, Op.evalTotal,
              ProtocolValue.concreteComponents, ProtocolValue.toConcrete_ofConcrete,
              Option.bind_some, Option.bind_none, Values.absent, Values.present,
              ProtocolValue.embedComponents, PIR.Process.bind]
            rfl

  case indexWrappingSubtract =>
    cases args with | cons first rest =>
      cases rest with | cons second tail =>
        cases tail
        cases first with
        | none =>
          cases second with
          | none => rfl
          | some second =>
            obtain ⟨b, rfl⟩ := index_concrete second
            rfl
        | some first =>
          obtain ⟨a, rfl⟩ := index_concrete first
          cases second with
          | none =>
            change ProtocolCalculation.strict model demand self ordinary .indexWrappingSubtract
              (ProtocolValue.embedComponents (.cons (some a) (.cons none .nil))) rfl = _
            erw [ProtocolCalculation.strict_embed]
            dsimp only [Op.arguments, Op.results, Op.regions]
            simp only [Evaluation.componentOperationOn, strictComponent, Evaluation.meaningOn,
              Evaluation.operationOn, RoleFamily.sequence, scalarValues, Op.evalTotal,
              ProtocolValue.concreteComponents, ProtocolValue.toConcrete_ofConcrete,
              Option.bind_some, Option.bind_none, Values.absent, Values.present,
              ProtocolValue.embedComponents, PIR.Process.bind]
            rfl
          | some second =>
            obtain ⟨b, rfl⟩ := index_concrete second
            change ProtocolCalculation.strict model demand self ordinary .indexWrappingSubtract
              (ProtocolValue.embedComponents (.cons (some a) (.cons (some b) .nil))) rfl = _
            erw [ProtocolCalculation.strict_embed]
            dsimp only [Op.arguments, Op.results, Op.regions]
            simp only [Evaluation.componentOperationOn, strictComponent, Evaluation.meaningOn,
              Evaluation.operationOn, RoleFamily.sequence, scalarValues, Op.evalTotal,
              ProtocolValue.concreteComponents, ProtocolValue.toConcrete_ofConcrete,
              Option.bind_some, Option.bind_none, Values.absent, Values.present,
              ProtocolValue.embedComponents, PIR.Process.bind]
            rfl

  case indexBitAnd =>
    cases args with | cons first rest =>
      cases rest with | cons second tail =>
        cases tail
        cases first with
        | none =>
          cases second with
          | none => rfl
          | some second =>
            obtain ⟨b, rfl⟩ := index_concrete second
            rfl
        | some first =>
          obtain ⟨a, rfl⟩ := index_concrete first
          cases second with
          | none =>
            change ProtocolCalculation.strict model demand self ordinary .indexBitAnd
              (ProtocolValue.embedComponents (.cons (some a) (.cons none .nil))) rfl = _
            erw [ProtocolCalculation.strict_embed]
            dsimp only [Op.arguments, Op.results, Op.regions]
            simp only [Evaluation.componentOperationOn, strictComponent, Evaluation.meaningOn,
              Evaluation.operationOn, RoleFamily.sequence, scalarValues, Op.evalTotal,
              ProtocolValue.concreteComponents, ProtocolValue.toConcrete_ofConcrete,
              Option.bind_some, Option.bind_none, Values.absent, Values.present,
              ProtocolValue.embedComponents, PIR.Process.bind]
            rfl
          | some second =>
            obtain ⟨b, rfl⟩ := index_concrete second
            change ProtocolCalculation.strict model demand self ordinary .indexBitAnd
              (ProtocolValue.embedComponents (.cons (some a) (.cons (some b) .nil))) rfl = _
            erw [ProtocolCalculation.strict_embed]
            dsimp only [Op.arguments, Op.results, Op.regions]
            simp only [Evaluation.componentOperationOn, strictComponent, Evaluation.meaningOn,
              Evaluation.operationOn, RoleFamily.sequence, scalarValues, Op.evalTotal,
              ProtocolValue.concreteComponents, ProtocolValue.toConcrete_ofConcrete,
              Option.bind_some, Option.bind_none, Values.absent, Values.present,
              ProtocolValue.embedComponents, PIR.Process.bind]
            rfl

  case indexLogicalShiftRight =>
    cases args with | cons first rest =>
      cases rest with | cons second tail =>
        cases tail
        cases first with
        | none =>
          cases second with
          | none => rfl
          | some second =>
            obtain ⟨b, rfl⟩ := index_concrete second
            rfl
        | some first =>
          obtain ⟨a, rfl⟩ := index_concrete first
          cases second with
          | none =>
            change ProtocolCalculation.strict model demand self ordinary .indexLogicalShiftRight
              (ProtocolValue.embedComponents (.cons (some a) (.cons none .nil))) rfl = _
            erw [ProtocolCalculation.strict_embed]
            dsimp only [Op.arguments, Op.results, Op.regions]
            simp only [Evaluation.componentOperationOn, strictComponent, Evaluation.meaningOn,
              Evaluation.operationOn, RoleFamily.sequence, scalarValues, Op.evalTotal,
              ProtocolValue.concreteComponents, ProtocolValue.toConcrete_ofConcrete,
              Option.bind_some, Option.bind_none, Values.absent, Values.present,
              ProtocolValue.embedComponents, PIR.Process.bind]
            rfl
          | some second =>
            obtain ⟨b, rfl⟩ := index_concrete second
            change ProtocolCalculation.strict model demand self ordinary .indexLogicalShiftRight
              (ProtocolValue.embedComponents (.cons (some a) (.cons (some b) .nil))) rfl = _
            erw [ProtocolCalculation.strict_embed]
            dsimp only [Op.arguments, Op.results, Op.regions]
            simp only [Evaluation.componentOperationOn, strictComponent, Evaluation.meaningOn,
              Evaluation.operationOn, RoleFamily.sequence, scalarValues, Op.evalTotal,
              ProtocolValue.concreteComponents, ProtocolValue.toConcrete_ofConcrete,
              Option.bind_some, Option.bind_none, Values.absent, Values.present,
              ProtocolValue.embedComponents, PIR.Process.bind]
            rfl


end Zkc.Source.Structured.CommonCoordinate
