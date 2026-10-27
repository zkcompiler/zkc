module

public import Zkc.Source.Structured.DomainContract

@[expose] public section

/-! Request-fixed relation meaning. A formula is its admitted helper invocation;
an opaque relation is the exact binding in the request's admitted registry.
No mathematical predicate is accepted from proof evidence. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

inductive RelationMeaning {snapshot : Snapshot} (imported : Imported snapshot)
    {application : RelationApplication} (relation : RelationBinding snapshot application)
    (Value : Ty → Type) (registry : OpaqueRegistry Value) where
  | formula (binding : FormulaBinding imported relation)
  | opaque (binding : OpaqueRegistry.Binding registry relation.declaration)

namespace RelationMeaning
variable {snapshot : Snapshot} {imported : Imported snapshot}
  {application : RelationApplication} {relation : RelationBinding snapshot application}
  {model : DomainModel} {registry : OpaqueRegistry model.Value}

/-- Stops and completed false results both fail truth, without identifying them. -/
def HoldsOn (meaning : RelationMeaning imported relation model.Value registry)
    (booleanOutput : relation.declaration.outputs = [.boolean])
    (arguments : Values model.Value relation.declaration.inputs) : Prop :=
  match meaning with
  | .formula binding => binding.invokeRelationOn model arguments =
      .done (booleanOutput.symm ▸ Values.cons true .nil)
  | .opaque binding => binding.Holds arguments

@[simp] theorem formula_holds (binding : FormulaBinding imported relation)
    (booleanOutput : relation.declaration.outputs = [.boolean])
    (arguments : Values model.Value relation.declaration.inputs) :
    (RelationMeaning.formula binding : RelationMeaning imported relation model.Value registry).HoldsOn
      booleanOutput arguments ↔ binding.invokeRelationOn model arguments =
        .done (booleanOutput.symm ▸ Values.cons true .nil) := Iff.rfl

@[simp] theorem opaque_holds (binding : OpaqueRegistry.Binding registry relation.declaration)
    (booleanOutput : relation.declaration.outputs = [.boolean])
    (arguments : Values model.Value relation.declaration.inputs) :
    (RelationMeaning.opaque binding : RelationMeaning imported relation model.Value registry).HoldsOn
      booleanOutput arguments ↔ binding.Holds arguments := Iff.rfl

/-- Replacing a proof of the same fixed lookup cannot replace its meaning. -/
theorem unique_meaning (first second : RelationMeaning imported relation model.Value registry)
    (booleanOutput : relation.declaration.outputs = [.boolean])
    (arguments : Values model.Value relation.declaration.inputs) :
    first.HoldsOn booleanOutput arguments ↔ second.HoldsOn booleanOutput arguments := by
  cases first with
  | formula first =>
      cases second with
      | formula second =>
          have names := Option.some.inj (first.formula_eq.symm.trans second.formula_eq)
          simp only [HoldsOn, FormulaBinding.invokeRelationOn]
          rw [names]
      | «opaque» second => exact False.elim (by
          have same := first.formula_eq
          rw [second.noFormula] at same
          contradiction)
  | «opaque» first =>
      cases second with
      | formula second => exact False.elim (by
          have same := second.formula_eq
          rw [first.noFormula] at same
          contradiction)
      | «opaque» second => exact first.unique_meaning second arguments

/-- Any binding of a formula declaration has its original completed-true
meaning. This also excludes an opaque interpretation of that declaration. -/
theorem formula_exact (meaning : RelationMeaning imported relation model.Value registry)
    (binding : FormulaBinding imported relation)
    (booleanOutput : relation.declaration.outputs = [.boolean])
    (arguments : Values model.Value relation.declaration.inputs) :
    meaning.HoldsOn booleanOutput arguments ↔ binding.invokeRelationOn model arguments =
      .done (booleanOutput.symm ▸ Values.cons true .nil) :=
  meaning.unique_meaning (.formula binding) booleanOutput arguments

/-- The shared boundary denotes the existing logical translation at the exact
relation-table position. Registry admission supplies lookup, not a new law. -/
theorem holds_iff_logical (environment : RelationEnvironmentOn imported model.toCarriers)
    (meaning : RelationMeaning imported relation model.Value environment.registry)
    (booleanOutput : relation.declaration.outputs = [.boolean])
    (arguments : Values model.Value relation.declaration.inputs) :
    meaning.HoldsOn booleanOutput arguments ↔
      Logical.relationMeaningOn model environment relation.index arguments := by
  cases meaning with
  | formula binding =>
      unfold HoldsOn Logical.relationMeaningOn
      change binding.invokeRelationOn model arguments = _ ↔
        (match relation.declaration.formula with
        | some name => ∃ boolean : relation.declaration.outputs = [.boolean],
            invoke (closedMeaningsOn model imported.program.payload.definitions)
              ⟨name, .math, relation.declaration.inputs, relation.declaration.outputs⟩
              arguments = .done (boolean.symm ▸ Values.cons true .nil)
        | none => environment.meanings relation.index arguments)
      rw [binding.formula_eq]
      exact ⟨fun truth => ⟨booleanOutput, truth⟩, fun ⟨_, truth⟩ => truth⟩
  | «opaque» binding =>
      unfold HoldsOn Logical.relationMeaningOn
      change binding.Holds arguments ↔
        (match relation.declaration.formula with
        | some name => ∃ boolean : relation.declaration.outputs = [.boolean],
            invoke (closedMeaningsOn model imported.program.payload.definitions)
              ⟨name, .math, relation.declaration.inputs, relation.declaration.outputs⟩
              arguments = .done (boolean.symm ▸ Values.cons true .nil)
        | none => environment.meanings relation.index arguments)
      rw [binding.noFormula]
      exact (environment.meanings_exact relation.index binding arguments).symm

/-- Uniform clients use the domain semantics at their existing ring model. -/
theorem holds_iff_uniform_logical {F G : Type}
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (environment : RelationEnvironment imported F G)
    (meaning : RelationMeaning imported relation (assignment F G) environment.registry)
    (booleanOutput : relation.declaration.outputs = [.boolean])
    (arguments : Values (assignment F G) relation.declaration.inputs) :
    meaning.HoldsOn (model := ringModel F G) booleanOutput arguments ↔
      Logical.relationMeaning environment relation.index arguments := by
  exact (meaning.holds_iff_logical (model := ringModel F G) environment.toOn booleanOutput arguments).trans
    (Iff.of_eq (Logical.relationMeaning_eq_relationMeaningOn environment relation.index arguments).symm)

end RelationMeaning

end Zkc.Source.Structured
