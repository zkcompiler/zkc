import ZkcExamples.Structured.SumcheckSourceSelections

set_option autoImplicit false
namespace Tests.SumcheckSourceProperties
open Zkc.Source Zkc.Source.Structured ReferenceLibrary
open ZkcExamples.Structured SumcheckSourceSelections
open Generated.Bindings
variable (model : DomainModel) (selection : Selection)

/-- These are the actual admitted helpers, including the outer TwoSums chain. -/
theorem actual_sum (xs : List (model.Field field)) :
    invoke (Multilinear.closed model (definitions := (source selection).payload.definitions))
      (Sum.totalHelper field sumBindings) (.cons xs .nil) =
      primitiveOutcome (Sum.totalOutcome model field xs) :=
  Sum.total_eq model (source selection).payload.linked (sumBodies model selection) xs

theorem actual_outer_sum (xs : List (model.Field field)) :
    invoke (Multilinear.closed model (definitions := (source .twoSums).payload.definitions))
      (Sum.totalHelper field outerSumBindings) (.cons xs .nil) =
      primitiveOutcome (Sum.totalOutcome model field xs) :=
  Sum.total_eq model (source .twoSums).payload.linked (outerSumBodies model) xs

theorem actual_scalar (xs : List (model.Field field)) (scalar : model.Field field) :
    invoke (Multilinear.closed model (definitions := (source .small).payload.definitions))
      SmallSumcheckInputs.helper4Helper (.cons xs (.cons scalar .nil)) =
      primitiveOutcome ((Sum.scalarRelation model field sumBindings).reference (.cons xs (.cons scalar .nil))) :=
  Sum.scalar_eq model (source .small).payload.linked (sumBodies model .small) _ (scalarBody model) xs scalar

theorem actual_pair (xs ys : List (model.Field field)) (a b : model.Field field) :
    invoke (Multilinear.closed model (definitions := (source .twoSums).payload.definitions))
      TwoSumsInputs.helper4Helper (.cons xs (.cons ys (.cons a (.cons b .nil)))) =
      primitiveOutcome ((Sum.pairRelation model field outerSumBindings).reference
        (.cons xs (.cons ys (.cons a (.cons b .nil))))) :=
  Sum.pair_eq model (source .twoSums).payload.linked (outerSumBodies model) _ (pairBody model) xs ys a b

theorem actual_pending (xs point : List (model.Field field)) (n w : Nat) (scalar : model.Field field) :
    invoke (Multilinear.closed model (definitions := (source selection).payload.definitions))
      SmallSumcheckInputs.helper14Helper (.cons xs (.cons n (.cons w (.cons point (.cons scalar .nil))))) =
      primitiveOutcome ((Sum.pendingRelation model field sumBindings bindings.values).reference
        (.cons xs (.cons n (.cons w (.cons point (.cons scalar .nil)))))) :=
  Sum.pending_eq model (source selection).payload.linked (sumBodies model selection)
    _ (roundBodies selection).toBodies (wrappers model selection).pending xs point n w scalar

theorem actual_table_shape (xs : List (model.Field field)) (n w : Nat) :
    invoke (Multilinear.closed model (definitions := (source selection).payload.definitions))
      SmallSumcheckInputs.helper13Helper (.cons xs (.cons n (.cons w .nil))) =
      .done (.cons (decide (w=1 ∧ xs.length=2^n)) .nil) :=
  Sum.tableShape_eq model (source selection).payload.linked _ (roundBodies selection).toBodies
    (wrappers model selection).tableShape xs n w

theorem actual_input_shape (xs : List (model.Field field)) (n : Nat) :
    invoke (Multilinear.closed model (definitions := (source selection).payload.definitions))
      ⟨shapeName selection, .math, [.vector field, .index], [.boolean]⟩ (.cons xs (.cons n .nil)) =
      primitiveOutcome ((Sum.inputShape model field (maximum selection)).reference (.cons xs (.cons n .nil))) :=
  (Sum.inputShape model field (maximum selection)).invoke (model := model)
    (helper := ⟨shapeName selection, .math, [.vector field, .index], [.boolean]⟩)
    _ (source selection).payload.linked (shapeBody model selection) _ trivial

theorem actual_initial (scalar : model.Field field) :
    invoke (Multilinear.closed model (definitions := (source selection).payload.definitions))
      SmallSumcheckInputs.helper9Helper (.cons scalar .nil) = .done (.cons [] (.cons scalar .nil)) :=
  (Sum.initial model field "s0").invoke (model := model) (helper := SmallSumcheckInputs.helper9Helper)
    _ (source selection).payload.linked (wrappers model selection).initial _ trivial

theorem actual_identity (point : List (model.Field field)) (scalar : model.Field field) :
    invoke (Multilinear.closed model (definitions := (source selection).payload.definitions))
      TwoSumsInputs.helper24Helper (.cons point (.cons scalar .nil)) = .done (.cons point (.cons scalar .nil)) :=
  (Sum.identity model field).invoke (model := model) (helper := TwoSumsInputs.helper24Helper)
    _ (source selection).payload.linked (wrappers model selection).atPrefix _ trivial

theorem actual_both (a b : Bool) :
    invoke (Multilinear.closed model (definitions := (source .twoSums).payload.definitions))
      TwoSumsInputs.helper25Helper (.cons a (.cons b .nil)) = .done (.cons (a && b) .nil) :=
  (Sum.both model).invoke (model := model) (helper := TwoSumsInputs.helper25Helper)
    _ (source .twoSums).payload.linked (bothBody model) _ trivial

/-- Actual complete reduction bodies, selected once, share the nominal theorem. -/
theorem actual_reduction (ctx : ProtocolContext) (distinct : NormalForm.RosterDistinct ctx 1 2)
    (point : Option (List (model.Field field))) (scalar : Option (model.Field field))
    (count service : Option Nat) :
    (reduction selection).denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions
        (SumcheckReferenceInstallation.tables model (source selection).payload.definitions)
        (ctx.roles 1) (Occurrence.table model (source selection).payload) ctx Occurrence.iterations)
      (SumcheckReductionReference.pattern.environment model
        (SumcheckReductionReference.inputs model point scalar count service)).get =
      SumcheckReductionReference.reference model (source selection).payload.definitions
        (Occurrence.table model (source selection).payload) (maximum selection) ctx point scalar count service := by
  rw [reduction_selected]
  exact SumcheckReductionReference.body_reference model _ (source selection).payload.linked
    (SumcheckReductionReference.actual_bodies model selection) _ _ ctx distinct point scalar count service

/-- Shape rejection is a returned false, independent of any scalar claim. -/
theorem bad_table (xs : List (model.Field field)) (n w : Nat) (bad : w ≠ 1 ∨ xs.length ≠ 2^n) :
    invoke (Multilinear.closed model (definitions := (source selection).payload.definitions))
      SmallSumcheckInputs.helper13Helper (.cons xs (.cons n (.cons w .nil))) = .done (.cons false .nil) := by
  rw [actual_table_shape]
  rcases bad with bad | bad <;> simp [bad]

theorem exhausted_sum (xs : List (model.Field field)) (missing : ¬ xs.length < indexLimit) :
    invoke (Multilinear.closed model (definitions := (source selection).payload.definitions))
      (Sum.totalHelper field sumBindings) (.cons xs .nil) = .halt .exhausted := by
  rw [actual_sum]
  simp only [Sum.totalOutcome, missing, ↓reduceIte, primitiveOutcome]
  rfl

theorem false_scalar (xs : List (model.Field field)) (scalar : model.Field field)
    (bound : xs.length < indexLimit) (wrong : scalar ≠ xs.sum) :
    invoke (Multilinear.closed model (definitions := (source .small).payload.definitions))
      SmallSumcheckInputs.helper4Helper (.cons xs (.cons scalar .nil)) = .done (.cons false .nil) := by
  rw [actual_scalar]
  simp [Sum.scalarRelation, bound, wrong, primitiveOutcome]

/-- Complete dependency signatures, rather than just names, select the law. -/
example : True := by
  fail_if_success
    have : Sum.Bodies model (source .small).payload.definitions field
        {sumBindings with add := "changed_dependency"} := by
      select_reference_bodies
  trivial

#print axioms actual_sum
#print axioms actual_pair
#print axioms actual_pending
#print axioms actual_reduction
#print axioms exhausted_sum
end Tests.SumcheckSourceProperties
