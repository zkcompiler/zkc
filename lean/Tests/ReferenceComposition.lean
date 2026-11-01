import ZkcTools.StructuredSource.ReferenceComposition
import ZkcTools.StructuredSource.HelperPresentation
import Zkc.Source.Structured.MapLaws
import Zkc.Protocols.Multilinear.Source.CollectBodies
import Tests.ReusableAggregateTwoBatchesBodies

/-! Structural composition controls use actual aggregate-bearing TwoBatches
source and an alternate scalar formula with heterogeneous broadcast captures.
Synthetic callback tables below make no source-association claim. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Tests.ReferenceComposition
open Zkc.Source Zkc.Source.Structured
open Tests.ReusableAggregateTwoBatchesBodies

/-- The actual aggregate input and silent marker survive direct transport of
an arbitrary explicit dependency, without classifying its helper name. -/
def twoBatches (model : DomainModel)
    (dependency : ReferenceLaw model mathematicalAdmissionHelper.inputs
      mathematicalAdmissionHelper.outputs) :=
  forward_reference% checkBatchBody using dependency

example (model : DomainModel)
    (dependency : ReferenceLaw model mathematicalAdmissionHelper.inputs
      mathematicalAdmissionHelper.outputs) : (twoBatches model dependency).body = checkBatchBody := rfl

example (model : DomainModel)
    (dependency : ReferenceLaw model mathematicalAdmissionHelper.inputs
      mathematicalAdmissionHelper.outputs)
    (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (available : dependency.Realizes (helper := mathematicalAdmissionHelper) table)
    (arguments : Values model.Value checkBatchHelper.inputs) :
    checkBatchBody.denote (Evaluation.meaningOn model SiteObservations.closed table) arguments.get =
      primitiveOutcome ((twoBatches model dependency).reference arguments) :=
  (twoBatches model dependency).valid table arguments (available _)

private abbrev field : Ty := .field "bls12-381.fr"
private abbrev vector : Ty := .vector "bls12-381.fr"

private def leaf : Helper := ⟨"ordered-results", .math,
  [.boolean, vector, .index], [.index, .boolean, vector]⟩

private def leafLaw (model : DomainModel) :=
  ReferenceLibrary.projection model
    (.cons (.there (.there .here)) (.cons .here (.cons (.there .here) .nil)) :
      Operands leaf.inputs leaf.outputs)

private def forwardingBody : Region dialect [.boolean, vector, .index, field] leaf.outputs :=
  .letOp (.invoke leaf)
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil
    (.ret (ReferenceLibrary.resultOperands leaf.outputs _))

private def forwarded (model : DomainModel) :=
  forward_reference% forwardingBody using (leafLaw model)

-- Every heterogeneous result is retained, in its declared order.
example (model : DomainModel) (accepted : Bool) (batch : List (model.Field "bls12-381.fr"))
    (index : Nat) (unused : model.Field "bls12-381.fr") :
    (forwarded model).reference (.cons accepted (.cons batch (.cons index (.cons unused .nil)))) =
      .returned (.cons index (.cons accepted (.cons batch .nil))) := rfl

private def changedReturn : Region dialect [.boolean, vector, .index, field] leaf.outputs :=
  .letOp (.invoke leaf)
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil
    (.ret (.cons ((Var.there (Var.there Var.here)).weakenPrefix leaf.outputs)
      (.cons (.there .here) (.cons (.there (.there .here)) .nil))))

/-- error: reference composition does not preserve the complete actual body -/
#guard_msgs in
example (model : DomainModel) := forward_reference% changedReturn using (leafLaw model)

/-- error: reference composition expects a forwarding operation with a complete return -/
#guard_msgs in
example (model : DomainModel) := forward_reference% (leafLaw model).body using (leafLaw model)

private def guardedHelper : Helper := ⟨"guarded-result", .math, [.boolean], [.boolean]⟩

/-- The success reference is conditional on the actual guard, not all inputs. -/
private def guardedLaw (model : DomainModel) :
    ReferenceLaw model guardedHelper.inputs guardedHelper.outputs where
  body := .letOp .guard (.cons .here .nil) .nil (.ret (.cons .here .nil))
  Requires _ arguments := arguments.get .here = true
  reference _ := .returned (.cons true .nil)
  valid _ arguments accepted := by
    cases arguments with
    | cons decision rest =>
      cases rest
      change decision = true at accepted
      subst decision
      rfl

private def guardedBody : Region dialect [.boolean, .index] [.boolean] :=
  .letOp (.invoke guardedHelper) (.cons .here .nil) .nil
    (.ret (ReferenceLibrary.resultOperands [.boolean] _))

private def guardedForward (model : DomainModel) :=
  forward_reference% guardedBody using (guardedLaw model)

/-- Body association and the condition at this input suffice. No unconditional
success theorem for the helper is available or required. -/
theorem conditional_forward (model : DomainModel) (definitions : List CheckedDefinition)
    (linked : DeclarationsLinked [] definitions)
    (associated : BodyIn definitions guardedHelper (guardedLaw model).body)
    (decision : Bool) (unused : Nat) (accepted : decision = true) :
    guardedBody.denote
      (Evaluation.meaningOn model SiteObservations.closed (closedMeaningsOn model definitions))
      (Values.cons decision (.cons unused .nil)).get = .done (.cons true .nil) :=
  (guardedForward model).valid _ _
    ((guardedLaw model).invoke definitions linked associated (.cons decision .nil) accepted)

private def guardedTable (model : DomainModel) :
    Evaluation.MeaningsOn model.toCarriers closedInterface :=
  [⟨guardedHelper, fun arguments => (guardedLaw model).body.denote
    (Evaluation.meaningOn model SiteObservations.closed []) arguments.get⟩]

example (model : DomainModel) (unused : Nat) :
    guardedBody.denote (Evaluation.meaningOn model SiteObservations.closed (guardedTable model))
      (Values.cons true (.cons unused .nil)).get = .done (.cons true .nil) := by
  apply (guardedForward model).valid _ _
  change invoke (guardedTable model) guardedHelper (.cons true .nil) = .done (.cons true .nil)
  rw [guardedTable, invoke_cons_same]
  exact (guardedLaw model).valid [] (.cons true .nil) rfl

-- The same table really refuses the input outside the precondition.
private theorem guarded_rejected (model : DomainModel) :
    invoke (guardedTable model) guardedHelper (.cons false .nil) = .halt .reject := by
  rw [guardedTable, invoke_cons_same]
  rfl

private theorem guarded_requires_refused (model : DomainModel) :
    ¬ (guardedForward model).Requires (guardedTable model) (.cons false (.cons 0 .nil)) := by
  intro premise
  change invoke (guardedTable model) guardedHelper (.cons false .nil) = .done (.cons true .nil) at premise
  rw [guarded_rejected] at premise
  cases premise

example (model : DomainModel) :
    ¬ (guardedLaw model).Realizes (helper := guardedHelper) (guardedTable model) := by
  intro total
  exact guarded_requires_refused model (total _)

private def stoppedLaw (model : DomainModel) (reason : PIR.Stop) :
    ReferenceLaw model guardedHelper.inputs guardedHelper.outputs where
  body := .stop reason
  Requires _ _ := True
  reference _ := .stopped reason
  valid _ _ _ := rfl

private def stoppedForward (model : DomainModel) (reason : PIR.Stop) :=
  forward_reference% guardedBody using (stoppedLaw model reason)

-- Pointwise forwarding retains any exact dependency stop.
example (model : DomainModel) (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (reason : PIR.Stop) (decision : Bool) (unused : Nat)
    (dependency : invoke table guardedHelper (.cons decision .nil) = .halt reason) :
    guardedBody.denote (Evaluation.meaningOn model SiteObservations.closed table)
      (Values.cons decision (.cons unused .nil)).get = .halt reason :=
  (stoppedForward model reason).valid table (.cons decision (.cons unused .nil)) dependency

private def spec : CollectSpec :=
  { ZkcExamples.Structured.MultilinearCollectBodies.collectSpec
      ⟨"difference", "rows", "callback", "unused"⟩ with
    captures := [.boolean, .index] }

private def collectionBody : Region dialect (spec.domain.inputs ++ spec.captures)
    [spec.collection.type] :=
  .letOp (.collect spec) (Operands.identity _) .nil
    (.ret (ReferenceLibrary.resultOperands [spec.collection.type] _))

helper_presentation Difference inputs [low, high, enabled, offset] outputs [values] := collectionBody

private def library :=
  collection_reference% collectionBody with_model (ringModel Int Int)
    with_shape (fun low high _ _ => Evaluation.mapShape [low.length, high.length])
    with_items (fun low high _ _ index =>
      .cons (low[index]?.getD 0) (.cons (high[index]?.getD 0) .nil))
    with_formula (fun low high _ _ enabled offset =>
      (if enabled then low - high else high - low) + (offset : Int))

private def filtered : CollectSpec := { spec with predicate := "selected" }

private def filteredBody : Region dialect (filtered.domain.inputs ++ filtered.captures)
    [filtered.collection.type] :=
  .letOp (.collect filtered) (Operands.identity _) .nil
    (.ret (ReferenceLibrary.resultOperands [filtered.collection.type] _))

/-- error: collection_reference% requires an unfiltered collection -/
#guard_msgs in
example := collection_reference% filteredBody with_model (ringModel Int Int)
  with_shape (fun low high _ _ => Evaluation.mapShape [low.length, high.length])
  with_items (fun low high _ _ index =>
    .cons (low[index]?.getD 0) (.cons (high[index]?.getD 0) .nil))
  with_formula (fun low high _ _ enabled offset =>
    (if enabled then low - high else high - low) + (offset : Int))

private def reference (low high : List Int) (enabled : Bool) (offset : Nat) :
    PIR.Outcome (Difference.Output (ringModel Int Int)) :=
  match Evaluation.mapShape [low.length, high.length] with
  | .stopped reason => .stopped reason
  | .returned length => .returned ⟨(List.range length).map fun index =>
      (if enabled then low[index]?.getD 0 - high[index]?.getD 0
        else high[index]?.getD 0 - low[index]?.getD 0) + (offset : Int)⟩

theorem difference_goal : Difference.Goal (ringModel Int Int) reference
    (fun table => Values.curry _ (library.Requires table)) := by
  apply Difference.of_law _ _ _ library rfl
  · intro low high enabled offset
    reference_encoding [library, reference]
  · intro table low high enabled offset premise; exact premise

private def callbackReference (arguments : Values (ringModel Int Int).Value spec.bodyHelper.inputs) : Int :=
  (if arguments.get (.there (.there (.there (.there .here)))) then
      arguments.get .here - arguments.get (.there .here)
    else arguments.get (.there .here) - arguments.get .here) +
    (arguments.get (.there (.there (.there (.there (.there .here))))) : Int)

private def table : Evaluation.MeaningsOn (ringModel Int Int).toCarriers closedInterface :=
  [⟨spec.bodyHelper, fun arguments => .done (.cons (callbackReference arguments) .nil)⟩]

private theorem totalCallback (arguments : Values (ringModel Int Int).Value spec.bodyHelper.inputs) :
    invoke table spec.bodyHelper arguments = .done (.cons (callbackReference arguments) .nil) := by
  rw [table, invoke_cons_same]

example : Difference.run (ringModel Int Int) table [4, 9] [7, 2] true 3 = .done ⟨[0, 10]⟩ := by
  rw [difference_goal table [4, 9] [7, 2] true 3 (by
    constructor
    · rfl
    · intro length shape index bound; exact totalCallback _)]
  rfl

example : Difference.run (ringModel Int Int) table [4, 9] [7, 2] false 3 = .done ⟨[6, -4]⟩ := by
  rw [difference_goal table [4, 9] [7, 2] false 3 (by
    constructor
    · rfl
    · intro length shape index bound; exact totalCallback _)]
  rfl

example : Difference.run (ringModel Int Int) table [4] [] true 3 = .halt .refused := by
  rw [difference_goal table [4] [] true 3 (by
    constructor
    · rfl
    · intro length shape; cases shape)]
  rfl

-- These generated connections need no callback when there are no reached items.
example : Difference.run (ringModel Int Int) [] [] [] true 3 = .done ⟨[]⟩ := by
  rw [difference_goal [] [] [] true 3 (by
    constructor
    · rfl
    · intro length shape index bound
      have empty : 0 = length := PIR.Outcome.returned.inj shape
      subst length
      exact False.elim (Nat.not_lt_zero index bound))]
  rfl

example : Difference.run (ringModel Int Int) [] [4] [] true 3 = .halt .refused := by
  rw [difference_goal [] [4] [] true 3 (by
    constructor
    · rfl
    · intro length shape; cases shape)]
  rfl

example : Difference.run (ringModel Int Int) [] [] [4] true 3 = .halt .refused := by
  rw [difference_goal [] [] [4] true 3 (by
    constructor
    · rfl
    · intro length shape; cases shape)]
  rfl

private def reachedTable : Evaluation.MeaningsOn (ringModel Int Int).toCarriers closedInterface :=
  [⟨spec.bodyHelper, fun arguments =>
    if arguments.get .here = 4 then .done (.cons (callbackReference arguments) .nil)
    else .halt .abort⟩]

-- The callback equation holds only on this admitted nonempty domain.
example : Difference.run (ringModel Int Int) reachedTable [4] [7] true 3 = .done ⟨[0]⟩ := by
  rw [difference_goal reachedTable [4] [7] true 3 (by
    constructor
    · rfl
    · intro length shape index bound
      have singleton : 1 = length := PIR.Outcome.returned.inj shape
      subst length
      have zero : index = 0 := Nat.lt_one_iff.mp bound
      subst index
      rw [reachedTable, invoke_cons_same]
      rfl)]
  rfl

-- A different typed item with the same captures stops, so no total equation was used.
example : invoke reachedTable spec.bodyHelper
    (.cons 9 (.cons 2 (.cons [4] (.cons [7] (.cons true (.cons 3 .nil)))))) =
      .halt .abort := by
  rw [reachedTable, invoke_cons_same]
  rfl

private def wrongLibrary :=
  collection_reference% collectionBody with_model (ringModel Int Int)
    with_shape (fun low high _ _ => Evaluation.mapShape [low.length, high.length])
    with_items (fun low high _ _ index =>
      .cons (low[index]?.getD 0) (.cons (high[index]?.getD 0) .nil))
    with_formula (fun low high _ _ enabled offset =>
      (if enabled then high - low else low - high) + (offset : Int))

-- Swapping a reached formula fails even though its types and shape still agree.
example : ¬ wrongLibrary.Requires reachedTable
    (.cons [4] (.cons [7] (.cons true (.cons 3 .nil)))) := by
  intro premise
  have reached := premise.2 1 rfl 0 (by decide +kernel)
  rw [reachedTable, invoke_cons_same] at reached
  have impossible : (0 : Int) = 6 := congrArg
    (fun values : Values (ringModel Int Int).Value spec.bodyHelper.outputs => values.get .here)
    (PIR.Process.done.inj reached)
  exact (by decide +kernel : (0 : Int) ≠ 6) impossible

#print axioms conditional_forward
#print axioms difference_goal
#print axioms Zkc.Source.Structured.ReferenceLibrary.indexedCollection

end Tests.ReferenceComposition
