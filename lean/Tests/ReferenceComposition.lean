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
  (twoBatches model dependency).valid table arguments available

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
    · intro selected; exact totalCallback _)]
  rfl

example : Difference.run (ringModel Int Int) table [4, 9] [7, 2] false 3 = .done ⟨[6, -4]⟩ := by
  rw [difference_goal table [4, 9] [7, 2] false 3 (by
    constructor
    · rfl
    · intro selected; exact totalCallback _)]
  rfl

example : Difference.run (ringModel Int Int) table [4] [] true 3 = .halt .refused := by
  rw [difference_goal table [4] [] true 3 (by
    constructor
    · rfl
    · intro selected; exact totalCallback _)]
  rfl

#print axioms difference_goal
#print axioms Zkc.Source.Structured.ReferenceLibrary.indexedCollection

end Tests.ReferenceComposition
