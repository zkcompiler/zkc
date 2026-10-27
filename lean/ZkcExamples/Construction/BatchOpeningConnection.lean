module

public import ZkcExamples.Construction.BatchOpening
public import Zkc.Source.Structured.Laws
public import Zkc.Construction.DomainExecutionLaws

@[expose] public section

/-! Whole-process equations for the actual batch-opening artifacts. The retained
helper checks repeated point/value equality, not a commitment opening. The source
finite-domain limit is independent of any selected byte codec's smaller limit.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace ZkcExamples.Construction.BatchOpeningConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open BatchOpeningBodies BatchOpening

namespace Associations
structured_associations BatchOpening
  [checkOpening, batchStep, batchValues, formula, realization, checkBatch]
end Associations
open Associations

abbrev Opening (F : Type) := F × (F × Unit)
abbrev Batch (F : Type) := List (Opening F)

def decision {F : Type} [DecidableEq F] (point value : F) (batch : Batch F) : Bool :=
  batch.all fun record => decide (record.1 = point) && decide (record.2.1 = value)

abbrev batchFold : FoldSpec :=
  ⟨DomainSpec.elements ("finite_" ++ batchValuesHelper.name ++ "_s3_domain") [.sequence openingTy]
      (.sequence openingTy) .here,
    [.boolean], [.field "koala-bear", .field "koala-bear"], batchStepHelper.name, "", .math⟩

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev meanings : Meanings F G := closedMeanings unit.definitions
abbrev model := ringModel F G
abbrev carriers := uniformCarriers F G

theorem checkOpening_equation (valid : Bool) (point value expectedPoint expectedValue : F) :
    invoke (meanings (F := F) (G := G)) checkOpeningHelper
      (.cons valid (.cons point (.cons value (.cons expectedPoint (.cons expectedValue .nil))))) =
      .done (.cons (valid && decide (point = expectedPoint) && decide (value = expectedValue)) .nil) := by
  rw [checkOpening_association.invoke unit.linked]
  rfl

theorem batchStep_equation (batch : Batch F) (valid : Bool) (record : Opening F)
    (point value : F) :
    invoke (meanings (F := F) (G := G)) batchStepHelper
      (.cons valid (.cons record (.cons batch (.cons point (.cons value .nil))))) =
      .done (.cons (valid && decide (record.1 = point) && decide (record.2.1 = value)) .nil) := by
  rw [batchStep_association.invoke unit.linked]
  change (invoke (meanings (F := F) (G := G)) checkOpeningHelper
    (.cons valid (.cons record.1 (.cons record.2.1 (.cons point (.cons value .nil)))))).bind _ = _
  rw [checkOpening_equation]
  rfl

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem batch_fold (batch : Batch F) (point value : F) (valid : Bool) :
    batch.foldl (fun (state : Values (assignment F G) [.boolean]) record =>
      Values.cons (state.get .here && decide (record.1 = point) && decide (record.2.1 = value)) .nil)
      (.cons valid .nil) = .cons (valid && decision point value batch) .nil := by
  induction batch generalizing valid with
  | nil => simp [decision]
  | cons record rest ih =>
      rw [List.foldl_cons, ih]
      simp only [decision, List.all_cons]
      congr 1
      simp only [Values.get, Bool.and_assoc]

theorem batchValues_bounded (point value : F) (batch : Batch F)
    (bounded : batch.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) batchValuesHelper (.cons point (.cons value (.cons batch .nil))) =
      .done (.cons (decision point value batch) .nil) := by
  rw [batchValues_association.invoke unit.linked]
  change (Evaluation.denoteFold (meanings (F := F) (G := G)) batchFold
    ((Values.cons batch Values.nil).append
      ((Values.cons true Values.nil).append (.cons point (.cons value .nil))))).bind _ = _
  have admitted : batchFold.domain.admit (carriers := uniformCarriers F G) (Values.cons batch
      (Values.nil : Values (assignment F G) [])) =
      .returned (batch.map fun item => .cons item .nil) := by
    simp [batchFold, DomainSpec.admit_elements, Collection.values, Values.get, bounded]
  have folded := Evaluation.denoteFold_reference_map meanings batchFold
    (.cons batch .nil) (.cons true .nil) (.cons point (.cons value .nil)) batch
    (fun item => .cons item .nil) admitted
    (fun (state : Values (assignment F G) [.boolean]) record =>
      Values.cons (state.get .here && decide (record.1 = point) && decide (record.2.1 = value)) .nil)
    (fun _ => True) trivial (by
      intro state record _ _
      cases state with | cons valid rest => ?_
      cases rest
      constructor
      · exact (Evaluation.foldTransition_unfiltered _ batchFold rfl _ _ _ _).trans
          (batchStep_equation batch valid record point value)
      · trivial)
  erw [folded, batch_fold (G := G) batch point value true]
  rfl

theorem batchValues_exhausted (point value : F) (batch : Batch F)
    (unbounded : ¬batch.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) batchValuesHelper (.cons point (.cons value (.cons batch .nil))) =
      .halt .exhausted := by
  rw [batchValues_association.invoke unit.linked]
  change (Finite.admitThen (batchFold.domain.admit (carriers := uniformCarriers F G)
    (Values.cons batch (.nil : Values (assignment F G) []))) _).bind _ = _
  simp [batchFold, DomainSpec.admit_elements, Collection.values, Values.get,
    unbounded, Finite.admitThen, PIR.Process.bind]

/-- One all-answer equation, with the real finite-fold exhaustion branch. -/
theorem check_equation (point value : F) (batch : Batch F) :
    invoke (meanings (F := F) (G := G)) checkBatchHelper (.cons point (.cons value (.cons batch .nil))) =
      if batch.length < indexLimit then .done (.cons (decision point value batch) .nil)
      else .halt .exhausted := by
  rw [checkBatch_association.invoke unit.linked]
  change (invoke (meanings (F := F) (G := G)) realizationHelper
    (.cons point (.cons value (.cons batch .nil)))).bind _ = _
  rw [realization_association.invoke unit.linked]
  change ((invoke (meanings (F := F) (G := G)) batchValuesHelper
    (.cons point (.cons value (.cons batch .nil)))).bind _).bind _ = _
  by_cases bounded : batch.length < indexLimit
  · rw [ite_eq_left bounded, batchValues_bounded point value batch bounded]
    rfl
  · rw [ite_eq_right bounded, batchValues_exhausted point value batch bounded]
    rfl

def inputs (point value : F) : Domain.Environment (carriers (F := F) (G := G)) :=
  [.data (.field "koala-bear" point), .data (.field "koala-bear" value)]

def received (point value : F) (batch : Batch F) : Domain.Environment (carriers (F := F) (G := G)) :=
  inputs point value ++ [.data (payload model batch)]

def result (point value : F) (batch : Batch F) : Domain.Result (carriers (F := F) (G := G)) :=
  ⟨[.data (.boolean (decision point value batch)), .data (payload model batch)],
    received point value batch ++ [.data (.boolean (decision point value batch))]⟩

theorem helper_equation (point value : F) (batch : Batch F) :
    Domain.callHelper (model (F := F) (G := G)) program checkBatchHelper.name [.data .boolean]
      (received point value batch) =
      if batch.length < indexLimit then .returned [.data (.boolean (decision point value batch))]
      else .stopped .exhausted := by
  have invoked : invoke (Domain.helperTable (model (F := F) (G := G)) program) checkBatchHelper
      (.cons point (.cons value (.cons batch .nil))) =
      if batch.length < indexLimit then .done (.cons (decision point value batch) .nil)
      else .halt .exhausted := by
    rw [Domain.Binding.helperTable_ringModel]
    exact check_equation point value batch
  have law := Domain.Binding.callHelper_of_invoke_not_refused (model (F := F) (G := G)) program
    checkBatchHelper (.cons point (.cons value (.cons batch .nil))) _ invoked
    (by split <;> intro impossible <;> cases impossible) (received point value batch) (by kernel_rfl)
  change Domain.callHelper _ _ _ [.data .boolean] _ = _ at law
  by_cases bounded : batch.length < indexLimit
  · rw [ite_eq_left bounded] at law ⊢
    exact law
  · rw [ite_eq_right bounded] at law ⊢
    exact law

/-- The actual whole validator, including the physical checkpoints before
receive, after receive, before helper, and after a successful helper. Replies
are arbitrary typed batches; neither validity nor a codec bound is assumed. -/
theorem validator_equation (point value : F) :
    Domain.participant (model (F := F) (G := G)) program context validator (inputs point value) =
      .call (.checkpoint (inputs point value)) (fun _ =>
        .call (.checkpoint (inputs point value)) (fun _ =>
          .call (.receive batchTy "label_6261746368_0" "label_6261746368_0" "role00000000") (fun batch =>
            .call (.checkpoint (received point value batch)) (fun _ =>
              .call (.checkpoint (received point value batch)) (fun _ =>
                if batch.length < indexLimit then
                  .call (.checkpoint (result point value batch).environment) (fun _ =>
                    .done (result point value batch))
                else .halt .exhausted))))) := by
  rw [validator_binding]
  unfold validatorView Domain.View.participant
  have shape : Domain.sortsMatch validator.inputs (inputs (G := G) point value) = true := by kernel_rfl
  simp only [shape, ↓reduceIte, Domain.View.sequence]
  rw [receive_reply (model (F := F) (G := G)) (inputs point value)]
  simp only [PIR.Process.bind]
  congr 1
  funext _
  congr 1
  funext _
  congr 1
  funext batch
  change Batch F at batch
  have head : Domain.View.helper (model (F := F) (G := G)) program checkBatchHelper.name
      [0, 1, 2] [.data .boolean] (received point value batch) =
      if batch.length < indexLimit then .done (result point value batch).environment
      else .halt .exhausted := by
    have read : Domain.read (received (G := G) point value batch) [0, 1, 2] =
        some (received point value batch) := by kernel_rfl
    have law := helper_equation (G := G) point value batch
    by_cases bounded : batch.length < indexLimit
    · rw [ite_eq_left bounded] at law ⊢
      rw [Domain.View.helper_eq _ _ _ _ _ _ _ _ read law]
      exact Domain.View.append_eq _ _ _ (by kernel_rfl)
    · rw [ite_eq_right bounded] at law ⊢
      exact Domain.View.helper_stop _ _ _ _ _ _ _ _ read law
  congr 1
  funext _
  congr 1
  funext _
  erw [head]
  split <;> kernel_rfl

end ZkcExamples.Construction.BatchOpeningConnection
