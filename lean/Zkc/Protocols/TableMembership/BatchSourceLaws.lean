module

public import Zkc.Protocols.TableMembership.ReferenceBodies
public import Zkc.Source.Structured.Laws
public import Zkc.Source.Structured.ReferenceLibrary

@[expose] public section

/-! Reusable complete outcome laws for a finite batch of point/value records.
The reached finite-domain bound is independent of byte codec limits. -/
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Protocols.TableMembership.BatchSource
open Zkc.Source Zkc.Source.Structured

structure Bodies (definitions : List CheckedDefinition) (field : String) (bindings : Names) : Prop where
  checkOpening : BodyIn definitions (checkOpeningHelper field bindings) (checkOpeningBody field bindings)
  batchStep : BodyIn definitions (batchStepHelper field bindings) (batchStepBody field bindings)
  batchValues : BodyIn definitions (batchValuesHelper field bindings) (batchValuesBody field bindings)
  formula : BodyIn definitions (formulaHelper field bindings) (formulaBody field bindings)
  mathematicalAdmission : BodyIn definitions (mathematicalAdmissionHelper field bindings) (mathematicalAdmissionBody field bindings)
  checkBatch : BodyIn definitions (checkBatchHelper field bindings) (checkBatchBody field bindings)

variable {field : String} {bindings : Names} {definitions : List CheckedDefinition}

abbrev openingTy (field : String) (bindings : Names) : Ty :=
  (batchStepHelper field bindings).inputs[1]

abbrev Opening (F : Type) := F × (F × Unit)
abbrev Batch (F : Type) := List (Opening F)

def decision {F : Type} [DecidableEq F] (point value : F) (batch : Batch F) : Bool :=
  batch.all fun record => decide (record.1 = point) && decide (record.2.1 = value)

abbrev batchFold (field : String) (bindings : Names) : FoldSpec :=
  ⟨DomainSpec.elements bindings.batchDomain [.sequence (openingTy field bindings)]
      (.sequence (openingTy field bindings)) .here,
    [.boolean], [.field field, .field field], (batchStepHelper field bindings).name, "", .math⟩

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev meanings (definitions : List CheckedDefinition) : Meanings F G := closedMeanings definitions
abbrev model := ringModel F G
abbrev carriers := uniformCarriers F G

theorem checkOpening_equation (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (valid : Bool) (point value expectedPoint expectedValue : F) :
    invoke (meanings (F := F) (G := G) definitions) (checkOpeningHelper field bindings)
      (.cons valid (.cons point (.cons value (.cons expectedPoint (.cons expectedValue .nil))))) =
      .done (.cons (valid && decide (point = expectedPoint) && decide (value = expectedValue)) .nil) := by
  rw [bodies.checkOpening.invoke linked, Evaluation.denote_meaning_eq_meaningOn]
  exact (checkOpeningLaw (ringModel F G) field bindings).valid _ _ trivial

theorem batchStep_equation (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (batch : Batch F) (valid : Bool) (record : Opening F)
    (point value : F) :
    invoke (meanings (F := F) (G := G) definitions) (batchStepHelper field bindings)
      (.cons valid (.cons record (.cons batch (.cons point (.cons value .nil))))) =
      .done (.cons (valid && decide (record.1 = point) && decide (record.2.1 = value)) .nil) := by
  rw [bodies.batchStep.invoke linked]
  change (invoke (meanings (F := F) (G := G) definitions) (checkOpeningHelper field bindings)
    (.cons valid (.cons record.1 (.cons record.2.1 (.cons point (.cons value .nil)))))).bind _ = _
  rw [(checkOpening_equation linked bodies)]
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

theorem batchValues_bounded (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (point value : F) (batch : Batch F)
    (bounded : batch.length < indexLimit) :
    invoke (meanings (F := F) (G := G) definitions) (batchValuesHelper field bindings) (.cons point (.cons value (.cons batch .nil))) =
      .done (.cons (decision point value batch) .nil) := by
  rw [bodies.batchValues.invoke linked]
  change (Evaluation.denoteFold (meanings (F := F) (G := G) definitions) (batchFold field bindings)
    ((Values.cons batch Values.nil).append
      ((Values.cons true Values.nil).append (.cons point (.cons value .nil))))).bind _ = _
  have admitted : (batchFold field bindings).domain.admit (carriers := uniformCarriers F G) (Values.cons batch
      (Values.nil : Values (assignment F G) [])) =
      .returned (batch.map fun record => .cons record .nil) := by
    rw [DomainSpec.admit_elements]
    exact ite_eq_left bounded
  have folded := Evaluation.denoteFold_reference_map (meanings definitions) (batchFold field bindings)
    (.cons batch .nil) (.cons true .nil) (.cons point (.cons value .nil)) batch
    (fun record => .cons record .nil) admitted
    (fun (state : Values (assignment F G) [.boolean]) record =>
      Values.cons (state.get .here && decide (record.1 = point) && decide (record.2.1 = value)) .nil)
    (fun _ => True) trivial (by
      intro state record _ _
      cases state with | cons valid rest => ?_
      cases rest
      constructor
      · exact (Evaluation.foldTransition_unfiltered _ (batchFold field bindings) rfl _ _ _ _).trans
          ((batchStep_equation linked bodies) batch valid record point value)
      · trivial)
  erw [folded, batch_fold (G := G) batch point value true]
  rfl

theorem batchValues_exhausted (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (point value : F) (batch : Batch F)
    (unbounded : ¬batch.length < indexLimit) :
    invoke (meanings (F := F) (G := G) definitions) (batchValuesHelper field bindings) (.cons point (.cons value (.cons batch .nil))) =
      .halt .exhausted := by
  rw [bodies.batchValues.invoke linked]
  change (Evaluation.denoteFold (meanings (F := F) (G := G) definitions) (batchFold field bindings)
    ((Values.cons batch Values.nil).append
      ((Values.cons true Values.nil).append (.cons point (.cons value .nil))))).bind _ = _
  rw [Evaluation.denoteFold_pack]
  have exhausted : (batchFold field bindings).domain.admit (carriers := uniformCarriers F G) (Values.cons batch
      (Values.nil : Values (assignment F G) [])) = .stopped .exhausted := by
    rw [DomainSpec.admit_elements]
    exact ite_eq_right unbounded
  rw [exhausted]
  rfl

/-- One all-answer equation, with the real finite-fold exhaustion branch. -/
theorem check_equation (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (point value : F) (batch : Batch F) :
    invoke (meanings (F := F) (G := G) definitions) (checkBatchHelper field bindings) (.cons point (.cons value (.cons batch .nil))) =
      if batch.length < indexLimit then .done (.cons (decision point value batch) .nil)
      else .halt .exhausted := by
  rw [bodies.checkBatch.invoke linked]
  change (invoke (meanings (F := F) (G := G) definitions) (mathematicalAdmissionHelper field bindings)
    (.cons point (.cons value (.cons batch .nil)))).bind _ = _
  rw [bodies.mathematicalAdmission.invoke linked]
  change ((invoke (meanings (F := F) (G := G) definitions) (batchValuesHelper field bindings)
    (.cons point (.cons value (.cons batch .nil)))).bind _).bind _ = _
  by_cases bounded : batch.length < indexLimit
  · rw [ite_eq_left bounded, (batchValues_bounded linked bodies) point value batch bounded]
    rfl
  · rw [ite_eq_right bounded, (batchValues_exhausted linked bodies) point value batch bounded]
    rfl


end Zkc.Protocols.TableMembership.BatchSource
