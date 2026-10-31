module

public import ZkcExamples.Construction.BatchOpening
public import ZkcExamples.Structured.BatchOpeningConnection
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

open Zkc.Protocols.TableMembership

abbrev Batch (F : Type) := BatchSource.Batch F

def decision {F : Type} [DecidableEq F] (point value : F) (batch : Batch F) : Bool :=
  batch.all fun record => decide (record.1 = point) && decide (record.2.1 = value)

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev model := ringModel F G
abbrev carriers := uniformCarriers F G

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
    exact BatchSource.check_equation unit.linked
      ZkcExamples.Structured.BatchOpeningConnection.installedBodies point value batch
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
