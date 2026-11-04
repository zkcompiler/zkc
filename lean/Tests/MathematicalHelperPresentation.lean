import ZkcTools.StructuredSource.HelperPresentation
import Zkc.Source.Structured.DomainModels

/-! Input-dependent restoration retains the complete return and every stop. -/
set_option autoImplicit false
noncomputable section
namespace Tests.MathematicalHelperPresentation
open Zkc.Source Zkc.Source.Structured

private def body : Region dialect [.field scalarDomain, .field scalarDomain]
    [.field scalarDomain, .field scalarDomain] :=
  .ret (.cons .here (.cons (.there .here) .nil))

helper_presentation Pair inputs [left, right] outputs [first, second] := body

def difference (model : DomainModel) (_left _right : model.Field scalarDomain)
    (result : Pair.Output model) : model.Field scalarDomain := result.first - result.second

def restore (model : DomainModel) (_left right : model.Field scalarDomain)
    (value : model.Field scalarDomain) : Pair.Output model := ⟨value + right, right⟩

def reference (model : DomainModel) (left right : model.Field scalarDomain) :
    PIR.Outcome (model.Field scalarDomain) := .returned (left - right)

theorem reachable (model : DomainModel) (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (left right : model.Field scalarDomain) (_ : True) :
    PIR.Yields (fun result => restore model left right (difference model left right result) = result)
      (Pair.run model table left right) := by
  change restore model left right (difference model left right ⟨left, right⟩) = ⟨left, right⟩
  simp only [restore, difference]
  congr 1
  exact sub_add_cancel left right

theorem projected (model : DomainModel) (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (left right : model.Field scalarDomain) (_ : True) :
    (Pair.run model table left right).bind (fun result => .done (difference model left right result)) =
      primitiveOutcome (reference model left right) := rfl

def mathematicalLaw (model : DomainModel) :=
  Pair.lawOfView model (difference model) (restore model) (reference model)
    (fun _ _ _ => True) (reachable model) (projected model)

example (model : DomainModel) (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (left right : model.Field scalarDomain) :
    body.denote (Evaluation.meaningOn model SiteObservations.closed table)
        (show Values model.Value [.field scalarDomain, .field scalarDomain] from
          .cons left (.cons right .nil)).get =
      primitiveOutcome ((mathematicalLaw model).reference (.cons left (.cons right .nil))) :=
  (mathematicalLaw model).valid table (.cons left (.cons right .nil)) trivial

/-- Reachability-specific packing need not invert an unreachable return. -/
example : restore (ringModel Int Int) 1 2 (difference (ringModel Int Int) 1 2 ⟨1, 3⟩) ≠
    (⟨1, 3⟩ : Pair.Output (ringModel Int Int)) := by
  intro same
  have impossible := congrArg Pair.Output.second same
  change (2 : Int) = 3 at impossible
  contradiction

private def stoppedBody : Region dialect [] [] := .stop .abort
helper_presentation Stopped inputs [] outputs [] := stoppedBody

def stoppedLaw (model : DomainModel) :=
  Stopped.lawOfView model (fun _ => ()) (fun _ => ⟨⟩)
    (.stopped .abort : PIR.Outcome Unit) (fun _ => True)
    (by intro table _; trivial)
    (by intro table _; rfl)

example (model : DomainModel) : (stoppedLaw model).reference .nil = .stopped .abort := rfl

end Tests.MathematicalHelperPresentation
