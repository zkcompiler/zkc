module

public import ZkcArkLibExamples.Fri.CommitGeometry
public import Zkc.Source.DenotationLaws

@[expose] public section

/-! Commit admits the shifted coset before beginning its publication
loop. The checked helper evaluates its first point, guards nonzero,
and returns the shift and row count from that same invocation. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.CommitDomain
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open FriSource (extension)
open FriSourceBodies FriSourceViews
attribute [local implicit_reducible] Op.arguments Op.results Op.regions

private theorem geometryBody (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (shift : Octic) (nz : shift ≠ 0)
    (point : (Primitive.numerical .polyPoint extension "").evaluateOn model.toFieldModel
      (.cons shift (.cons 32 (.cons 0 .nil))) = .returned (.cons shift .nil)) :
    helper1Body.ReturnsValues (Evaluation.meaningOn model SiteObservations.closed table)
      (.cons shift (.cons 32 .nil)) (.cons shift (.cons 32 .nil)) := by
  have read := congrArg (@primitiveOutcome closedInterface _) point
  have compare : decide (shift = (0 : Octic)) = false := decide_eq_false nz
  refine Region.ReturnsValues.letOp .nil rfl ?_
  refine Region.ReturnsValues.letOp (.cons 0 .nil) rfl ?_
  refine Region.ReturnsValues.letOp .nil rfl ?_
  refine Region.ReturnsValues.letOp (.cons shift .nil) ?_ ?_
  · change primitiveOutcome ((Primitive.numerical .polyPoint extension "").evaluateOn model.toFieldModel
      (.cons shift (.cons 32 (.cons 0 .nil)))) = _
    exact read
  refine Region.ReturnsValues.letOp .nil rfl ?_
  refine Region.ReturnsValues.letOp (.cons (Nat.cast 0 : Octic) .nil) rfl ?_
  refine Region.ReturnsValues.letOp .nil rfl ?_
  refine Region.ReturnsValues.letOp (.cons false .nil) ?_ ?_
  · change PIR.Process.done (I := closedInterface) (Values.cons (Value := model.Value) (ty := .boolean)
      (decide (shift = (Nat.cast 0 : Octic))) .nil) = _
    rw [Nat.cast_zero, compare]
    rfl
  repeat' first
    | apply Region.ReturnsValues.letOp .nil rfl
    | apply Region.ReturnsValues.letOp (.cons false .nil) rfl
    | apply Region.ReturnsValues.letOp (.cons true .nil) rfl
  rfl

/-- The checked coset helper called by the receiver at its actual input
geometry. An arbitrary nonzero shift is allowed. -/
theorem installed {I : PIR.Signature} (shift : Octic) (nz : shift ≠ 0) :
    invoke (RetainedFold.helpers (I := I)).closed helper1Helper (.cons shift (.cons 32 .nil)) =
      .done (.cons shift (.cons 32 .nil)) := by
  have point := RetainedDomain.pointValue model extension shift (RetainedDomain.root 5) nz 32 0
    (by decide) (by decide) (RetainedDomain.domainRoot 5 (by decide))
  have atZero : shift * RetainedDomain.root 5 ^ 0 = shift := by simp
  have first := point.trans (congrArg (fun x : Octic ↦ PIR.Outcome.returned
    (Values.cons (Value := model.Value) (ty := .field extension) x .nil)) atZero)
  have association : BodyIn unit.definitions helper1Helper helper1Body := by exact_body helper1Definition
  obtain ⟨definition, member, sig, raw⟩ := association
  rw [Evaluation.closed_invoke_componentTablesOn, Evaluation.definitions_invoke_body_view_asOn model
    SiteObservations.closed unit.definitions unit.linked definition member helper1Helper sig helper1Body raw]
  rw [show helper1Body.denote (meaningOn model (closedMeaningsOn model unit.definitions))
        (Values.cons (Value := model.Value) (ty := .field extension) shift (.cons (ty := .index) 32 .nil)).get =
        .done (.cons shift (.cons 32 .nil)) from geometryBody _ shift nz first]
  rfl

end ZkcSecurity.ArkLib.Fri.CommitDomain
