import Zkc.Source.Structured.BodyBindings
import Zkc.Source.Structured.UnitViews

namespace Tests.StructuredBodyBindings
open Zkc.Source Zkc.Source.Structured

private def constantBody (value : Bool) : Region dialect [] [.boolean] :=
  .letOp (.booleanConstant value) .nil .nil (.ret (.cons .here .nil))

private def helper : Helper := ⟨"value", .math, [], [.boolean]⟩
private def actual : CheckedDefinition := CheckedDefinition.ofBody helper (constantBody true)
private def other : CheckedDefinition :=
  CheckedDefinition.ofBody ⟨"other", .math, [], [.boolean]⟩ (constantBody false)
private def wrongRaw : CheckedDefinition := CheckedDefinition.ofBody helper (constantBody false)
private def wrongKind : CheckedDefinition := { actual with kind := .local }
private def wrongInputs : CheckedDefinition :=
  CheckedDefinition.ofBody ⟨"value", .math, [.boolean], [.boolean]⟩
    (.ret (.cons .here .nil))
private def wrongOutputs : CheckedDefinition :=
  CheckedDefinition.ofBody ⟨"value", .math, [], []⟩ (.ret .nil)

theorem original : BodyIn [actual, other] helper (constantBody true) := by
  bind_structured_bodies

theorem reordered : BodyIn [other, actual] helper (constantBody true) := by
  bind_structured_bodies

/-- Search continues past a same-name/signature definition with a wrong body. -/
theorem full_match : BodyIn [wrongRaw, wrongKind, actual] helper (constantBody true) := by
  bind_structured_bodies

private structure Inner (definitions : List CheckedDefinition) : Prop where
  value : BodyIn definitions helper (constantBody true)

private structure Outer (definitions : List CheckedDefinition) : Prop where
  inner : Inner definitions
  other : BodyIn definitions other.helper (constantBody false)

theorem nested : Outer [other, wrongRaw, actual] := by
  bind_structured_bodies

/-- Template call operands and dependency descriptors are part of the match. -/
private def callBody (calleeName : String) (swap : Bool) :
    Region dialect [.boolean, .boolean] [.boolean] :=
  .letOp (.invoke ⟨calleeName, .math, [.boolean, .boolean], [.boolean]⟩)
    (if swap then .cons (.there .here) (.cons .here .nil)
      else .cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))

private def callee : Helper := ⟨"callee", .math, [.boolean, .boolean], [.boolean]⟩
private def callHelper : Helper := ⟨"caller", .math, [.boolean, .boolean], [.boolean]⟩
private def caller : CheckedDefinition :=
  CheckedDefinition.ofBody callHelper (callBody callee.name false)
private def changedOperands : CheckedDefinition :=
  CheckedDefinition.ofBody callHelper (callBody callee.name true)
private def changedDependency : CheckedDefinition :=
  CheckedDefinition.ofBody callHelper (callBody "different" false)

theorem exact_call : BodyIn [actual, caller] callHelper (callBody callee.name false) := by
  bind_structured_bodies

private structure Empty : Prop
private structure OtherProof : Prop where
  fact : True
private structure Mixed (definitions : List CheckedDefinition) : Prop where
  value : BodyIn definitions helper (constantBody true)
  fact : True

/-- Failure controls exercise the tactic itself, not just hand-proved negations. -/
example : True := by
  fail_if_success
    have : BodyIn [wrongRaw] helper (constantBody true) := by bind_structured_bodies
  fail_if_success
    have : BodyIn [wrongKind] helper (constantBody true) := by bind_structured_bodies
  fail_if_success
    have : BodyIn [wrongInputs] helper (constantBody true) := by bind_structured_bodies
  fail_if_success
    have : BodyIn [wrongOutputs] helper (constantBody true) := by bind_structured_bodies
  fail_if_success
    have : BodyIn [other] helper (constantBody true) := by bind_structured_bodies
  fail_if_success
    have : BodyIn [changedOperands] callHelper (callBody callee.name false) := by
      bind_structured_bodies
  fail_if_success
    have : BodyIn [changedDependency] callHelper (callBody callee.name false) := by
      bind_structured_bodies
  fail_if_success
    have : BodyIn [actual] helper (.stop .abort) := by bind_structured_bodies
  fail_if_success
    have : True := by bind_structured_bodies
  fail_if_success
    have : False := by bind_structured_bodies
  fail_if_success
    have : Empty := by bind_structured_bodies
  fail_if_success
    have : OtherProof := by bind_structured_bodies
  fail_if_success
    have : Mixed [actual] := by bind_structured_bodies
  fail_if_success
    have : Nat := by bind_structured_bodies
  trivial

/-- Matching retains actual stopping behavior rather than inventing a return. -/
private def stopped : CheckedDefinition :=
  CheckedDefinition.ofBody ⟨"stopped", .math, [], []⟩ (.stop .abort)

theorem stopped_body : BodyIn [other, stopped] stopped.helper (.stop .abort) := by
  bind_structured_bodies

end Tests.StructuredBodyBindings
