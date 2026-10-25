module

public import ZkcSecurity.Families.Sigma.Algebra
public import Zkc.Construction.DomainCalculations

@[expose] public section

/-! Arithmetic realization for the installed module interpretation. Nominal
group and scalar identities remain explicit in every operation and payload. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Families.Sigma.Realization
open Zkc.Source Zkc.Source.Structured Zkc.Construction

variable {K H : Type} [CommRing K] [AddCommGroup H] [Module K H]
  [DecidableEq K] [DecidableEq H]

@[simp] theorem groupScale (group field : String) (point : H) (scalar : K) :
    Domain.calculate (ringModel K H) (.groupScale group field)
      [.data (.group group point), .data (.field field scalar)] =
      .returned [.data (.group group (scalar • point))] := by
  simp only [Domain.calculate, Calculation.op, Op.arguments, Domain.decodeValues,
    Domain.Value.decode, Domain.Payload.value, ↓reduceDIte]
  rfl

@[simp] theorem groupAdd (group : String) (left right : H) :
    Domain.calculate (ringModel K H) (.groupAdd group)
      [.data (.group group left), .data (.group group right)] =
      .returned [.data (.group group (left + right))] := by
  simp only [Domain.calculate, Calculation.op, Op.arguments, Domain.decodeValues,
    Domain.Value.decode, Domain.Payload.value, ↓reduceDIte]
  rfl

@[simp] theorem groupEqual (group : String) (left right : H) :
    Domain.calculate (ringModel K H) (.groupEqual group)
      [.data (.group group left), .data (.group group right)] =
      .returned [.data (.boolean (decide (left = right)))] := by
  simp only [Domain.calculate, Calculation.op, Op.arguments, Domain.decodeValues,
    Domain.Value.decode, Domain.Payload.value, ↓reduceDIte]
  rfl

@[simp] theorem booleanAnd (left right : Bool) :
    Domain.calculate (ringModel K H) .booleanAnd
      [.data (.boolean left), .data (.boolean right)] =
      .returned [.data (.boolean (left && right))] := rfl

end ZkcSecurity.Families.Sigma.Realization
