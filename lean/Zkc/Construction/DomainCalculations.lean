module

public import Zkc.Construction.DomainView

@[expose] public section

/-! Reusable nominal scalar/Boolean equations for actual constructed arithmetic.
Index constants in the constructed protocol language retain their own semantics;
bounded primitive index arithmetic remains separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Construction.Domain.Calculations
open Zkc.Source Zkc.Source.Structured Zkc.Construction

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

@[simp] theorem fieldAdd (field : String) (left right : F) :
    Domain.calculate (ringModel F G) (.fieldAdd field)
      [.data (.field field left), .data (.field field right)] =
      .returned [.data (.field field (left + right))] := by
  simp only [Domain.calculate, Calculation.op, Op.arguments, Domain.decodeValues,
    Domain.Value.decode, Domain.Payload.value, ↓reduceDIte]
  rfl

@[simp] theorem fieldSubtract (field : String) (left right : F) :
    Domain.calculate (ringModel F G) (.fieldSubtract field)
      [.data (.field field left), .data (.field field right)] =
      .returned [.data (.field field (left - right))] := by
  simp only [Domain.calculate, Calculation.op, Op.arguments, Domain.decodeValues,
    Domain.Value.decode, Domain.Payload.value, ↓reduceDIte]
  rfl

@[simp] theorem fieldMultiply (field : String) (left right : F) :
    Domain.calculate (ringModel F G) (.fieldMultiply field)
      [.data (.field field left), .data (.field field right)] =
      .returned [.data (.field field (left * right))] := by
  simp only [Domain.calculate, Calculation.op, Op.arguments, Domain.decodeValues,
    Domain.Value.decode, Domain.Payload.value, ↓reduceDIte]
  rfl

@[simp] theorem fieldEqual (field : String) (left right : F) :
    Domain.calculate (ringModel F G) (.fieldEqual field)
      [.data (.field field left), .data (.field field right)] =
      .returned [.data (.boolean (decide (left = right)))] := by
  simp only [Domain.calculate, Calculation.op, Op.arguments, Domain.decodeValues,
    Domain.Value.decode, Domain.Payload.value, ↓reduceDIte]
  rfl

@[simp] theorem fieldConstant (field : String) (value : Nat) :
    Domain.calculate (ringModel F G) (.fieldConstant field value) [] =
      .returned [.data (.field field (value : F))] := rfl

@[simp] theorem indexConstant (value : Nat) :
    Domain.calculate (ringModel F G) (.indexConstant value) [] =
      .returned [.data (.index value)] := rfl

@[simp] theorem indexEqual (left right : Nat) :
    Domain.calculate (ringModel F G) .indexEqual [.data (.index left), .data (.index right)] =
      .returned [.data (.boolean (decide (left = right)))] := rfl

@[simp] theorem booleanConstant (value : Bool) :
    Domain.calculate (ringModel F G) (.booleanConstant value) [] =
      .returned [.data (.boolean value)] := rfl

@[simp] theorem booleanEqual (left right : Bool) :
    Domain.calculate (ringModel F G) .booleanEqual
      [.data (.boolean left), .data (.boolean right)] =
      .returned [.data (.boolean (left == right))] := rfl

end Zkc.Construction.Domain.Calculations
