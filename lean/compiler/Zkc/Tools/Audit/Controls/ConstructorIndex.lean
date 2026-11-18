module

/-! Counterfeit constructor indices. The parent datatype and helper names are real, but one
of the logical body, native body, or replacement target differs from Lean's generated form. -/

@[expose] public section
namespace Zkc.Tools.Audit.Controls

set_option genCtorIdx false in
inductive WrongLogic where
  | left | right

unsafe def WrongLogic.ctorIdx._impl (x : WrongLogic) : Nat := getObjTagNat x
@[implemented_by WrongLogic.ctorIdx._impl]
def WrongLogic.ctorIdx (_x : WrongLogic) : Nat := 0

set_option genCtorIdx false in
inductive WrongNative where
  | left | right

unsafe def WrongNative.ctorIdx._impl (_x : WrongNative) : Nat := 0
@[implemented_by WrongNative.ctorIdx._impl]
def WrongNative.ctorIdx (x : WrongNative) : Nat :=
  WrongNative.casesOn (motive := fun _ => Nat) x 0 1

set_option genCtorIdx false in
inductive WrongTarget where
  | left | right

unsafe def WrongTarget.replacement (x : WrongTarget) : Nat := getObjTagNat x
@[implemented_by WrongTarget.replacement]
def WrongTarget.ctorIdx (x : WrongTarget) : Nat :=
  WrongTarget.casesOn (motive := fun _ => Nat) x 0 1

end Zkc.Tools.Audit.Controls
