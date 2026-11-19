module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Field.Basic
public import Zkc.Formal.Written.StandardModel

@[expose] public section
namespace Zkc.Formal.Written.ArithmeticModel
open Core

variable (F G : Type) [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Mathlib's field and scalar action supply the algebraic interface of the written proofs. -/
def operations : Operations F G :=
  ⟨0, (· - ·), (· * ·), (·⁻¹), (· + ·), fun p k ↦ k • p⟩

def actionLaws : ActionLaws (operations F G) where
  one := 1
  difference := (· - ·)
  sub_zero := fun _ _ ↦ sub_eq_zero
  cancel_left := fun a x y ↦ add_sub_add_left_eq_sub x y a
  scale_sub := fun p x y ↦ (sub_smul x y p).symm
  scale_mul := by intro p x y; change y • x • p = (x * y) • p; rw [smul_smul, mul_comm]
  scale_one := one_smul F
  mul_inv := fun _ h ↦ mul_inv_cancel₀ h

def data : StandardModel.Data F G where
  toOperations := operations F G
  scalarAdd := (· + ·)
  zeroPoint := 0
  unit := ⟨1, one_ne_zero⟩
  literal n := n
  literalZero := Nat.cast_zero
  invNonzero := fun _ h ↦ inv_ne_zero h

abbrev model := StandardModel.model (data F G)
abbrev groupRows := StandardModel.groupRows (data F G)
abbrev functionRows := StandardModel.functionRows (data F G)
abbrev unpack_ne_zero := StandardModel.unpack_ne_zero (data F G)

end Zkc.Formal.Written.ArithmeticModel
