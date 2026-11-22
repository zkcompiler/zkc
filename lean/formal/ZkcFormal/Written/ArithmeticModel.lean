module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Field.Basic
public import ZkcFormal.Written.StandardModel
public import ZkcFormal.WalkLabels

@[expose] public section
namespace ZkcFormal.Written.ArithmeticModel
open Zkc.Core

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

end ZkcFormal.Written.ArithmeticModel

namespace ZkcFormal.Written.ArithmeticModel

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-! What the operations of the model are in the field and in the module: each holds by
definition. A walk reads them where it stops (`walk_value`), so that what a text has left to
prove is stated with the operations of the field. -/

@[walk_value] theorem data_zero : (data F G).zero = 0 := rfl
@[walk_value] theorem data_scalarAdd (x y : F) : (data F G).scalarAdd x y = x + y := rfl
@[walk_value] theorem data_sub (x y : F) : (data F G).sub x y = x - y := rfl
@[walk_value] theorem data_mul (x y : F) : (data F G).mul x y = x * y := rfl
@[walk_value] theorem data_inv (x : F) : (data F G).inv x = x⁻¹ := rfl
@[walk_value] theorem data_add (p q : G) : (data F G).add p q = p + q := rfl
@[walk_value] theorem data_scale (p : G) (k : F) : (data F G).scale p k = k • p := rfl
@[walk_value] theorem data_zeroPoint : (data F G).zeroPoint = 0 := rfl
@[walk_value] theorem data_literal (n : ℕ) : (data F G).literal n = n := rfl

/-- The sum of a sequence in the model is its sum in the field. -/
@[walk_value] theorem data_sum (xs : List F) :
    List.foldr (data F G).scalarAdd (data F G).zero xs = xs.sum := rfl

/-- The same, where the zero of the model is already read as the zero of the field. -/
@[walk_value] theorem data_sum_zero (xs : List F) :
    List.foldr (data F G).scalarAdd 0 xs = xs.sum := rfl

/-- A literal of the scalar type is its number in the field. -/
theorem readLiteral_scalar [DecidableEq F] [DecidableEq G] (n : ℕ) (reads) :
    Zkc.Core.Ty.readLiteral (model F G)
        (.nominal (.inl (Zkc.Vocabulary.TypeKey.field Zkc.Vocabulary.Field.bls12381Fr))) [n] reads =
      (n : F) := by
  have read := Zkc.Core.Ty.read_readLiteral (model F G)
    (.nominal (.inl (Zkc.Vocabulary.TypeKey.field Zkc.Vocabulary.Field.bls12381Fr))) [n] reads
  unfold Zkc.Core.Ty.read at read
  split at read
  · next readable =>
      have literal : (model F G).literal
          (.inl (Zkc.Vocabulary.TypeKey.field Zkc.Vocabulary.Field.bls12381Fr)) n = some (n : F) :=
        ite_eq_left readable
      rw [literal] at read
      exact (Prod.mk.inj (Option.some.inj read)).1.symm
  · cases read

/-! How a literal reads: zero and one as the field's, any other as its numeral. The three are
of patterns that do not overlap, and no lemma about numbers at large has the label, so that
reading the values of a goal leaves a text's own hypotheses about numbers as they were. -/

@[walk_value] theorem readLiteral_scalar_zero [DecidableEq F] [DecidableEq G] (reads) :
    Zkc.Core.Ty.readLiteral (model F G)
        (.nominal (.inl (Zkc.Vocabulary.TypeKey.field Zkc.Vocabulary.Field.bls12381Fr))) [0] reads =
      (0 : F) :=
  (readLiteral_scalar 0 reads).trans (Nat.cast_zero (R := F))

@[walk_value] theorem readLiteral_scalar_one [DecidableEq F] [DecidableEq G] (reads) :
    Zkc.Core.Ty.readLiteral (model F G)
        (.nominal (.inl (Zkc.Vocabulary.TypeKey.field Zkc.Vocabulary.Field.bls12381Fr))) [1] reads =
      (1 : F) :=
  (readLiteral_scalar 1 reads).trans (Nat.cast_one (R := F))

@[walk_value] theorem readLiteral_scalar_numeral [DecidableEq F] [DecidableEq G] (n : ℕ) (reads) :
    Zkc.Core.Ty.readLiteral (model F G)
        (.nominal (.inl (Zkc.Vocabulary.TypeKey.field Zkc.Vocabulary.Field.bls12381Fr))) [n + 2]
        reads = ((n + 2 : ℕ) : F) :=
  readLiteral_scalar (n + 2) reads

end ZkcFormal.Written.ArithmeticModel
