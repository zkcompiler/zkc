module

public import Zkc.Source.Structured.Component

@[expose] public section

/-! General logical primitive equations. Range premises denote u64, never field
reduction or wrapping. Native allocation and observer capacity remain separate. -/

namespace Zkc.Source.Structured
namespace Primitive
variable {F G : Type} [CommRing F] [DecidableEq F]

@[simp] theorem constant (n : Nat) (bound : n < indexLimit) :
    evaluate (F := F) (G := G) (.indexConstant n) .nil = .returned (.cons n .nil) := by
  simp [evaluate, bound]

@[simp] theorem index_equal (a b : Nat) (ha : a < indexLimit) (hb : b < indexLimit)
     :
    evaluate (F := F) (G := G) .indexEqual (.cons a (.cons b .nil)) =
      .returned (.cons (decide (a = b)) .nil) := by
  simp [evaluate, checkedIndices, ha, hb]

@[simp] theorem index_less (a b : Nat) (ha : a < indexLimit) (hb : b < indexLimit)
     :
    evaluate (F := F) (G := G) .indexLess (.cons a (.cons b .nil)) =
      .returned (.cons (decide (a < b)) .nil) := by
  simp [evaluate, checkedIndices, ha, hb]

@[simp] theorem index_add (a b : Nat) (ha : a < indexLimit) (hb : b < indexLimit)
    (bound : a + b < indexLimit) :
    evaluate (F := F) (G := G) .indexAdd (.cons a (.cons b .nil)) =
      .returned (.cons (a + b) .nil) := by
  simp [evaluate, checkedIndices, ha, hb, bound]

@[simp] theorem index_mul (a b : Nat) (ha : a < indexLimit) (hb : b < indexLimit)
    (bound : a * b < indexLimit) :
    evaluate (F := F) (G := G) .indexMul (.cons a (.cons b .nil)) =
      .returned (.cons (a * b) .nil) := by
  simp [evaluate, checkedIndices, ha, hb, bound]

@[simp] theorem index_sub (a b : Nat) (ha : a < indexLimit) (hb : b < indexLimit)
    (order : b ≤ a) :
    evaluate (F := F) (G := G) .indexSub (.cons a (.cons b .nil)) =
      .returned (.cons (a - b) .nil) := by
  simp [evaluate, checkedIndices, ha, hb, order]

@[simp] theorem index_div (a b : Nat) (ha : a < indexLimit) (hb : b < indexLimit)
    (nonzero : b ≠ 0) :
    evaluate (F := F) (G := G) .indexDiv (.cons a (.cons b .nil)) =
      .returned (.cons (a / b) .nil) := by
  simp [evaluate, checkedIndices, ha, hb, nonzero]

@[simp] theorem index_mod (a b : Nat) (ha : a < indexLimit) (hb : b < indexLimit)
    (nonzero : b ≠ 0) :
    evaluate (F := F) (G := G) .indexMod (.cons a (.cons b .nil)) =
      .returned (.cons (a % b) .nil) := by
  simp [evaluate, checkedIndices, ha, hb, nonzero]

theorem add_overflow (a b : Nat) (overflow : indexLimit ≤ a + b) :
    evaluate (F := F) (G := G) .indexAdd (.cons a (.cons b .nil)) = .stopped .refused := by
  simp only [evaluate, checkedIndices]
  split <;> simp_all [Nat.not_lt.mpr overflow]

theorem mul_overflow (a b : Nat) (overflow : indexLimit ≤ a * b) :
    evaluate (F := F) (G := G) .indexMul (.cons a (.cons b .nil)) = .stopped .refused := by
  simp only [evaluate, checkedIndices]
  split <;> simp_all [Nat.not_lt.mpr overflow]

theorem sub_underflow (a b : Nat) (underflow : a < b) :
    evaluate (F := F) (G := G) .indexSub (.cons a (.cons b .nil)) = .stopped .refused := by
  simp only [evaluate, checkedIndices]
  split <;> simp_all [Nat.not_le.mpr underflow]

@[simp] theorem div_zero (a : Nat) :
    evaluate (F := F) (G := G) .indexDiv (.cons a (.cons 0 .nil)) = .stopped .refused := by
  simp [evaluate, checkedIndices]

@[simp] theorem mod_zero (a : Nat) :
    evaluate (F := F) (G := G) .indexMod (.cons a (.cons 0 .nil)) = .stopped .refused := by
  simp [evaluate, checkedIndices]

@[simp] theorem empty (domain : String) :
    evaluate (F := F) (G := G) (.vectorEmpty domain) .nil = .returned (.cons [] .nil) := rfl

@[simp] theorem length (domain : String) (xs : List F) (bound : xs.length < indexLimit) :
    evaluate (G := G) (.vectorLength domain) (.cons xs .nil) =
      .returned (.cons xs.length .nil) := by simp [evaluate, bound]

theorem length_exhausted (domain : String) (xs : List F) (bound : indexLimit ≤ xs.length) :
    evaluate (G := G) (.vectorLength domain) (.cons xs .nil) = .stopped .exhausted := by
  simp [evaluate, Nat.not_lt.mpr bound]

@[simp] theorem sum (domain : String) (xs : List F) :
    evaluate (G := G) (.vectorSum domain) (.cons xs .nil) =
      .returned (.cons (xs.foldl (· + ·) 0) .nil) := rfl

@[simp] theorem split (domain : String) (xs : List F)
    (positive : 0 < xs.length) (even : xs.length % 2 = 0) :
    evaluate (G := G) (.vectorSplit domain) (.cons xs .nil) =
      .returned (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) .nil)) := by
  simp [evaluate, positive, even]

theorem split_refused (domain : String) (xs : List F)
    (shape : xs.length = 0 ∨ xs.length % 2 ≠ 0) :
    evaluate (G := G) (.vectorSplit domain) (.cons xs .nil) = .stopped .refused := by
  rcases shape with empty | odd <;> simp [evaluate, *]

omit [CommRing F] [DecidableEq F] in
/-- Both contiguous outputs reconstruct the entire original vector in order. -/
theorem split_order (xs : List F) :
    xs.take (xs.length / 2) ++ xs.drop (xs.length / 2) = xs := List.take_append_drop _ _

@[simp] theorem append (domain : String) (xs : List F) (x : F) :
    evaluate (G := G) (.vectorAppend domain) (.cons xs (.cons x .nil)) =
      .returned (.cons (xs ++ [x]) .nil) := rfl

@[simp] theorem vector_equal (domain : String) (xs ys : List F) :
    evaluate (G := G) (.vectorEqual domain) (.cons xs (.cons ys .nil)) =
      .returned (.cons (decide (xs = ys)) .nil) := rfl

theorem unequal_lengths (domain : String) (xs ys : List F) (lengths : xs.length ≠ ys.length) :
    evaluate (G := G) (.vectorEqual domain) (.cons xs (.cons ys .nil)) =
      .returned (.cons false .nil) := by
  have different : xs ≠ ys := fun same => lengths (congrArg List.length same)
  simp [evaluate, different]

@[simp] theorem field_equal (domain : String) (x y : F) :
    evaluate (G := G) (.fieldEqual domain) (.cons x (.cons y .nil)) =
      .returned (.cons (decide (x = y)) .nil) := rfl

end Primitive
namespace Evaluation
variable {F G : Type} {I : PIR.Signature}
variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

-- These local options expose dependent port/value aliases during elaboration;
-- they do not change the kernel or introduce proof assumptions.
theorem exec_missing (sites : SiteObservations I) (tables : ComponentTables F G I)
    (primitive : Primitive) (args : Values (Component (assignment F G)) primitive.arguments)
    (missing : RoleFamily.sequence args = none) :
    componentOperation sites tables (.exec primitive) args .nil = .halt .incomplete := by
  simp only [componentOperation]
  split
  · rfl
  · rename_i values present
    have impossible := present.symm.trans missing
    cases impossible

theorem exec_stopping_prefix (sites : SiteObservations I) (tables : Meanings F G I)
    (primitive : Primitive) (args : Values (assignment F G) primitive.arguments)
    (reason : PIR.Stop) (stops : primitive.evaluate args = .stopped reason)
    {A : Type} (suffix : Values (assignment F G) primitive.results → PIR.Process I A) :
    (operation sites tables (.exec primitive) args .nil).bind suffix = .halt reason := by
  simp only [operation, stops, primitiveOutcome, PIR.Process.bind]

set_option backward.isDefEq.respectTransparency false in
/-- A primitive stop retains its preceding source site and cannot reach a suffix. -/
theorem marked_exec_stopping_prefix (sites : SiteObservations I) (tables : Meanings F G I)
    (site : String) (primitive : Primitive) (args : Values (assignment F G) primitive.arguments)
    (reason : PIR.Stop) (stops : primitive.evaluate args = .stopped reason)
    {A : Type} (suffix : Values (assignment F G) primitive.results → PIR.Process I A) :
    ((sites.mark site).bind fun _ => operation sites tables (.exec primitive) args .nil).bind suffix =
      (sites.mark site).bind (fun _ => .halt reason) := by
  rw [PIR.Process.bind_assoc]
  congr 1
  funext acknowledged
  exact exec_stopping_prefix sites tables primitive args reason stops suffix

/-- Pure index equality propagates operand absence without a Local stop. -/
theorem pure_index_equal_missing (sites : SiteObservations I) (tables : ComponentTables F G I)
    (right : Option Nat) :
    componentOperation sites tables .indexEqual (.cons none (.cons right .nil)) .nil =
      .done (.cons none .nil) := rfl


end Evaluation
end Zkc.Source.Structured
