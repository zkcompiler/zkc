module

public import Zkc.Algebra.RingNormalization

@[expose] public section

namespace RingNormalizationTests
open Zkc.Algebra.RingExpression

def horner : Expr ℤ Nat :=
  .add (.input 0) (.mul (.input 3) (.add (.input 1) (.mul (.input 3) (.input 2))))

def expanded : Expr ℤ Nat :=
  .add (.add (.input 0) (.mul (.input 3) (.input 1)))
    (.mul (.mul (.input 3) (.input 3)) (.input 2))

example : horner.check expanded = true := by decide +kernel

/-- Commuting factors and summands does not affect the checked identity. -/
example : expanded.check (.add (.mul (.input 2) (.mul (.input 3) (.input 3)))
    (.add (.mul (.input 1) (.input 3)) (.input 0))) = true := by decide +kernel

/-- The proof is symbolic and independent of field size or characteristic. -/
theorem symbolic_horner {R : Type} [CommRing R] (a b c x : R) :
    a + x * (b + x * c) = a + x * b + (x * x) * c := by
  have identity := Expr.check_cast_sound (S := R) horner expanded (by decide +kernel)
    (fun | 0 => a | 1 => b | 2 => c | _ => x)
  simpa only [horner, expanded, Expr.map, Expr.eval] using identity

example : (Expr.neg horner).check (.neg expanded) = true := by decide +kernel
example : horner.check (.add expanded (.constant 1)) = false := by decide +kernel
example : horner.check (.add (.input 0) (.mul (.input 3) (.add (.input 1) (.input 2)))) =
    false := by decide +kernel

/-- Like-term collection is deliberately outside this sufficient criterion. -/
example : (Expr.add (.input 0) (.input 0) : Expr ℤ Nat).check
    (.mul (.constant 2) (.input 0)) = false := by decide +kernel

end RingNormalizationTests
