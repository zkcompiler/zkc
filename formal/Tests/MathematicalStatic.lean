import Zkc.Source.Mathematical.StaticNormalization

/-! Meaning and refusal checks for symbolic dimensions used by admission. -/

set_option autoImplicit false
namespace Tests.MathematicalStatic
open Zkc.Source.Mathematical.Static

private def literal {arity : Nat} (value : Nat) (bound : value < limit := by decide) :
    Expression arity := .literal ⟨value, bound⟩

private def x : Expression 3 := .parameter ⟨0, by decide⟩
private def y : Expression 3 := .parameter ⟨1, by decide⟩
private def z : Expression 3 := .parameter ⟨2, by decide⟩

private def keyOf {arity : Nat} (expression : Expression arity) :
    Except NormalizationError String := (normalize expression).map Normalized.key

private def equal {arity : Nat} (left right : Expression arity) : Bool :=
  match equality left right with
  | .ok (some _) => true
  | _ => false

example : equal (.multiply x (.add y z)) (.add (.multiply y x) (.multiply z x)) = true := rfl
example : equal (.add x x) (.multiply (literal 2) x) = true := rfl
example : equal (.multiply (literal 0) x) (literal 0) = true := rfl
example : equal (.pow2 (.add x y)) (.pow2 (.add y x)) = true := rfl
example : equal (.pow2 (literal 3 : Expression 0)) (literal 8) = true := rfl
example : equal (.add x (literal 1)) (.add x (literal 2)) = false := rfl

-- Normalized closed dimensions are literal syntax; normalized parameters do
-- not acquire redundant arithmetic wrappers during repeated substitution.
example : (normalize (.pow2 (literal 3 : Expression 0))).map (fun value => value.expression.erase) =
    .ok (.literal 8) := rfl
example : (normalize (.add x (literal 0))).map (fun value => value.expression.erase) =
    .ok (.parameter 0) := rfl

example (source : Expression 0) (result : Normalized source) :
    result.expression.erase = .literal (source.eval Fin.elim0) := result.closed_literal

example : keyOf (literal 0 : Expression 0) = .ok "" := rfl
example : keyOf (literal 8 : Expression 0) = keyOf (literal 8 : Expression 3) := rfl
example : (normalize (.pow2 (literal 3 : Expression 0)) 3).isOk = false := rfl
example : (normalize (.pow2 (literal 3 : Expression 0)) 4).isOk = true := rfl

-- Exponent addition is deliberately opaque; no exponential identity is used.
example : equal (.pow2 (.add x y)) (.multiply (.pow2 x) (.pow2 y)) = false := rfl

example : keyOf (.add x (literal 2)) = .ok "2[]1[2:p0]" := rfl
example : keyOf (.multiply x (.add y z)) = .ok "1[2:p02:p1]1[2:p02:p2]" := rfl
example : keyOf (.pow2 (.add x y)) = .ok "1[15:e1[2:p0]1[2:p1]]" := rfl

example : keyOf (.multiply (literal 0 : Expression 0) (.pow2 (literal 64))) =
    .error .overflow := rfl
example : keyOf (.add (literal 18446744073709551615 : Expression 0) (literal 1)) =
    .error .overflow := rfl
example : keyOf (.multiply (literal 18446744073709551615) (.add x x)) =
    .error .resource := rfl
example : (normalize (.multiply (.add x y) (.add y z)) 10).isOk = false := rfl

-- This proof uses the returned semantic certificate, not execution at a few
-- sample assignments. The equality holds for every natural parameter tuple.
theorem distributed_dimension (parameters : Fin 3 → Nat) :
    (Expression.multiply x (.add y z)).eval parameters =
      (Expression.add (.multiply y x) (.multiply z x)).eval parameters := by
  let certificate := (equality (.multiply x (.add y z))
    (.add (.multiply y x) (.multiply z x))).toOption.getD none
  have present : certificate.isSome = true := rfl
  exact (certificate.get present).sound parameters

-- Normalization may erase a parameter under zero. Closed admission must still
-- evaluate the authored tree to detect intermediate overflow after substitution.
example : keyOf (.multiply (literal 0) (.pow2 x)) = .ok "" := rfl
example : ((Expression.multiply (literal 0) (.pow2 x)).checked
    (fun _ => ⟨64, by decide⟩)).isOk = false := rfl

end Tests.MathematicalStatic
