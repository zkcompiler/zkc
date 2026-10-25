module

public import Zkc.Claims.Wire
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

/-! Finite rational interpretation with explicit unsupported forms. Parameters
and model budget names are resolved through a fixed environment; absent symbols,
negative charges, division by zero and non-natural exponents are not defaults. -/

set_option autoImplicit false
namespace Zkc.Claims

abbrev NumericEnvironment := String → Option Rat

def naturalValue (value : Rat) : Except Incomplete Nat :=
  if value.den = 1 ∧ 0 ≤ value.num then .ok value.num.toNat
  else .error ⟨["natural expression"]⟩

def evaluate (environment : NumericEnvironment) : Wire.Expr → Except Incomplete Rat
  | .natural value => .ok value
  | .reference name => match environment name with
    | some value => .ok value
    | none => .error ⟨["unbound parameter: " ++ name]⟩
  | .neg operand => do return -(← evaluate environment operand)
  | .binary operator left right => do
    let left ← evaluate environment left
    let right ← evaluate environment right
    match operator with
    | .add => return left + right
    | .sub => return left - right
    | .mul => return left * right
    | .div => if right = 0 then .error ⟨["nonzero denominator"]⟩ else return left / right
    | .pow => return left ^ (← naturalValue right)
  | .application name _ _ => .error ⟨["numeric application: " ++ name]⟩
  | .list _ => .error ⟨["scalar expression"]⟩

def evaluateNatural (environment : NumericEnvironment) (expression : Wire.Expr) : Except Incomplete Nat := do
  naturalValue (← evaluate environment expression)

def evaluateNonnegative (environment : NumericEnvironment) (expression : Wire.Expr) :
    Except Incomplete {value : Rat // 0 ≤ value} := do
  let value ← evaluate environment expression
  if nonnegative : 0 ≤ value then return ⟨value, nonnegative⟩
  else .error ⟨["nonnegative expression"]⟩

end Zkc.Claims
