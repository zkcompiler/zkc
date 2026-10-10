import Zkc.Source.Program
import Mathlib.Algebra.Ring.Basic

/-! A typed arithmetic vocabulary with a protocol-supplied effectful invocation.

Quadratic evaluation is a mathematical operation. Addition and multiplication
provide a lower-level algorithm vocabulary. The semiring interpretation justifies
their equations; arbitrary interpretations of these names need not satisfy them.
-/

set_option autoImplicit false

namespace Zkc.Source.Arithmetic

inductive Ty where
  | boolean | scalar
  deriving DecidableEq, Repr

inductive Op where
  | quadratic | add | multiply | invoke
  deriving DecidableEq, Repr

def arguments : Op → List Ty
  | .quadratic => [.scalar, .scalar, .scalar, .scalar]
  | .add | .multiply => [.scalar, .scalar]
  | .invoke => [.scalar]

abbrev language : Language := ⟨Ty, Op, arguments, fun _ => .scalar, .boolean⟩

abbrev Value (F : Type) : Ty → Type
  | .boolean => Bool
  | .scalar => F

/-- The invocation may stop, mutate state, emit observations or make many calls.
The arithmetic operations themselves have pure logical meanings. -/
abbrev interpretation {F : Type} [Semiring F] {I : PIR.Signature}
    (invoke : F → PIR.Proc I F) : Interpretation language I where
  Value := Value F
  condition := id
  operation
    | .quadratic, .cons a (.cons b (.cons c (.cons r .nil))) =>
        .done (a + (b * r + c * (r * r)))
    | .add, .cons a (.cons b .nil) => .done (a + b)
    | .multiply, .cons a (.cons b .nil) => .done (a * b)
    | .invoke, .cons value .nil => invoke value

end Zkc.Source.Arithmetic
