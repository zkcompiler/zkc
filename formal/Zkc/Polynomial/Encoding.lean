import Zkc.Polynomial.Quadratic

/-! Injective logical coefficient serialization with an explicit dimension.

This identifies the exact ordered coefficient object. It is not a byte codec,
hash collision assumption or canonicalization modulo field-function equality.
-/

set_option autoImplicit false

namespace Zkc.Polynomial.Quadratic

variable {F : Type} {n : Nat}

def coefficients : {n : Nat} → Quadratic F n → List F
  | 0, .constant value => [value]
  | _ + 1, .node a b c => coefficients a ++ (coefficients b ++ coefficients c)

theorem coefficients_length (p : Quadratic F n) : p.coefficients.length = 3 ^ n := by
  induction p with
  | constant => rfl
  | node a b c ia ib ic =>
      simp only [coefficients, List.length_append, ia, ib, ic, pow_succ]
      omega

theorem coefficients_injective : Function.Injective (coefficients (F := F) (n := n)) := by
  intro p q same
  induction p with
  | constant value =>
      cases q
      cases List.cons.inj same |>.1
      rfl
  | node a b c ia ib ic =>
      cases q with
      | node d e f =>
          have first := List.append_inj same (by rw [coefficients_length, coefficients_length])
          have rest := List.append_inj first.2 (by rw [coefficients_length, coefficients_length])
          cases ia first.1
          cases ib rest.1
          cases ic rest.2
          rfl

end Zkc.Polynomial.Quadratic
