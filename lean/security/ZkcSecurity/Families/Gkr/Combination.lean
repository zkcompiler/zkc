module

public import ZkcSecurity.Families.Gkr.Circuit
public import Zkc.Polynomial.Multilinear.Line
public import Zkc.Protocols.AlgebraicRounds.Gate

public section

/-! GKR's two-to-one reduction uses a polynomial on the line through the two
Sumcheck points. Its degree is the circuit width, not the round degree two.
The endpoint test proves disagreement with that polynomial before the draw.
-/

namespace ZkcSecurity.Families.Gkr.Combination
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open Zkc.Protocols.AlgebraicRounds

variable {F : Type} [Field F] {width : Nat}

theorem different (below : Table F width) (left right : Fin width → F)
    (add mul claim first : F) (coefficients : List F)
    (head : coefficients.headD 0 = first)
    (wrong : claim ≠ Gate.value add mul (extension width below left) (extension width below right))
    (checked : claim = Gate.value add mul first coefficients.sum) :
    coefficientPolynomial coefficients ≠ linePolynomial width below left right := by
  intro same
  have atZero := congrArg (fun p : Polynomial F => p.eval 0) same
  have atOne := congrArg (fun p : Polynomial F => p.eval 1) same
  rw [coefficientPolynomial_eval_zero, head, linePolynomial_zero] at atZero
  rw [coefficientPolynomial_eval_one, linePolynomial_one] at atOne
  exact wrong (by simpa only [atZero, atOne] using checked)

theorem honest_endpoints (below : Table F width) (left right : Fin width → F)
    (coefficients : List F)
    (honest : coefficientPolynomial coefficients = linePolynomial width below left right) :
    coefficients.headD 0 = extension width below left ∧
      coefficients.sum = extension width below right := by
  constructor
  · simpa only [coefficientPolynomial_eval_zero, linePolynomial_zero] using
      congrArg (fun p : Polynomial F => p.eval 0) honest
  · simpa only [coefficientPolynomial_eval_one, linePolynomial_one] using
      congrArg (fun p : Polynomial F => p.eval 1) honest

theorem honest_evaluation (below : Table F width) (left right : Fin width → F)
    (coefficients : List F)
    (honest : coefficientPolynomial coefficients = linePolynomial width below left right) (t : F) :
    powerSum coefficients t = extension width below (linePoint left right t) := by
  rw [← coefficientPolynomial_eval, honest, linePolynomial_eval]

end ZkcSecurity.Families.Gkr.Combination
