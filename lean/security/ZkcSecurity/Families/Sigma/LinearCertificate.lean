module

public import Mathlib.Algebra.Module.BigOperators

public section

/-! A small checked algebraic method. A proposal is just the coefficients of a
linear combination. The checker validates every coefficient of the target
equation; one generic module theorem interprets the certificate. Protocol names,
verification results and an existential witness are not certificate fields. -/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sigma.LinearCertificate
open scoped BigOperators

variable {F G Row Coordinate : Type} [CommRing F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [Fintype Row] [Fintype Coordinate]

@[expose] def check (rows : Row → Coordinate → F) (target : Coordinate → F)
    (coefficients : Row → F) : Bool :=
  decide (∀ coordinate, ∑ row, coefficients row * rows row coordinate = target coordinate)

@[expose] def evaluate (row : Coordinate → F) (values : Coordinate → G) : G :=
  ∑ coordinate, row coordinate • values coordinate

/-- Only checked coefficient equality is trusted; the proposer may be a
library routine, an external solver, or an authored symbolic certificate. -/
theorem soundness (rows : Row → Coordinate → F) (target : Coordinate → F)
    (coefficients : Row → F) (checked : check rows target coefficients = true)
    (values : Coordinate → G) (accepted : ∀ row, evaluate (rows row) values = 0) :
    evaluate target values = 0 := by
  have equal : ∀ coordinate, ∑ row, coefficients row * rows row coordinate = target coordinate :=
    of_decide_eq_true checked
  unfold evaluate at accepted ⊢
  simp_rw [← equal, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum, accepted, smul_zero]
  exact Finset.sum_const_zero

end ZkcSecurity.Families.Sigma.LinearCertificate
