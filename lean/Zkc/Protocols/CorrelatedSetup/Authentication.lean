import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Algebraic identities for affine authentication and batched gate residuals.

These ring equalities impose no randomness, hiding or authentication-security law.
-/

set_option autoImplicit false

namespace Zkc.Protocols.CorrelatedSetup.Authentication
variable {F : Type} [CommRing F]
def authKey (d x m : F) := m+x*d
theorem affine_auth (d x y m n a b c : F) :
    a*authKey d x m + b*authKey d y n+c*d =
      authKey d (a*x+b*y+c) (a*m+b*n) := by simp [authKey]; ring
theorem gate_residual (d x y z mx my mz : F) :
    authKey d x mx * authKey d y my - authKey d z mz*d =
    mx*my+(x*my+y*mx-mz)*d-(z-x*y)*d^2 := by simp [authKey]; ring
theorem batch_residual {I : Type} [Fintype I]
    (d : F) (a b errors weights : I → F) (u v : F) :
    (∑ i, weights i * (a i+b i*d-errors i*d^2))+(u+v*d) =
    ((∑ i, weights i*a i)+u) + ((∑ i, weights i*b i)+v)*d -
      (∑ i, weights i*errors i)*d^2 := by
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [← Finset.sum_mul, ← mul_assoc]
  ring

end Zkc.Protocols.CorrelatedSetup.Authentication
