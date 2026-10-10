import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Polynomial
open _root_.Polynomial
/-- A univariate root bound for ANY injectively embedded finite challenge domain. -/
theorem embedded_roots {F D : Type} [CommRing F] [IsDomain F] [DecidableEq F]
    [Fintype D] (embed : D → F) (inj : Function.Injective embed)
    (p : Polynomial F) (hp : p ≠ 0) :
    (Finset.univ.filter (fun d => p.eval (embed d) = 0)).card ≤ p.natDegree := by
  classical
  let Z := Finset.univ.filter (fun d => p.eval (embed d) = 0)
  have hz : (Z.image embed).card ≤ p.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hx
    exact (Polynomial.mem_roots hp).mpr (Finset.mem_filter.mp hd).2
  simpa [Z,Finset.card_image_of_injective _ inj] using hz


end Zkc.Polynomial
