import Zkc.Polynomial.EmbeddedRoots
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Protocols.Sumcheck.ProductFamily.OneRound
open _root_.Polynomial
def verdict {F : Type} [CommRing F] [DecidableEq F] (s a b c r : F) : Option Unit :=
  if a+a+b+c = s then if a+(b*r+c*(r*r)) = r+r then some () else none else none

noncomputable def discrepancy {F : Type} [CommRing F] (a b c : F) : Polynomial F :=
  C a + C (b-2) * X + C c * X^2

theorem discrepancy_eval {F : Type} [CommRing F] (a b c r : F) :
    (discrepancy a b c).eval r = a+(b*r+c*(r*r))-(r+r) := by
  simp [discrepancy]
  ring

theorem discrepancy_degree {F : Type} [CommRing F] [Nontrivial F] (a b c : F) :
    (discrepancy a b c).natDegree ≤ 2 := by
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le
    · simp
    · exact (natDegree_mul_le).trans (by simp)
  · exact (natDegree_mul_le).trans (by simp)

theorem discrepancy_nonzero {F : Type} [CommRing F] (s a b c : F)
    (hs : s ≠ 2) (hb : a+a+b+c = s) : discrepancy a b c ≠ 0 := by
  intro h
  have h0 := congrArg (fun p : Polynomial F => p.eval 0) h
  have h1 := congrArg (fun p : Polynomial F => p.eval 1) h
  simp [discrepancy] at h0 h1
  apply hs
  rw [← hb]
  linear_combination h0 + h1

/-- Actual n1 acceptance can hold at at most two embedded challenges for a false claim. -/
theorem accepting_card {F D : Type} [Field F] [DecidableEq F] [Fintype D]
    (embed : D → F) (inj : Function.Injective embed) (s a b c : F) (hs : s ≠ 2) :
    (Finset.univ.filter (fun d => verdict s a b c (embed d) = some ())).card ≤ 2 := by
  classical
  by_cases hb : a+a+b+c = s
  · have hsub : Finset.univ.filter (fun d => verdict s a b c (embed d) = some ()) ⊆
        Finset.univ.filter (fun d => (discrepancy a b c).eval (embed d) = 0) := by
      intro d hd
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hd ⊢
      simp [verdict,hb] at hd
      rw [discrepancy_eval,sub_eq_zero]
      exact hd
    exact (Finset.card_le_card hsub).trans
      ((Zkc.Polynomial.embedded_roots embed inj _ (discrepancy_nonzero s a b c hs hb)).trans
        (discrepancy_degree a b c))
  · simp [verdict,hb]


end Zkc.Protocols.Sumcheck.ProductFamily.OneRound
