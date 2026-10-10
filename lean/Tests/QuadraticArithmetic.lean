import Zkc.Relation.QuadraticArithmetic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

namespace Tests.QuadraticArithmetic
open Zkc.Relation RankOne

private instance : Fact (Nat.Prime 101) := ⟨by decide⟩

-- Two ordered rows: z₀*z₀=z₁ and z₁*z₀=z₂.
private def system : System (ZMod 101) 2 3 :=
  ⟨⟨#v[[⟨0,1⟩], [⟨1,1⟩]]⟩, ⟨#v[[⟨0,1⟩], [⟨0,1⟩]]⟩,
    ⟨#v[[⟨1,1⟩], [⟨2,1⟩]]⟩⟩
private def points : Fin 2 → ZMod 101 := ![1, -1]
private theorem distinct : Function.Injective points := by decide
private def honest : Fin 3 → ZMod 101 := ![3, 9, 27]
private def bad : Fin 3 → ZMod 101 := ![3, 9, 26]

example : AIR.vanishing Finset.univ points ∣ system.residual points honest := by
  apply (system.satisfies_iff_vanishing_dvd points distinct honest).mp
  unfold System.Satisfies
  decide

-- A single changed coordinate really violates divisibility; the premise is
-- actual sparse R1CS satisfaction, not an assumed final verifier equation.
example : ¬ AIR.vanishing Finset.univ points ∣ system.residual points bad := by
  rw [← system.satisfies_iff_vanishing_dvd points distinct bad]
  unfold System.Satisfies
  decide

-- Swapping C's rows alone is observable even though the same entries remain.
private def crossed : System (ZMod 101) 2 3 :=
  { system with C := ⟨#v[[⟨2,1⟩], [⟨1,1⟩]]⟩ }
example : ¬ AIR.vanishing Finset.univ points ∣ crossed.residual points honest := by
  rw [← crossed.satisfies_iff_vanishing_dvd points distinct honest]
  unfold System.Satisfies
  decide

private def paddedPoints : Fin 3 → ZMod 101 := ![1, -1, 2]
private theorem paddedDistinct : Function.Injective paddedPoints := by decide
private def publicRow : Sparse.Matrix (ZMod 101) 1 3 := ⟨#v[[⟨0, 1⟩]]⟩
example : AIR.vanishing Finset.univ paddedPoints ∣
    (system.appendTrivialRows publicRow).residual paddedPoints honest := by
  rw [system.appended_vanishing_dvd_iff publicRow paddedPoints paddedDistinct]
  unfold System.Satisfies
  decide

private def paddedAssignment : Fin 4 → ZMod 101 := ![3, 9, 27, 88]
example : AIR.vanishing Finset.univ paddedPoints ∣
    (system.pad 1 1).residual paddedPoints paddedAssignment := by
  rw [system.padded_vanishing_dvd_iff 1 1 paddedPoints paddedDistinct]
  unfold System.Satisfies
  decide

-- The all-zero assignment satisfies homogeneous equations and their QAP,
-- but never binds ONE. This rules out treating divisibility as statement binding.
example {p w n : Nat} (r : System (ZMod 101) 2 n) (layout : Layout p w n)
    (statement : Fin p → ZMod 101) :
    (AIR.vanishing Finset.univ points ∣ r.residual points (fun _ => 0)) ∧
      ¬ Bound layout statement (fun _ => 0) := by
  exact ⟨(r.satisfies_iff_vanishing_dvd points distinct _).mp r.satisfies_zero,
    System.zero_not_bound layout statement⟩

end Tests.QuadraticArithmetic
