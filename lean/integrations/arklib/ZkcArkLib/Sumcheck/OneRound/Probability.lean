import Zkc.Protocols.Sumcheck.ProductFamily.OneRound
import ZkcArkLib.Probability

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.Sumcheck.OneRound
open Zkc.Protocols.Sumcheck.ProductFamily.OneRound ZkcArkLib.Probability OracleComp ENNReal
def freshVerdict {F D : Type} [CommRing F] [DecidableEq F] [SampleableType D]
    (embed : D → F) (s a b c : F) : ProbComp (Option Unit) := do
  let d ← $ᵗ D
  pure (verdict s a b c (embed d))

theorem fresh_mass {F D : Type} [CommRing F] [DecidableEq F]
    [SampleableType D] [Fintype D] (embed : D → F) (s a b c : F) :
    Pr[= some () | freshVerdict embed s a b c] =
      ((Finset.univ.filter (fun d => verdict s a b c (embed d) = some ())).card : ℝ≥0∞) /
        Fintype.card D := by
  classical
  simp only [freshVerdict,bind_pure_comp]
  rw [← probEvent_eq_eq_probOutput,probEvent_map]
  exact probEvent_uniformSample D _

theorem fresh_bound {F D : Type} [Field F] [DecidableEq F]
    [SampleableType D] [Fintype D] (embed : D → F) (inj : Function.Injective embed)
    (s a b c : F) (hs : s ≠ 2) :
    Pr[= some () | freshVerdict embed s a b c] ≤ (2 : ℝ≥0∞) / Fintype.card D := by
  rw [fresh_mass]
  apply ENNReal.div_le_div_right
  exact_mod_cast accepting_card embed inj s a b c hs


end ZkcArkLib.Sumcheck.OneRound
