import Zkc.Frontend.Written.Charge
import Zkc.Tests.Formal.SourceProtocolRoots
import VCVio.OracleComp.ProbComp.IndepProductEvents

namespace FixedTableSampling
open Zkc.Frontend Zkc.Tests.Formal MeasureTheory
open scoped ENNReal

/-- A frozen table fixes the set of matching rows before the independent indices are drawn. -/
theorem fixedRows {N q : Nat} [NeZero N] (good : Finset (Fin N)) :
    𝒟[AnswerTape.answerTape (Fin N) q] (Set.univ.pi fun _ => (good : Set (Fin N))) =
      ((good.card : ℝ≥0∞) / N)^q := by
  rw [AnswerTape.evalDist_answerTape_univPi]
  simp [SampleableType.evalDist_uniformSample_eq_encard_div]

/-- The source instance uses 1024 positions, tolerance 256 and 40 independent samples. -/
theorem writtenBound (draw : Written.DeclaredDraw) (amount : draw.ceiling = (3 / 4 : Rat)^40)
    (good : Finset (Fin 1024)) (few : good.card ≤ 1024 - 256) :
    𝒟[AnswerTape.answerTape (Fin 1024) 40] (Set.univ.pi fun _ => (good : Set (Fin 1024))) ≤
      ENNReal.ofReal (draw.ceiling : ℝ) := by
  rw [amount]
  push_cast
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [fixedRows]
  apply pow_le_pow_left'
  calc (good.card : ℝ≥0∞) / 1024 ≤ (768 : ℝ≥0∞) / 1024 := by gcongr; exact_mod_cast few
       _ = 3 / 4 := by
         rw [ENNReal.div_eq_div_iff (by norm_num) (by simp) (by norm_num) (by simp)]
         norm_num

#eval show IO Unit from do
  let root := (← IO.currentDir) / "../.."
  let entry ← SourceProtocolRoots.replaceOnce (root / "examples/spot_check.zkc") "spec def committed(" "def committed("
  let assembly ← assemble #[entry] (SourcePairReadback.loadModule root .original)
  let state ← IO.ofExcept (Written.sourceState assembly)
  let #[scheme] := state.results.schemes.filter (·.name == "Checked") | throw (IO.userError "missing Checked scheme")
  let charge ← IO.ofExcept (Written.declaredDraw state ⟨scheme.protocol⟩ "positions")
  if amount : charge.ceiling = (3 / 4 : Rat)^40 then
    have bound := writtenBound charge amount
    let _ := bound
    IO.println "Verified fixed-table sampling with the closed positions ceiling"
  else throw (IO.userError "wrong closed positions ceiling")

end FixedTableSampling
