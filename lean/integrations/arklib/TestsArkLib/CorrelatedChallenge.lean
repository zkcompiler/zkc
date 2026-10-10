import ZkcArkLib.Sumcheck.OneRound.Security
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace TestsArkLib.CorrelatedChallenge
open ZkcArkLib.Sumcheck.OneRound Zkc.Protocols.Sumcheck.ProductFamily.OneRound ZkcArkLib.Probability OracleComp ENNReal

open OracleComp

def controlEmbed (d : Fin 5) : ZMod 5 := d.val

def attack (d : Fin 5) : Zkc.Protocols.AlgebraicRounds.Early.Message (ZMod 5) :=
  if d.val = 0 then (0,0,0) else if d.val = 1 then (3,4,0)
  else if d.val = 2 then (2,1,0) else if d.val = 3 then (0,4,1) else (1,3,0)

/-- Marginally uniform challenge, but the pre-draw state already determines it. -/
def correlated : ProbComp (Option Unit) := do
  let st ← $ᵗ (Fin 5)
  let msg := attack st
  pure (verdict 0 msg.1 msg.2.1 msg.2.2 (controlEmbed st))

theorem diagonal_accept (d : Fin 5) :
    let msg := attack d
    verdict 0 msg.1 msg.2.1 msg.2.2 (controlEmbed d) = some () := by
  fin_cases d <;> decide

theorem correlated_acceptance : Pr[= some () | correlated] = 1 := by
  simp [correlated,diagonal_accept]

/-- A sampler can be uniform marginally while completely predictable from pre-draw state. -/
def correlatedJoint : ProbComp (Fin 5 × Fin 5) := do
  let st ← $ᵗ (Fin 5)
  pure (st,st)

theorem correlated_marginal : 𝒟[Prod.snd <$> correlatedJoint] = 𝒟[$ᵗ (Fin 5)] := by
  simp [correlatedJoint]

theorem correlated_not_fresh :
    Pr[= ((0 : Fin 5),(1 : Fin 5)) | correlatedJoint] = 0 := by
  simp [correlatedJoint]

/-- Same attack table and uniform private coins, with a genuinely fresh second draw. -/
theorem control_fresh_mass :
    Pr[= some () | experiment controlEmbed ($ᵗ (Fin 5)) (fun _ => attack) 0] =
      (6 : ℝ≥0∞) / 25 := by
  have each (st : Fin 5) :
      Pr[= some () | actual controlEmbed (fun _ => attack) 0 st] =
        (if st.val = 3 then (2 : ℝ≥0∞) else 1) / 5 := by
    rw [actual_eq]
    change Pr[= some () | freshVerdict controlEmbed 0 (attack st).1
      (attack st).2.1 (attack st).2.2] = _
    rw [fresh_mass]
    have counts : ∀ t : Fin 5,
        (Finset.univ.filter (fun d => verdict (0 : ZMod 5) (attack t).1
          (attack t).2.1 (attack t).2.2 (controlEmbed d) = some ())).card =
            if t.val = 3 then 2 else 1 := by decide
    rw [counts]
    split <;> simp_all
  simp [experiment,probOutput_bind_eq_sum_fintype,each,Fin.sum_univ_succ]
  have h : (5 : NNReal)⁻¹ * 5⁻¹ + (5⁻¹ * 5⁻¹ +
      (5⁻¹ * 5⁻¹ + (5⁻¹ * (2 / 5) + 5⁻¹ * 5⁻¹))) = 6 / 25 := by norm_num
  have hh := congrArg (fun x : NNReal => (x : ℝ≥0∞)) h
  simpa only [ENNReal.coe_add,ENNReal.coe_mul,ENNReal.coe_ofNat,
    ENNReal.coe_inv (by norm_num : (5 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (5 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (25 : NNReal) ≠ 0)] using hh


end TestsArkLib.CorrelatedChallenge
