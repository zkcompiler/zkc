import ZkcArkLib.LocalProver.Security

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.LocalProver
open OracleComp ENNReal Zkc.Protocols.Sumcheck.LocalProver

/-- Aborting produces an ordinary outcome, without a draw or probabilistic failure. -/
def response {F D : Type} (draw : Boundary F → ProbComp D) : Cut F → ProbComp (Option D)
  | .stopped _ => pure none
  | .committed b => some <$> draw b

/-- Full mathematical observer: complete local cut and the sole challenge, if any.
    Local coins are retained for conditioning, not claimed to be public. -/
def joint {F D : Type} [CommRing F] [DecidableEq F]
    (draw : Boundary F → ProbComp D) (p : Code) (inputs : List F) :
    ProbComp (Cut F × Option D) :=
  exec (fun c => (c, ·) <$> response draw c) p (initial inputs)

theorem joint_mass {F D : Type} [CommRing F] [DecidableEq F]
    (draw : Boundary F → ProbComp D) (p : Code) (inputs : List F)
    (c : Cut F) (d : Option D) :
    Pr[= (c,d) | joint draw p inputs] =
      Pr[= c | pre p (initial inputs)] * Pr[= d | response draw c] := by
  classical
  rw [joint, normalize, probOutput_bind_eq_tsum]
  simp [probOutput_prod_mk_snd_map, mul_ite]

theorem committed_mass {F D : Type} [CommRing F] [DecidableEq F]
    (draw : Boundary F → ProbComp D) (p : Code) (inputs : List F)
    (b : Boundary F) (d : D) :
    Pr[= (.committed b, some d) | joint draw p inputs] =
      Pr[= .committed b | pre p (initial inputs)] * Pr[= d | draw b] := by
  rw [joint_mass]
  simp [response]

/-- Exact conditional law, only for positive-mass (equivalently reachable) commits. -/
theorem conditional_draw {F D : Type} [CommRing F] [DecidableEq F]
    (draw : Boundary F → ProbComp D) (p : Code) (inputs : List F)
    (b : Boundary F) (hb : Reaches p (initial inputs) (.committed b)) (d : D) :
    Pr[= (.committed b, some d) | joint draw p inputs] /
      Pr[= .committed b | pre p (initial inputs)] = Pr[= d | draw b] := by
  rw [committed_mass, mul_comm]
  exact ENNReal.mul_div_cancel_right
    (probOutput_ne_zero_of_mem_support ((support_iff_reaches _ _ _).mpr hb))
    (ne_of_lt probOutput_lt_top)

theorem pre_normalized {F : Type} [CommRing F] [DecidableEq F]
    (p : Code) (inputs : List F) :
    ∑' c, Pr[= c | pre p (initial inputs)] = 1 := by
  exact tsum_probOutput_of_liftM_PMF _

theorem response_normalized {F D : Type} (draw : Boundary F → ProbComp D) (c : Cut F) :
    ∑' d, Pr[= d | response draw c] = 1 := by
  exact tsum_probOutput_of_liftM_PMF _

def observeVerdict {F D : Type} [CommRing F] [DecidableEq F]
    (embed : D → F) : Cut F × Option D → Option Unit
  | (.committed b, some d) =>
      Zkc.Protocols.Sumcheck.ProductFamily.OneRound.verdict b.claim b.message.1 b.message.2.1 b.message.2.2 (embed d)
  | _ => none

/-- The joint trace erases to the ACTUAL existing ArkLib verifier experiment. -/
theorem observer_transport {F D : Type} [CommRing F] [DecidableEq F]
    (embed : D → F) (draw : Boundary F → ProbComp D) (p : Code) (inputs : List F) :
    observeVerdict embed <$> joint draw p inputs = actual embed draw p inputs := by
  rw [joint, normalize, actual, normalize, map_bind]
  congr 1
  funext c
  cases c with
  | stopped st => simp [response, observeVerdict, finish]
  | committed b =>
      rw [finish, ZkcArkLib.Sumcheck.OneRound.Kernel.kernel_transport]
      simp [response, observeVerdict, Functor.map_map]

/-- At the standard provider, the boundary is ZkcArkLib.Sumcheck.OneRound.actual itself. -/
theorem uniform_finish {F D : Type} [CommRing F] [DecidableEq F] [SampleableType D]
    (embed : D → F) (b : Boundary F) :
    finish embed (fun _ => $ᵗ D) (.committed b) =
      ZkcArkLib.Sumcheck.OneRound.actual embed (fun _ (b : Boundary F) => b.message) b.claim b := by
  rw [finish, ZkcArkLib.Sumcheck.OneRound.Kernel.kernel_transport, ZkcArkLib.Sumcheck.OneRound.actual_eq]

theorem uniform_source_bound {F D : Type} [Field F] [DecidableEq F]
    [Fintype D] [SampleableType D] (embed : D → F) (inj : Function.Injective embed)
    (p : Code) (inputs : List F)
    (false_claim : ∀ b, Reaches p (initial inputs) (.committed b) → b.claim ≠ 2) :
    Pr[= some () | actual embed (fun _ => $ᵗ D) p inputs] ≤
      (2 : ℝ≥0∞) / Fintype.card D := by
  simpa [div_eq_mul_inv] using source_bound embed inj (fun _ => $ᵗ D) p inputs
    (Fintype.card D : ℝ≥0∞)⁻¹ (by intros; simp) false_claim


end ZkcArkLib.LocalProver
