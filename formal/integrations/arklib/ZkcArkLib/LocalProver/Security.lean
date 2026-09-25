import ZkcArkLib.LocalProver.Probability
import ZkcArkLib.Sumcheck.OneRound.Kernel

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.LocalProver
open OracleComp ENNReal Zkc.Protocols.Sumcheck.LocalProver

/-- The boundary executes the existing ArkLib reduction, with the frozen message. -/
def finish {F D : Type} [CommRing F] [DecidableEq F] (embed : D → F)
    (draw : Boundary F → ProbComp D) : Cut F → ProbComp (Option Unit)
  | .stopped _ => pure none
  | .committed b => ZkcArkLib.Sumcheck.OneRound.Kernel.actualKernel embed (draw b)
      (fun _ (b : Boundary F) => b.message) b.claim b

def actual {F D : Type} [CommRing F] [DecidableEq F] (embed : D → F)
    (draw : Boundary F → ProbComp D) (p : Code) (inputs : List F) : ProbComp (Option Unit) :=
  exec (finish embed draw) p (initial inputs)

theorem source_bound {F D : Type} [Field F] [DecidableEq F] [Fintype D]
    (embed : D → F) (inj : Function.Injective embed) (draw : Boundary F → ProbComp D)
    (p : Code) (inputs : List F) (ε : ℝ≥0∞)
    (cap : ∀ b, Reaches p (initial inputs) (.committed b) → ∀ d, Pr[= d | draw b] ≤ ε)
    (false_claim : ∀ b, Reaches p (initial inputs) (.committed b) → b.claim ≠ 2) :
    Pr[= some () | actual embed draw p inputs] ≤ 2 * ε := by
  rw [actual, normalize, ← probEvent_eq_eq_probOutput]
  apply probEvent_bind_le_of_forall_le
  intro out hout
  cases out with
  | stopped st => simp [finish]
  | committed b =>
      have hb := (support_iff_reaches p (initial inputs) (.committed b)).mp hout
      rw [probEvent_eq_eq_probOutput]
      have h := ZkcArkLib.Sumcheck.OneRound.Kernel.adaptive_claim_bound embed inj (pure b) draw
        (fun _ (b : Boundary F) => b.message) Boundary.claim ε
        (by
          intro st hst
          have he : st = b := by simpa using hst
          subst st
          exact cap b hb)
        (by
          intro st hst
          have he : st = b := by simpa using hst
          subst st
          exact false_claim b hb)
      simpa [finish] using h


end ZkcArkLib.LocalProver
