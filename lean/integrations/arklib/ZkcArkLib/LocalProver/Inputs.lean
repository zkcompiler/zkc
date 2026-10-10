import Zkc.Protocols.Sumcheck.LocalProver.Inputs
import ZkcArkLib.LocalProver.Probability

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.LocalProver
open OracleComp Zkc.Protocols.Sumcheck.LocalProver

variable {F A : Type} [CommRing F] [DecidableEq F]

/-- A control semantics which changes ONLY the missing-input fallback. -/
def execFallback (fallback : Nat → F) (k : Cut F → ProbComp A) :
    Code → State F → ProbComp A
  | .abort, st => k (.stopped st)
  | .assign i e p, st => execFallback fallback k p (write st i (evalFallback fallback st e))
  | .random n i p, st => do
      let x ← $ᵗ (Fin (n+1))
      execFallback fallback k p (coin st n i x)
  | .ifz e p q, st => if evalFallback fallback st e = 0 then
      execFallback fallback k p (branch st true) else execFallback fallback k q (branch st false)
  | .commit s a b c, st => k (.committed
      ⟨st,evalFallback fallback st s,evalFallback fallback st a,
        evalFallback fallback st b,evalFallback fallback st c⟩)

theorem exec_no_default (fallback : Nat → F) (k : Cut F → ProbComp A)
    (p : Code) (st : State F) (bound : ∀ i ∈ codeInputs p, i < st.inputs.length) :
    execFallback fallback k p st = exec k p st := by
  induction p generalizing st with
  | abort => rfl
  | assign i e p ih =>
    have he := eval_no_default fallback st e (fun j hj => bound j (by simp [codeInputs,hj]))
    simp only [execFallback,exec,he]
    apply ih
    intro j hj
    exact bound j (by simp [codeInputs,hj])
  | random n i p ih =>
    simp only [execFallback,exec]
    congr 1
    funext x
    apply ih
    intro j hj
    exact bound j hj
  | ifz e p q ihp ihq =>
    have he := eval_no_default fallback st e (fun j hj => bound j (by simp [codeInputs,hj]))
    simp only [execFallback,exec,he]
    split
    · exact ihp _ (fun j hj => bound j (by simp [codeInputs,hj]))
    · exact ihq _ (fun j hj => bound j (by simp [codeInputs,hj]))
  | commit s a b c =>
    have hs := eval_no_default fallback st s (fun j hj => bound j (by simp [codeInputs,hj]))
    have ha := eval_no_default fallback st a (fun j hj => bound j (by simp [codeInputs,hj]))
    have hb := eval_no_default fallback st b (fun j hj => bound j (by simp [codeInputs,hj]))
    have hc := eval_no_default fallback st c (fun j hj => bound j (by simp [codeInputs,hj]))
    simp only [execFallback,exec,boundary,hs,ha,hb,hc]


end ZkcArkLib.LocalProver
