import Zkc.Protocols.Sumcheck.LocalProver.Source
import ZkcArkLib.LocalProver.Probability

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.LocalProver.Source
open PIR Zkc.Protocols.Sumcheck.LocalProver Zkc.Protocols.Sumcheck.LocalProver.Source

def handler : MonadHandler ProbComp sig Unit Empty := fun (n : Nat) st => do
  let x ← $ᵗ (Fin (n+1))
  pure ⟨.returned x,st,[]⟩

def retain {F : Type} (c : Cut F) : Execution Unit Empty (Cut F) :=
  ⟨.returned c,(),[]⟩

/-- Exact old probabilistic computation, including every local state/history and abort.
    A local abort is an ordinary boundary Cut here, not silent probability failure. -/
theorem execution_exact {F : Type} [Ring F] [DecidableEq F] (p : Code) (st : State F) :
    (source p st).runM handler () = retain <$> pre p st := by
  induction p generalizing st with
  | abort => simp [source, Proc.runM, pre, exec, retain]
  | assign i e p ih => simpa [source, pre, exec] using ih (write st i (eval st e))
  | random n i p ih =>
    simp only [source, Proc.runM, handler, bind_assoc, pure_bind, Execution.followM]
    simp only [pre, exec, map_bind]
    congr 1
    funext x
    rw [ih]
    simp [retain, pre, Functor.map_map]
    rfl
  | ifz e p q ihp ihq =>
    by_cases h : eval st e = 0 <;> simp [source, pre, exec, h, ihp, ihq]
  | commit s a b c => simp [source, Proc.runM, pre, exec, retain]

/-- Every complete common-execution result has mass; aborts have not been dropped. -/
theorem normalized {F : Type} [Ring F] [DecidableEq F] (p : Code) (st : State F) :
    ∑' r, Pr[= r | (source p st).runM handler ()] = 1 :=
  tsum_probOutput_of_liftM_PMF _


end ZkcArkLib.LocalProver.Source
