import Zkc.Semantics.Interpretation
import Zkc.Semantics.MonadExecution

/-! Staged interpretation for monadic complete executions, including probability.
The monad carries the entire outcome, residual state and event sequence.
-/

set_option autoImplicit false

namespace PIR.Proc

theorem runM_interpret {m : Type → Type} [Monad m] [LawfulMonad m]
    {I J : Signature} {A S E : Type}
    (operations : OperationInterpretation I J) (backend : MonadHandler m J S E)
    (source : Proc I A) (state : S) :
    (source.interpret operations).runM backend state =
      source.runM (fun op s => (operations op).runM backend s) state := by
  induction source generalizing state with
  | done value => rfl
  | halt why => rfl
  | call op next ih =>
    simp only [interpret, runM_bind, runM]
    congr 1
    funext first
    congr 1
    funext reply last
    exact ih reply last

end PIR.Proc
