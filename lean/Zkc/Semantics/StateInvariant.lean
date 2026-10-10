import Zkc.Semantics.Execution

/-! Handler invariants apply to actual final states, including stopped calls. -/

set_option autoImplicit false

namespace PIR

variable {I : Signature} {S E A : Type}

def Handler.Preserves (handler : Handler I S E) (invariant : S → Prop) : Prop :=
  ∀ op state, invariant state → invariant (handler op state).state

theorem Proc.run_invariant (handler : Handler I S E) (invariant : S → Prop)
    (preserves : handler.Preserves invariant) (program : Proc I A)
    (state : S) (initial : invariant state) :
    invariant (program.run handler state).state := by
  induction program generalizing state with
  | done value => exact initial
  | halt why => exact initial
  | call op next ih =>
      have step := preserves op state initial
      cases outcome : (handler op state).outcome with
      | stopped why => simpa [Proc.run, Execution.follow, outcome] using step
      | returned value =>
          simpa [Proc.run, Execution.follow, outcome] using
            ih value (handler op state).state step

end PIR
