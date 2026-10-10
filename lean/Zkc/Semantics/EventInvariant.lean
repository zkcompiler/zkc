import Zkc.Semantics.StateInvariant

/-! State invariants justify properties of every actually emitted event,
including prefixes retained by stopped operations and continuations. -/

set_option autoImplicit false

namespace PIR

variable {I : Signature} {S E A : Type}

def Handler.Emits (handler : Handler I S E) (invariant : S → Prop) (allowed : E → Prop) : Prop :=
  ∀ op state, invariant state → ∀ event ∈ (handler op state).events, allowed event

theorem Proc.run_events (handler : Handler I S E) (invariant : S → Prop) (allowed : E → Prop)
    (preserves : handler.Preserves invariant) (emits : handler.Emits invariant allowed)
    (program : Proc I A) (state : S) (initial : invariant state) :
    ∀ event ∈ (program.run handler state).events, allowed event := by
  induction program generalizing state with
  | done value => simp [Proc.run]
  | halt why => simp [Proc.run]
  | call op next ih =>
      intro event member
      have nextState := preserves op state initial
      cases outcome : (handler op state).outcome with
      | stopped why =>
          simp only [Proc.run, Execution.follow, outcome] at member
          exact emits op state initial event member
      | returned value =>
          simp only [Proc.run, Execution.follow, outcome, List.mem_append] at member
          rcases member with first | tail
          · exact emits op state initial event first
          · exact ih value (handler op state).state nextState event tail

end PIR
