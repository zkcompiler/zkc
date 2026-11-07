module

public import Zkc.Semantics.MonadExecution

@[expose] public section

/-! A handler can be replaced on operations outside a component's signature
of possible calls. Equality covers full executions in the selected monad. -/
set_option autoImplicit false
namespace PIR.Process
variable {I : Signature} {A B S E : Type}

/-- Structural upper bound over all replies, including unexecuted suffixes. -/
def CallsWithin (allowed : I.Op → Prop) : Process I A → Prop
  | .done _ | .halt _ => True
  | .call op next => allowed op ∧ ∀ reply, CallsWithin allowed (next reply)

theorem CallsWithin.bind {allowed : I.Op → Prop} (process : Process I A) (next : A → Process I B)
    (head : CallsWithin allowed process) (tail : ∀ a, CallsWithin allowed (next a)) :
    CallsWithin allowed (process.bind next) := by
  induction process with
  | done a => exact tail a
  | halt why => trivial
  | call op branch ih => exact ⟨head.1, fun reply ↦ ih reply (head.2 reply)⟩

theorem CallsWithin.runM_congr {m : Type → Type} [Monad m] {allowed : I.Op → Prop}
    (process : Process I A) (restricted : CallsWithin allowed process) (left right : MonadHandler m I S E)
    (agree : ∀ op, allowed op → ∀ state, left op state = right op state) (state : S) :
    process.runM left state = process.runM right state := by
  induction process generalizing state with
  | done _ | halt _ => rfl
  | call op branch ih =>
    simp only [runM, agree op restricted.1 state]
    have tail : (fun reply ↦ (branch reply).runM left) = fun reply ↦ (branch reply).runM right :=
      funext fun reply ↦ funext (ih reply (restricted.2 reply))
    rw [tail]

end PIR.Process
