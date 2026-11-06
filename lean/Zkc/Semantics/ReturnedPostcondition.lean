module

public import Zkc.Semantics.HandlerReturn

@[expose] public section

/-! Compose a postcondition on the value and state of a returning execution.
The original handler determines all stops and events. This judgment alone
makes no assertion about the probability of returning. -/
set_option autoImplicit false
namespace PIR.Process
open Std.Do.Internal
variable {I : Signature} {M : Type → Type} [Monad M] [LawfulMonad M] {S E A B : Type}
  {handler : MonadHandler M I S E} {initial : S}

/-- A conditional property of the actual record at a given initial state. -/
def OnReturn (handler : MonadHandler M I S E) (initial : S) (p : Process I A)
    (post : A → S → Prop) : Prop :=
  Ensures (fun rec ↦ ∀ a, rec.outcome = .returned a → post a rec.state) (p.runM handler initial)

theorem OnReturn.bind {first : Process I A} {next : A → Process I B}
    {middle : A → S → Prop} {post : B → S → Prop}
    (head : OnReturn handler initial first middle)
    (tail : ∀ value state, middle value state → OnReturn handler state (next value) post) :
    OnReturn handler initial (first.bind next) post := by
  unfold OnReturn at *
  rw [PIR.runM_bind]
  apply head.bind
  rintro ⟨out, state, events⟩ checked
  cases out with
  | stopped why => exact Zkc.MonadicPostcondition.pure _ _ (by intro _ eq; cases eq)
  | returned a => exact Zkc.MonadicPostcondition.map (tail a state (checked a rfl)) _ (fun _ result ↦ result)

end PIR.Process
