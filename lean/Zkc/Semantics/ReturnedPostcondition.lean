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

theorem ReturnsUnder.onReturn {p : Process I A} {a : A} {inv : S → Prop}
    (law : ReturnsUnder handler inv p a) (valid : inv initial) :
    OnReturn handler initial p (fun value state ↦ inv state ∧ value = a) :=
  (law initial valid).weaken fun _ both value returned ↦ ⟨both.1, both.2 value returned⟩

theorem OnReturn.done {value : A} {post : A → S → Prop} (valid : post value initial) :
    OnReturn handler initial (.done value) post :=
  Zkc.MonadicPostcondition.pure _ _ (fun _ eq ↦ PIR.Outcome.returned.inj eq ▸ valid)

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

/-- An opaque prefix may return any value or stop. Prove the consumer for
every reply and every post-state to keep the prefix's original behavior. -/
theorem OnReturn.bindAny {first : Process I A} {next : A → Process I B} {post : B → S → Prop}
    (tail : ∀ value state, OnReturn handler state (next value) post) :
    OnReturn handler initial (first.bind next) post := by
  apply OnReturn.bind (middle := fun _ _ ↦ True)
  · unfold OnReturn
    exact Zkc.MonadicPostcondition.of_refinement
      ((first.runM handler initial) >>= fun result ↦ pure ⟨result, fun _ _ ↦ trivial⟩)
      (by simp)
  · exact fun a state _ ↦ tail a state

end PIR.Process
