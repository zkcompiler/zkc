module

public import Zkc.Semantics.MonadExecution
public import Zkc.Semantics.MonadicPostcondition

@[expose] public section

/-! A handler may refuse a checked operation. Its successful reply can still
determine the continuation. These rules reason about the original complete
record, including the state on every refusal. -/
set_option autoImplicit false
namespace PIR.Process
open Std.Do.Internal Zkc
variable {I : Signature} {m : Type → Type} [Monad m] [LawfulMonad m]
  {S E A B : Type} {handler : MonadHandler m I S E} {invariant : S → Prop}

/-- Every reached record satisfies the state invariant. A return exposes the
specified value. No totality or amount of returned mass is assumed. -/
def ReturnsUnder (handler : MonadHandler m I S E) (invariant : S → Prop)
    (process : Process I A) (expected : A) : Prop :=
  ∀ state, invariant state → Ensures
    (fun record ↦ invariant record.state ∧ ∀ value, record.outcome = .returned value → value = expected)
    (process.runM handler state)

theorem ReturnsUnder.done (value : A) : ReturnsUnder handler invariant (.done value) value :=
  fun _ valid ↦ MonadicPostcondition.pure _ _ ⟨valid, fun _ equal ↦ (Outcome.returned.inj equal).symm⟩

theorem ReturnsUnder.bind {first : Process I A} {next : A → Process I B} {a : A} {b : B}
    (head : ReturnsUnder handler invariant first a)
    (tail : ReturnsUnder handler invariant (next a) b) :
    ReturnsUnder handler invariant (first.bind next) b := by
  intro state valid
  rw [PIR.runM_bind]
  apply (head state valid).bind
  rintro ⟨outcome, current, events⟩ ⟨kept, reply⟩
  cases outcome with
  | stopped reason => exact MonadicPostcondition.pure _ _ ⟨kept, by intro _ equal; cases equal⟩
  | returned value =>
    obtain rfl := reply value rfl
    exact MonadicPostcondition.map (tail current kept) _ (fun _ law ↦ law)

theorem ReturnsUnder.action (op : I.Op) (expected : I.Reply op)
    (law : ∀ state, invariant state → Ensures
      (fun record ↦ invariant record.state ∧ ∀ value, record.outcome = .returned value → value = expected)
      (handler op state)) :
    ReturnsUnder handler invariant (.call op .done) expected := by
  intro state valid
  change Ensures _ (handler op state >>= _)
  apply (law state valid).bind
  rintro ⟨outcome, current, events⟩ post
  cases outcome <;> simp only [Execution.followM, Process.runM, pure_bind, List.append_nil] <;>
    exact MonadicPostcondition.pure _ _ post

end PIR.Process
