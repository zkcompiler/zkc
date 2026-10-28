module

public import Zkc.Obligations.RepeatedComponent
public import Zkc.Semantics.OperationSupport

@[expose] public section

/-! All-replies returned frames also compose through components whose logical
claim is irrelevant to the current No branch. Query cuts still require the
explicit empty-event escape law. Reached histories and full values are kept. -/
set_option autoImplicit false
namespace PIR
variable {I : Signature} {A : Type}

theorem Yields.conj {p q : A → Prop} {process : Process I A}
    (left : Yields p process) (right : Yields q process) :
    Yields (fun value => p value ∧ q value) process := by
  induction process with
  | done => exact ⟨left,right⟩
  | halt => trivial
  | call _ _ ih => exact fun reply => ih reply (left reply) (right reply)
end PIR

namespace PIR.OperationSupport
variable {I : Signature} {A B : Type} {allowed : I.Op → Prop}

/-- A reply-independent support proof can use an independent returned frame
when checking the continuation. Stops contribute no invented return. -/
theorem bind_framed {process : Process I A} (supported : OperationSupport allowed process)
    {frame : A → Prop} (preserves : Yields frame process) (next : A → Process I B)
    (suffix : ∀ value, frame value → OperationSupport allowed (next value)) :
    OperationSupport allowed (process.bind next) := by
  induction process with
  | done value => exact suffix value preserves
  | halt => trivial
  | call operation continuation ih =>
    exact ⟨supported.1, fun reply => ih reply (supported.2 reply) (preserves reply)⟩
end PIR.OperationSupport

namespace Zkc.Obligations.Derivation
open Zkc.Transcript
variable {I : PIR.Signature} {E P A : Type} {Raw : E → Type}
  {absorb : Interface I E P Raw} {escape : EscapeJudgment E Raw}

/-- A retained false claim can survive an unrelated component using an
independent all-replies frame. The frame is never inferred from a No premise.
The empty event cannot discard any raw reply or hide an independence premise. -/
noncomputable def ofYields (empty : ∀ reached event, escape reached event (fun _ => False))
    {post : A → Prop} {process : PIR.Process I A} (preserves : PIR.Yields post process)
    (history : List E) : Derivation absorb escape (fun _ => post) history process := by
  induction process generalizing history with
  | done value => exact .done preserves
  | halt reason => exact .halt reason
  | call operation next ih =>
    rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
      ⟨event, decode⟩ | _
    · exact .receive absorbed fun message value _ => ih value (preserves value) _
    · exact .send absorbed (ih value (preserves value) _)
    · exact .query absorbed (fun _ => False) (empty history event)
        (fun _ value _ _ => ih value (preserves value) _)
    · exact .refuse absorbed

end Zkc.Obligations.Derivation

namespace PIR.WeakestPrecondition
open Std.WP
variable {I : Signature} {S E A B : Type}

/-- Successful sequential composition threads the actual handler state and
complete reached history. An allowed stop cannot establish the middle premise. -/
theorem successful_bind (handler : Handler I S E) (process : Process I A)
    (next : A → Process I B) (middle : A → S → List E → Prop)
    (post : B → S → List E → Prop) (state : S) (history : List E)
    (first : satisfies (process.run handler state) middle (fun _ _ _ => False) history)
    (suffix : ∀ value reachedState reached, middle value reachedState reached →
      satisfies ((next value).run handler reachedState) post (fun _ _ _ => False) reached) :
    satisfies ((process.bind next).run handler state) post (fun _ _ _ => False) history := by
  change runWP handler (process.bind next) post estack⟨fun _ _ _ => False⟩ state history
  rw [runWP_bind]
  cases execution : process.run handler state with
  | mk outcome final events =>
    rw [execution] at first
    simp only [runWP, execution]
    cases outcome with
    | stopped reason => exact first.elim
    | returned value => exact suffix value final (history ++ events) first
end PIR.WeakestPrecondition
