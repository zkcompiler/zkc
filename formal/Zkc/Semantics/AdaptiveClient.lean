import Zkc.Semantics.Execution

set_option autoImplicit false

namespace Zkc.Semantics.AdaptiveClient
-- Relational replacement in every inductive adaptive client; each realized branch terminates.
inductive Client (A O : Type) where
  | done
  | call : A → (O → Client A O) → Client A O

def execClient {S A O : Type} (step : A → S → O × S) :
    Client A O → S → List O × S
  | .done, s => ([], s)
  | .call a k, s =>
      let (o, t) := step a s
      let (os, u) := execClient step (k o) t
      (o :: os, u)

def signature (A O : Type) : PIR.Signature := ⟨A, fun _ => O⟩

/-- The client sees replies only. Each response is retained in the selected trace. -/
def source {A O : Type} : Client A O → PIR.Proc (signature A O) Unit
  | .done => .done ()
  | .call a next => .call a (fun o => source (next o))

def handler {S A O : Type} (step : A → S → O × S) :
    PIR.Handler (signature A O) S O := fun a s =>
  let out := step a s
  ⟨.returned out.1, out.2, [out.1]⟩

theorem execution_exact {S A O : Type} (step : A → S → O × S)
    (c : Client A O) (s : S) :
    (source c).run (handler step) s =
      ⟨.returned (), (execClient step c s).2, (execClient step c s).1⟩ := by
  induction c generalizing s with
  | done => rfl
  | call a next ih =>
    simp only [source, PIR.Proc.run, handler, PIR.Execution.follow]
    rw [ih]
    rfl

theorem adaptive_transport {S T A O : Type}
    (left : A → S → O × S) (right : A → T → O × T)
    (R : S → T → Prop)
    (law : ∀ a s t, R s t →
      (left a s).1 = (right a t).1 ∧ R (left a s).2 (right a t).2)
    (c : Client A O) (s : S) (t : T) (h : R s t) :
    (execClient left c s).1 = (execClient right c t).1 ∧
    R (execClient left c s).2 (execClient right c t).2 := by
  have handlers : PIR.HandlerRelated R (fun o => [o]) (fun o => [o])
      (handler left) (handler right) := by
    intro a s t related
    obtain ⟨outputs, states⟩ := law a s t related
    exact ⟨congrArg PIR.Outcome.returned outputs, states,
      by simp [handler, PIR.observeEvents, outputs]⟩
  have result := PIR.run_related R (fun o => [o]) (fun o => [o])
    (handler left) (handler right) handlers (source c) s t h
  rw [execution_exact, execution_exact] at result
  exact ⟨by simpa [PIR.observeEvents] using result.events, result.state⟩


end Zkc.Semantics.AdaptiveClient
