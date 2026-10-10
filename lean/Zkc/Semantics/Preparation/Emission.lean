import Zkc.Semantics.Preparation

/-! Event-only client of contextual preparation and its priced reference bridge.

The adaptive request/emit reference has a useful exact accounting theorem.
Emission is an ordinary external operation of the common preparation signature.
-/

set_option autoImplicit false

namespace PIR.Preparation.Emission

def signature (E : Type) : Signature := ⟨E, fun _ => Unit⟩

def handler {E : Type} : Handler (signature E) Unit E :=
  fun event state => ⟨.returned (), state, [event]⟩

open Zkc.Modules.Preparation

variable {K V E A : Type} [DecidableEq K]

def embed : Program K V E A → Proc (PIR.Preparation.signature K V (signature E)) A
  | .done value => .done value
  | .emit event tail => .call (.external event) (fun _ => embed tail)
  | .request key next => .call (.prepare key) (fun value => embed (next value))

/-- The complete state and all three accounting quantities reach the reference. -/
theorem embedding_exact (provider : Provider K V) (prices : Prices K V)
    (mode : Mode) (program : Program K V E A)
    (cache : Cache K V) :
    let actual := (embed program).run (PIR.Preparation.handler provider prices mode handler) (cache, ())
    let reference := Zkc.Modules.Preparation.run provider prices mode program cache
    actual.outcome = .returned reference.value ∧ actual.state = (reference.cache, ()) ∧
    observeEvents view actual.events = reference.trace ∧
    work actual.events = reference.work ∧ saved actual.events = reference.saved ∧
    overhead actual.events = reference.overhead := by
  induction program generalizing cache with
  | done value => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | emit event tail ih =>
      obtain ⟨ho, hc, ht, hw, hs, hp⟩ := ih cache
      exact ⟨ho, hc, congrArg (List.cons event) ht, hw, hs, hp⟩
  | request key next ih =>
      obtain ⟨ho, hc, ht, hw, hs, hp⟩ :=
        ih (acquire provider prices mode cache key).value
          (acquire provider prices mode cache key).cache
      refine ⟨ho, hc, ht, ?_, ?_, ?_⟩
      · exact congrArg (Nat.add (acquire provider prices mode cache key).work) hw
      · exact congrArg (Nat.add (acquire provider prices mode cache key).saved) hs
      · exact congrArg (Nat.add (acquire provider prices mode cache key).overhead) hp

/-- Accounted savings offset overhead exactly when memoization improves this
reference cost. Native lookup/allocation costs still require their own model. -/
theorem priced_improvement (provider : Provider K V) (prices : Prices K V)
    (program : Program K V E A) :
    let memo := (embed program).run
      (PIR.Preparation.handler provider prices .memo handler) (empty, ())
    let direct := (embed program).run
      (PIR.Preparation.handler provider prices .direct handler) (empty, ())
    work memo.events + overhead memo.events ≤ work direct.events ↔
      overhead memo.events ≤ saved memo.events := by
  have hm := embedding_exact provider prices .memo program empty
  have hd := embedding_exact provider prices .direct program empty
  dsimp at hm hd ⊢
  rw [hm.2.2.2.1, hm.2.2.2.2.2, hd.2.2.2.1, hm.2.2.2.2.1]
  exact priced_improvement_iff provider prices program

end PIR.Preparation.Emission
