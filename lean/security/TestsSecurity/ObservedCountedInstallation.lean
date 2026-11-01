module

public import TestsSecurity.SourceLoopInstallation
public import Zkc.Source.Structured.ObservedLoop

@[expose] public section

/-! Library counted presentations, definitional wrappers and direct recursion
share the same checked property installers. No test supplies a loop equation. -/
set_option autoImplicit false
namespace TestsSecurity.ObservedCountedInstallation
open Zkc.Source Zkc.Source.Structured Zkc.Obligations Zkc.Transcript
open ZkcSecurity.Source ZkcSecurity.FiatShamir
open TestsSecurity.SourceLoopInstallation
variable {carriers : Carriers}
  (escape : EscapeJudgment (PublicProperties.Event carriers) PublicProperties.Raw)

def observed (site : String) (index count state : Nat) :
    PIR.Process (Occurrence.signature carriers) Nat :=
  ObservedLoop.counted .silent site (fun state _ => step state) index count state

def wrapped (site : String) (index count state : Nat) :
    PIR.Process (Occurrence.signature carriers) Nat :=
  observed site index count state

/-- All received amounts and reached histories remain arbitrary. -/
def history_no (minimum floor index count state : Nat) (site : String)
    (history : List (PublicProperties.Event carriers))
    (valid : minimum ≤ history.length ∧ floor ≤ state) :
    Derivation PublicProperties.interface escape
      (fun final next => minimum ≤ final.length ∧ floor ≤ next) history
      (wrapped site index count state) := by
  install_source_loop_no using_invariant
    (fun final (_index _remaining : Nat) next => minimum ≤ final.length ∧ floor ≤ next)
    using_rules [step_history escape]

theorem observed_cost (index count state : Nat) (site : String) (price : ENNReal)
    (history : List (PublicProperties.Event carriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (ObservedLoop.counted Occurrence.iterations site
        (fun state _ => queryStep state) index count state) history (count * price) := by
  install_source_loop_cost per_iteration price using_rules [query_cost (carriers := carriers)]

def wrappedSend (site : String) (index count state : Nat) :
    PIR.Process (Occurrence.signature carriers) Nat :=
  ObservedLoop.counted Occurrence.iterations site (fun state _ => pairedSend state) index count state

def wrappedReceive (site : String) (index count state : Nat) :
    PIR.Process (Occurrence.signature carriers) Nat :=
  ObservedLoop.counted Occurrence.iterations site (fun state _ => pairedReceive state) index count state

theorem observed_pair (index count state : Nat) (site : String) :
    Pair ⟨0, 1, []⟩ (fun a b => a = b)
      (wrappedSend (carriers := carriers) site index count state)
      (wrappedReceive site index count state) := by
  install_source_loop_pair using_invariant (fun _ _ (a b : Nat) => a = b)
    using_rules [paired_step (carriers := carriers)]

/-- Mixed old and new presentations consume the same callback law. -/
theorem mixed_pair (index count state : Nat) (site : String) :
    Pair ⟨0, 1, []⟩ (fun a b => a = b)
      (sendLoop (carriers := carriers) site index count state)
      (wrappedReceive site index count state) := by
  install_source_loop_pair using_invariant (fun _ _ (a b : Nat) => a = b)
    using_rules [paired_step (carriers := carriers)]

/-- None returns normally. A zero amount refuses; a receive preserves the
entire optional state, including the independent marker. -/
def optionalStep (state : Option (Nat × Nat)) (_index : Nat) :
    PIR.Process (Occurrence.signature carriers) (Option (Nat × Nat)) :=
  match state with
  | none => .done none
  | some (amount, marker) =>
    if amount = 0 then .halt .refused else
      .call (.action (.receive .index "optional" 0))
        (fun reply => .done (some (amount + reply, marker)))

def optionalValid (floor : Nat) (marker : Option Nat) (state : Option (Nat × Nat)) : Prop :=
  state.map Prod.snd = marker ∧ ∀ value, state = some value → floor ≤ value.1

def optional_no (floor : Nat) (marker : Option Nat) (state : Option (Nat × Nat))
    (_index : Nat) (history : List (PublicProperties.Event carriers))
    (valid : optionalValid floor marker state) :
    Derivation PublicProperties.interface escape (fun _ next => optionalValid floor marker next)
      history (optionalStep state _index) := by
  cases state with
  | none => exact .done valid
  | some value =>
    rcases value with ⟨amount, saved⟩
    simp only [optionalStep]
    split
    · exact .halt .refused
    · apply Derivation.receive rfl
      intro raw reply decoded
      refine .done ⟨valid.1, ?_⟩
      intro value equal
      cases Option.some.inj equal
      have lower := valid.2 (amount, saved) rfl
      dsimp only at lower ⊢
      omega

def optional_loop_no (floor index count : Nat) (site : String)
    (state : Option (Nat × Nat)) (history : List (PublicProperties.Event carriers))
    (valid : optionalValid floor (state.map Prod.snd) state) :
    Derivation PublicProperties.interface escape
      (fun _ next => optionalValid floor (state.map Prod.snd) next) history
      (ObservedLoop.counted Occurrence.iterations site optionalStep index count state) := by
  install_source_loop_no using_invariant
    (fun _ (_index _remaining : Nat) next => optionalValid floor (state.map Prod.snd) next)
    using_rules [optional_no escape]

/-- Missing mathematics remains a typed callback goal. -/
def missing_no (floor index count state : Nat) (site : String)
    (history : List (PublicProperties.Event carriers)) (valid : floor ≤ state) :
    Derivation PublicProperties.interface escape (fun _ next => floor ≤ next) history
      (wrapped site index count state) := by
  fail_if_success
    solve
    | install_source_loop_no using_invariant
        (fun _ (_index _remaining : Nat) next => floor ≤ next) using_rules []
  install_source_loop_no using_invariant
    (fun _ (_index _remaining : Nat) next => floor ≤ next) using_rules []
  exact step_no escape floor _ (by assumption) _

theorem missing_cost (index count state : Nat) (site : String) (price : ENNReal)
    (history : List (PublicProperties.Event carriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (ObservedLoop.counted Occurrence.iterations site
        (fun state _ => queryStep state) index count state) history (count * price) := by
  fail_if_success
    solve
    | install_source_loop_cost per_iteration price using_rules []
  install_source_loop_cost per_iteration price using_rules []
  apply OccurrenceProperties.within_cost
  intro reached
  exact query_cost _ _ reached

theorem missing_pair (index count state : Nat) (site : String) :
    Pair ⟨0, 1, []⟩ (fun a b => a = b)
      (wrappedSend (carriers := carriers) site index count state)
      (wrappedReceive site index count state) := by
  fail_if_success
    solve
    | install_source_loop_pair using_invariant (fun _ _ (a b : Nat) => a = b) using_rules []
  install_source_loop_pair using_invariant (fun _ _ (a b : Nat) => a = b) using_rules []
  apply Pair.within
  exact paired_step _ _

def countDependent (site : String) (index count state : Nat) :
    PIR.Process (Occurrence.signature carriers) Nat :=
  ObservedLoop.counted Occurrence.iterations site
    (fun state _ => step (state + count)) index count state

def changedContinuation (site : String) : Nat → Nat → Nat → PIR.Process (Occurrence.signature carriers) Nat
  | _, 0, state => .done state
  | index, count + 1, state =>
    (Occurrence.iterations.within site index (step state)).bind
      (fun next => observed site (index + 2) count next)

def wrappedBad (site : String) (index count state : Nat) :
    PIR.Process (Occurrence.signature carriers) Nat :=
  changedContinuation site index count state

example (_index _count _state : Nat) (_site : String)
    (_history : List (PublicProperties.Event carriers)) (_valid : 0 ≤ _state) : True := by
  fail_if_success
    have _bad : Derivation PublicProperties.interface escape (fun _ next => 0 ≤ next) _history
        (countDependent _site _index _count _state) := by
      install_source_loop_no using_invariant
        (fun _ (_index _remaining : Nat) next => 0 ≤ next) using_rules [step_no escape]
  fail_if_success
    have _bad : Derivation PublicProperties.interface escape (fun _ next => 0 ≤ next) _history
        (wrappedBad _site _index _count _state) := by
      install_source_loop_no using_invariant
        (fun _ (_index _remaining : Nat) next => 0 ≤ next) using_rules [step_no escape]
  trivial

example (_index _count _state : Nat) : True := by
  fail_if_success
    have _bad : Pair ⟨0, 1, []⟩ (fun a b => a = b)
        (wrappedSend (carriers := carriers) "left" _index _count _state)
        (wrappedReceive "right" _index _count _state) := by
      solve
      | install_source_loop_pair using_invariant (fun _ _ (a b : Nat) => a = b)
          using_rules [paired_step (carriers := carriers)]
  trivial

#print axioms history_no
#print axioms observed_cost
#print axioms observed_pair
#print axioms mixed_pair
#print axioms optional_loop_no
#print axioms missing_no
#print axioms missing_cost
#print axioms missing_pair
end TestsSecurity.ObservedCountedInstallation
