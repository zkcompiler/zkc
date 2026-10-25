module

public import Zkc.Construction.DomainProducer

@[expose] public section

/-! The property-independent success event for an actual compiled pair.
Both phases must return, the selected Boolean must be true, and the actual
producer's proof must be consumed completely. The oracle state is arbitrary. -/

set_option autoImplicit false
namespace Zkc.Construction.Domain
open Zkc.Source

def acceptanceAt {carriers : Structured.Carriers} (position : Nat)
    (values : Domain.Environment carriers) : Option Bool :=
  match values[position]? with
  | some (.data (.boolean decision)) => some decision
  | _ => none

namespace PairExecution

/-- Every phase must return, the exact generated proof must be exhausted, and
the selected Boolean return must be true. Stops cannot satisfy this event. -/
def Success {carriers : Structured.Carriers} {S : Type} (position : Nat)
    (observed : Domain.PairExecution carriers S) : Prop :=
  ∃ produced validated result,
    observed.producer.outcome = .returned produced ∧
    observed.validator = some validated ∧ validated.outcome = .returned result ∧
    validated.state.proof = [] ∧ acceptanceAt position result.values = some true

theorem stopped_fails {carriers : Structured.Carriers} {S : Type} (position : Nat)
    (observed : Domain.PairExecution carriers S) (reason : PIR.Stop)
    (stopped : observed.producer.outcome = .stopped reason) : ¬ Success position observed := by
  rintro ⟨_, _, _, returned, _⟩
  rw [stopped] at returned
  cases returned

theorem unread_fails {carriers : Structured.Carriers} {S : Type} (position : Nat)
    (observed : Domain.PairExecution carriers S)
    (validated : PIR.Execution (Domain.RuntimeState carriers S) (Domain.Event carriers)
      (Domain.Result carriers))
    (selected : observed.validator = some validated) (unread : validated.state.proof ≠ []) :
    ¬ Success position observed := by
  rintro ⟨_, _, _, _, same, _, consumed, _⟩
  rw [selected] at same
  cases Option.some.inj same
  exact unread consumed

theorem false_fails {carriers : Structured.Carriers} {S : Type} (position : Nat)
    (observed : Domain.PairExecution carriers S)
    (validated : PIR.Execution (Domain.RuntimeState carriers S) (Domain.Event carriers)
      (Domain.Result carriers)) (selected : observed.validator = some validated)
    (result : Domain.Result carriers) (returned : validated.outcome = .returned result)
    (rejected : acceptanceAt position result.values = some false) : ¬ Success position observed := by
  rintro ⟨_, actual, value, _, same, completed, _, accepted⟩
  rw [selected] at same
  cases Option.some.inj same
  rw [returned] at completed
  cases PIR.Outcome.returned.inj completed
  rw [rejected] at accepted
  cases accepted


/-- Both stages return, the selected Boolean is true, and no proof remains.
A producer stop is a failure even if its preceding proof would be accepted. -/
def succeeds {carriers : Structured.Carriers} {S : Type} (position : Nat)
    (execution : PairExecution carriers S) : Bool :=
  match execution.producer.outcome, execution.validator with
  | .returned _, some checked =>
      match checked.outcome with
      | .returned result =>
          (match result.values[position]? with
          | some (.data (.boolean true)) => true
          | _ => false) && checked.state.proof.isEmpty
      | .stopped _ => false
  | _, _ => false

/-- The executable observation is exactly the common logical success event. -/
theorem succeeds_iff {carriers : Structured.Carriers} {S : Type} (position : Nat)
    (execution : PairExecution carriers S) :
    succeeds position execution = true ↔ Success position execution := by
  cases hp : execution.producer.outcome with
  | stopped reason => simp [succeeds, Success, hp]
  | returned produced =>
    cases hv : execution.validator with
    | none => simp [succeeds, Success, hp, hv]
    | some checked =>
      cases hc : checked.outcome with
      | stopped reason => simp [succeeds, Success, hp, hv, hc]
      | returned result =>
        cases hvalue : result.values[position]? with
        | none => simp [succeeds, Success, acceptanceAt, hp, hv, hc, hvalue]
        | some value =>
          cases value with
          | transcript | indices => simp [succeeds, Success, acceptanceAt, hp, hv, hc, hvalue]
          | data payload =>
            cases payload <;> simp [succeeds, Success, acceptanceAt, hp, hv, hc, hvalue]
            rename_i decision
            cases decision <;> simp [and_comm]

end PairExecution

end Zkc.Construction.Domain
