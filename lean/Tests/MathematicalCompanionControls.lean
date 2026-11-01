import Tests.ReusableAggregateTwoBatches
import Tests.MathematicalCompanionSigma
import Tests.MathematicalCompanionFresh

/-! Fixed-meaning controls. Refusals below have concrete contradiction proofs;
resource exhaustion or an unsuccessful search is never the passing condition. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
noncomputable section
namespace Tests.MathematicalCompanionControls
open Zkc.Source Zkc.Source.Structured
open MathematicalCompanionFreshSources MathematicalCompanionFresh

/-- Same-typed weights cannot be swapped at the changed wrapper interface. -/
theorem swapped_weights_refused :
    ¬ WrappedGate.Goal (ringModel Int Int)
      (fun right mulWeight addWeight left => .returned ⟨
        Zkc.Protocols.AlgebraicRounds.Gate.value mulWeight addWeight left right, right, left⟩)
      (fun _ _ _ _ _ => True) := by
  intro wrong
  have result := wrong [] 7 3 2 5 trivial
  rw [wrapped_equation] at result
  have different := congrArg WrappedGate.Output.value
    (PIR.Process.done.inj result)
  norm_num [wrappedReference, Zkc.Protocols.AlgebraicRounds.Gate.value] at different

/-- Keeping the gate value while discarding a retained operand is insufficient. -/
theorem incomplete_output_refused :
    ¬ WrappedGate.Goal (ringModel Int Int)
      (fun right mulWeight addWeight left => .returned ⟨
        Zkc.Protocols.AlgebraicRounds.Gate.value addWeight mulWeight left right, 0, left⟩)
      (fun _ _ _ _ _ => True) := by
  intro wrong
  have result := wrong [] 7 3 2 5 trivial
  rw [wrapped_equation] at result
  have different := congrArg WrappedGate.Output.retainedRight
    (PIR.Process.done.inj result)
  norm_num [wrappedReference] at different

theorem missing_guard_refused :
    ¬ UnguardedRead.Goal (ringModel Int Int)
      (fun enabled values index expected =>
        match readReference (ringModel Int Int) enabled values index expected with
        | .returned output => .returned ⟨output.residual, output.retainedValues, output.retainedIndex⟩
        | .stopped reason => .stopped reason)
      (fun _ _ _ _ _ => True) := by
  intro wrong
  have stopped := wrong [] false [5] 0 2 trivial
  change PIR.Process.done _ = PIR.Process.halt .reject at stopped
  cases stopped

theorem guard_stops_before_read (model : DomainModel)
    (values : List (model.Field scalarDomain)) (index : Nat)
    (expected : model.Field scalarDomain) :
    GuardedRead.run model [] false values index expected = .halt .reject :=
  read_companion model [] false values index expected trivial

theorem out_of_bounds_still_refused (model : DomainModel)
    (values : List (model.Field scalarDomain)) (expected : model.Field scalarDomain) :
    GuardedRead.run model [] true values values.length expected = .halt .refused := by
  simpa [readReference, primitiveOutcome] using
    read_companion model [] true values values.length expected trivial

open MathematicalCompanionSigmaGoals

/-- The handler threads one service counter through both private draws. It
does not assume fresh independent services or equality of the two replies. -/
def privateReplies : PIR.Handler (Occurrence.signature (uniformCarriers Rat Rat)) Nat String
  | .enter _, state | .leave _, state => ⟨.returned (), state, []⟩
  | .action (.query site _ _), state => ⟨.returned (state + 2 : Rat), state + 1, [site]⟩
  | .action (.receive (.field _) _ _), state => ⟨.returned (7 : Rat), state, []⟩
  | .action (.receive ..), state => ⟨.stopped .refused, state, []⟩
  | .action (.send ..), state => ⟨.returned (), state, []⟩

def privateInput : Inputs.View (Component (ringModel Rat Rat).Value) :=
  { firstBase := some 2, firstPoint := some 6, secondBase := some 5, secondPoint := some 20,
    firstWitness := some 3, secondWitness := some 4,
    nonceService := some 9, challengeService := none }

def privateRun :=
  (Occurrence.participant (ringModel Rat Rat)
    ZkcExamples.Structured.Generated.Bindings.SchnorrAndRandomizedInputs.program 0
    (Inputs.pack privateInput)).run privateReplies 0

theorem two_private_draws_remain :
    privateRun.outcome = .returned (Outputs.pack { decision := none }) ∧
    privateRun.state = 2 ∧ privateRun.events = ["s0", "s2"] := by
  unfold privateRun
  rw [actual_producer]
  constructor
  · kernel_rfl
  constructor <;> kernel_rfl

theorem misplaced_private_site_refused : privateRun.events ≠ ["s2", "s0"] := by
  rw [two_private_draws_remain.2.2]
  decide

theorem missing_private_service_stops :
    ((Occurrence.participant (ringModel Rat Rat)
      ZkcExamples.Structured.Generated.Bindings.SchnorrAndRandomizedInputs.program 0
      (Inputs.pack { privateInput with nonceService := none })).run privateReplies 0).outcome =
      .stopped .incomplete := by
  rw [actual_producer]
  kernel_rfl

/-- Direct and explicit companion lookup prove exactly the same fixed goal. -/
example (model : DomainModel) : WrappedGate.Goal model (wrappedReference model)
    (fun _ _ _ _ _ => True) :=
  zkc_companion ["mathematical-companion/wrapped-gate" [model]]

#print axioms swapped_weights_refused
#print axioms incomplete_output_refused
#print axioms missing_guard_refused
#print axioms two_private_draws_remain
#print axioms misplaced_private_site_refused
end Tests.MathematicalCompanionControls
