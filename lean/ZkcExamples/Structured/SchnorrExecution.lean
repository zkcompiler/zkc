module

public import ZkcExamples.Structured.SchnorrInteractive

@[expose] public section

/-! The full returned tuple of the actual admitted verifier. Acceptance and
contract observations can use this execution without fabricating an output.
The handler is the existing causal one-session transcript strategy. -/
namespace ZkcExamples.Structured.SchnorrExecution
open Zkc.Source Zkc.Source.Structured SchnorrInteractive
open Zkc.Protocols.Schnorr.Common

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option smartUnfolding false

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

def execute (base key : G) (service : Nat) (prover : Strategy F G) (challenge : F) :=
  ((program.participant F G 1 (verifierInputs base key service)).interpret
    CommonAdapter.project).run (transcriptHandler prover challenge) ()

/-- Both sides retain the same ordered events, state and outcome. Only the
singleton tuple packing differs from the existing decision-only verifier. -/
theorem execute_eq (base key : G) (service : Nat) (prover : Strategy F G) (challenge : F) :
    execute base key service prover challenge =
      (SchnorrInteractive.run base key service prover challenge).follow
        (fun decision state => ⟨.returned (.cons decision .nil), state, []⟩) := by
  unfold execute
  rw [verifier_outputs_equation, PIR.Proc.interpret_bind, CommonAdapter.project_embed,
    PIR.run_bind]
  simp only [Zkc.Protocols.Schnorr.Common.run, verifier_correspondence]
  rfl

theorem accepted_iff (base key : G) (service : Nat) (prover : Strategy F G) (challenge : F) :
    (execute base key service prover challenge).outcome =
      .returned (.cons (some true) .nil) ↔
    (SchnorrInteractive.run base key service prover challenge).outcome = .returned (some true) := by
  rw [execute_eq]
  generalize SchnorrInteractive.run base key service prover challenge = result
  rcases result with ⟨outcome, state, events⟩
  cases outcome with
  | stopped reason => exact ⟨(by intro impossible; cases impossible),
      (by intro impossible; cases impossible)⟩
  | returned decision =>
    constructor
    · intro same
      have outputs := PIR.Outcome.returned.inj same
      exact congrArg PIR.Outcome.returned (congrArg (fun values => values.get .here) outputs)
    · intro same
      cases PIR.Outcome.returned.inj same
      rfl

theorem events_eq (base key : G) (service : Nat) (prover : Strategy F G) (challenge : F) :
    (execute base key service prover challenge).events =
      (SchnorrInteractive.run base key service prover challenge).events := by
  rw [execute_eq]
  generalize SchnorrInteractive.run base key service prover challenge = result
  rcases result with ⟨outcome, state, events⟩
  cases outcome <;> simp [PIR.Execution.follow]

end ZkcExamples.Structured.SchnorrExecution
