module

public import ZkcExamples.Structured.SchnorrInteractive
public import Zkc.Semantics.ReturnView

@[expose] public section

/-! The full returned tuple of the actual admitted verifier. Acceptance and
contract observations can use this execution without fabricating an output.
The handler is the existing causal one-session transcript strategy. -/
namespace ZkcExamples.Structured.SchnorrExecution
open Zkc.Source Zkc.Source.Structured SchnorrInteractive
open Zkc.Protocols.Schnorr.Common

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
  exact PIR.Process.run_of_return_view
    ((program.participant F G 1 (verifierInputs base key service)).interpret CommonAdapter.project)
    (fun outputs ↦ outputs.get .here) Values.singleton Values.singleton_get
    (verifier base key service)
    (by symm; exact PIR.Process.interpret_bind CommonAdapter.project _ _)
    (transcriptHandler prover challenge) ()

/-- Every optional output is reflected, including absent and false decisions. -/
theorem returned_iff (base key : G) (service : Nat) (prover : Strategy F G) (challenge : F)
    (decision : Option Bool) :
    (execute base key service prover challenge).outcome = .returned (.cons decision .nil) ↔
      (SchnorrInteractive.run base key service prover challenge).outcome = .returned decision := by
  rw [execute_eq]
  exact PIR.Execution.follow_return_returned_iff _ _
    (fun _ _ same ↦ congrArg (fun values ↦ values.get .here) same) decision

theorem accepted_iff (base key : G) (service : Nat) (prover : Strategy F G) (challenge : F) :
    (execute base key service prover challenge).outcome =
      .returned (.cons (some true) .nil) ↔
    (SchnorrInteractive.run base key service prover challenge).outcome = .returned (some true) := by
  exact returned_iff base key service prover challenge (some true)

theorem events_eq (base key : G) (service : Nat) (prover : Strategy F G) (challenge : F) :
    (execute base key service prover challenge).events =
      (SchnorrInteractive.run base key service prover challenge).events := by
  rw [execute_eq]
  exact PIR.Execution.follow_return_events _ _

end ZkcExamples.Structured.SchnorrExecution
