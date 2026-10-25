import Zkc.Construction.OriginalExecution

/-! Failure after an emitted proof message and an owner-local service call.
The physical checkpoint differs after erasure, while the explicitly named
interaction projection preserves the unread proof, service state and events. -/
set_option autoImplicit false
namespace Tests.DomainRuntimeProjection
open Zkc.Source Zkc.Construction Zkc.Construction.Domain

variable {carriers : Structured.Carriers}

private def message : Origin := .message "Root" "commit" "P" "V"
private def localOrigin : Origin := .query "Root" "coins" "private" "random.F/0" "P" (.draw "F")
private def port : ServicePort := ⟨"private", "P", 4, 9, "random.F/0"⟩
private def failingOracle : Oracle Id carriers Nat := fun _ _ state => (.stopped .refused, state + 100)
private def failingService : LocalServices Id carriers Nat := fun _ _ _ state => (.stopped .reject, state + 7)

private def program (frame : Environment carriers) : PIR.Process (effects carriers) Unit :=
  .call (.checkpoint frame) fun _ =>
  .call (.send "commit" "commit" "V" (.boolean true)) fun _ =>
  .call (.observe (.message message (.boolean true))) fun _ =>
  .call (.localService port localOrigin) fun _ =>
  .call (.query [] localOrigin) fun _ => .done ()

example (frame initial : Environment carriers) (proof : Proof carriers) (state : Nat) :
    run .producer failingOracle (program frame) ⟨initial, proof, state⟩ failingService =
      ⟨.stopped .reject, ⟨frame, proof ++ [.boolean true], state + 7⟩,
        [.message message (.boolean true)]⟩ := rfl

example (frame initial : Environment carriers) (proof : Proof carriers) (state : Nat) :
    run .producer failingOracle ((program frame).interpret Original.forgetCheckpoints)
      ⟨initial, proof, state⟩ failingService =
      ⟨.stopped .reject, ⟨initial, proof ++ [.boolean true], state + 7⟩,
        [.message message (.boolean true)]⟩ := rfl

-- The equality is at the declared abstraction, rather than at physical frames.
example (frame : Environment carriers) (proof : Proof carriers) (state : Nat) :
    ((program frame).interpret Original.forgetCheckpoints).runM
      (interactionHandler .producer failingOracle failingService) ⟨proof, state⟩ =
    (program frame).runM (interactionHandler .producer failingOracle failingService) ⟨proof, state⟩ :=
  interaction_forgetCheckpoints .producer failingOracle failingService _ _

#print axioms Zkc.Construction.Original.Simulation.source_run_interaction
end Tests.DomainRuntimeProjection
