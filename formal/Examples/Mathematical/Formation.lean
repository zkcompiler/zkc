import Zkc.Source.Mathematical.Formation
import Examples.Mathematical.Components
import Examples.Mathematical.Sigma
import Examples.Mathematical.Sumcheck

set_option autoImplicit false
namespace Examples.Mathematical
open Zkc.Source Zkc.Source.Mathematical

example : doubleMessage.Formed := by
  constructor
  · decide
  · decide
  · simp [Program.participates, PortsParticipate, doubleMessage, privateInput, shared, parties]

example (n : Nat) : (Sumcheck.protocol n).Formed := by
  constructor
  · decide
  · simp [Sumcheck.protocol, Program.sites]
  · simp [Program.participates, PortsParticipate, Sumcheck.protocol, Sumcheck.inputs,
      Sumcheck.statePort, Sumcheck.parties]

example (n : Nat) : (Sumcheck.protocol n).sites = [0, 1, 2, 3, 4, 5, 6] := rfl

def duplicateSites : Program parties language [counter] [] [] [] :=
  .query 0 .verifier .here (by decide) .nil (by decide) (.stop 0 .verifier .reject)

example : ¬ duplicateSites.Formed := by
  intro formed
  have := formed.sites_unique
  simp [duplicateSites, Program.sites] at this

def foreignOwner : Program [Party.prover] language [] [] [] [] := .stop 0 .verifier .reject

example : ¬ foreignOwner.Formed := by
  intro formed
  have := formed.participants
  simp [foreignOwner, Program.participates, PortsParticipate] at this

end Examples.Mathematical
