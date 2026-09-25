import Zkc.Source.PhaseAdmission
import Zkc.Source.Interpretation
import Zkc.Semantics.InterpretationAdmission

/-! Reuse checked source summaries after a lawful operation interpretation.
Certificate data stays at its source abstraction; the relation composes with
the lower protocol phases. No new invariant is guessed from a phase name.
-/

set_option autoImplicit false

namespace Zkc.Source.PhaseAdmission

variable {language : Language} {Phase : Type} {I J : PIR.Signature}
  {policy : Policy language Phase} {meaning : Interpretation language I}
  {source : PIR.Interaction I} {target : PIR.Interaction J}
  {operations : PIR.OperationInterpretation I J}

def Realizes.translate (laws : Realizes policy meaning source)
    (admission : PIR.InterpretationAdmission source target operations) :
    Realizes policy (meaning.translate operations) target where
  relates abstract lowerPhase := ∃ upperPhase,
    laws.relates abstract upperPhase ∧ admission.phases upperPhase lowerPhase
  operation := by
    intro op before exits accepted args lowerPhase related
    obtain ⟨upperPhase, formedAt, related⟩ := related
    obtain ⟨formed, returns⟩ := laws.operation op before exits accepted args upperPhase formedAt
    obtain ⟨lowerFormed, lowerReturns⟩ := admission.transport
      (meaning.operation op args) _ upperPhase lowerPhase formed returns related
    refine ⟨lowerFormed, PIR.Boundary.returns_mono target _ _ _ lowerPhase lowerReturns ?_⟩
    intro value finalPhase returning
    obtain ⟨upperFinal, ⟨after, member, summary⟩, phases⟩ := returning
    exact ⟨after, member, upperFinal, summary, phases⟩

end Zkc.Source.PhaseAdmission
