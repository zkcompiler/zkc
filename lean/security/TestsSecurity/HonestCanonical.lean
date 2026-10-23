import ZkcSecurity.Claims.CanonicalAuthorityPair

/-! The shared fixed export consumes the exact owner semantics. These are
generic adapter controls, without a root producer proof or root receipt. -/
set_option autoImplicit false
namespace TestsSecurity.HonestCanonical
open Zkc.Claims Zkc.Source.Structured
open ZkcSecurity.Claims ZkcSecurity.Claims.HonestPair

variable {model : DomainModel} {original : Snapshot} {imported : Imported original}
  {selected : Zkc.Construction.AuthoredPair.Selection original}

theorem elaboration_pins_policy (capabilities : Domain.Capabilities model original)
    (registry : HonestPair.ModelRegistry) (request : Wire.Request)
    (subject : HonestPair.Subject model original imported selected) (result : Except Incomplete ℚ≥0)
    (elaborated : completenessArguments capabilities registry request subject = .ok result) :
    request.parameters = subject.inputPolicy.parameters := by
  unfold completenessArguments at elaborated
  cases source : subject.check request with
  | error error => simp only [source] at elaborated; cases elaborated
  | ok value =>
      simp only [source] at elaborated
      cases policy : subject.inputPolicy.checkParameters request.parameters with
      | error error => simp only [policy] at elaborated; cases elaborated
      | ok value => exact subject.inputPolicy.parameters_eq_of_checked _ policy

example (capabilities : Domain.Capabilities model original) (registry : HonestPair.ModelRegistry)
    (subject : HonestPair.CanonicalSubject model original imported selected) (error : ℚ≥0) :
    (completenessProperty capabilities registry).meaning subject (.ok error) =
      .ok (@CanonicalCompleteness model original imported selected subject.down capabilities.samples (error : ENNReal)) := by
  rfl

example (subject : HonestPair.Subject model original imported selected) :
    subject.OccurrencesChecked := ⟨subject.producerOccurrences, subject.validatorOccurrences⟩

#print axioms elaboration_pins_policy
end TestsSecurity.HonestCanonical
