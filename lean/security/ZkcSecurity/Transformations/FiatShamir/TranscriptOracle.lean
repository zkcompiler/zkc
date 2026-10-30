module

public import Zkc.Construction.DomainTranscript
public import ZkcSecurity.ProgramLogic.Transcript.Interface

@[expose] public section

/-! The public history-oracle signature, shared by honest and adversarial
experiments. Private sampling is deliberately absent from this interface. -/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.TranscriptOracle

abbrev Spec {E : Type} (Raw : E → Type) := OracleSpec.ofFn (Typed.ByLast Raw)

abbrev DomainSpec (carriers : Zkc.Source.Structured.Carriers) :=
  Spec (@Zkc.Construction.Domain.Raw carriers)

/-- Factoring ownership does not enlarge the existing adversary interface. -/
theorem domainSpec_eq (carriers : Zkc.Source.Structured.Carriers) :
    DomainSpec carriers = OracleSpec.ofFn
      (Typed.ByLast (@Zkc.Construction.Domain.Raw carriers)) := rfl

end ZkcSecurity.FiatShamir.TranscriptOracle
