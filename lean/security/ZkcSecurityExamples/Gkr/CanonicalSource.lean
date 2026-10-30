module

public import ZkcSecurityExamples.Gkr.Canonical
public import ZkcSecurityExamples.Gkr.SourceValidator

@[expose] public section

/-! The registered circuit-output target supplies falsity for every typed
statement. The occurrence validator's proof performs its own admission split. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalSource
open Zkc.Source Zkc.Source.Structured Zkc.Obligations
open ZkcSecurity.Source ZkcExamples.Structured
variable {F G : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]
attribute [local instance] ZkcSecurity.FiatShamir.OccurrenceReading.rawSampleable

def rejected
    (statement : (Canonical.subject (ringModel F G)).validatorArtifacts.Statement (ringModel F G))
    (handle : Nat) (wrong : (Canonical.validatorSubject (ringModel F G)).FalseStatement statement)
    (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Derivation PublicProperties.interface (PublicProperties.escape (SourceValidator.price (F := F)))
      (fun _ result => result.get SourceValidator.output ≠ some true)
      history (SourceValidator.body (Canonical.invocation (ringModel F G) statement handle)) :=
  SourceValidator.rejected _ (fun correct => wrong
    ⟨fun _ _ => none, (Canonical.holds_all (ringModel F G) statement handle _).mpr correct⟩) history

#print axioms rejected
end ZkcSecurity.Realizations.Gkr.CanonicalSource
