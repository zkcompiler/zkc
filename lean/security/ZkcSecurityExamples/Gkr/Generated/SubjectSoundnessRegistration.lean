module

public import ZkcSecurityExamples.Gkr.Generated.Subject
public import ZkcSecurityExamples.Gkr.Generated.Soundness
public import ZkcSecurityTools.ClaimConstruction

@[expose] public section

/-! Generated physical registration. Canonical authority fixes the meaning;
theorem exports are applied without per-request proof wrappers. -/
set_option autoImplicit false
noncomputable section

namespace ZkcSecurity.Realizations.Gkr.Generated.SubjectSoundnessRegistration
open Zkc.Claims ZkcSecurity.Claims

abbrev subject := ZkcSecurity.Realizations.Gkr.Generated.Subject.validatorSubject
abbrev capabilities := ZkcSecurity.Realizations.Gkr.Generated.Soundness.capabilities
def authority := CanonicalAuthority.domains (ZkcSecurity.Realizations.Gkr.Generated.Subject.validatorArtifacts) capabilities

def modelContext (application : String) : ModelContext := ModelContext.parameter "application" application
def models (application : String) : Registry authority.ModelExport :=
  ⟨[authority.modelEntry (modelContext application)]⟩
def properties (application : String) := authority.properties (models application)

def library : ZkcSecurity.Tools.ClaimConstruction.Library where
  subject := ``subject
  authority := some ``authority
  context := some ``modelContext
  properties := ``properties
  models := ``models
  normalization := [``authority, ``modelContext, ``properties, ``models]
  theoremNormalization := [``ZkcSecurity.Realizations.Gkr.Generated.Soundness.schedule, ``ZkcSecurity.Realizations.Gkr.Generated.Soundness.validatorCost, ``ZkcSecurity.Realizations.Gkr.Generated.Soundness.scalarBound, ``ZkcSecurity.Realizations.Gkr.CanonicalSoundness.schedule, ``ZkcSecurity.Realizations.Gkr.CanonicalSoundness.validatorCost, ``ZkcSecurity.Realizations.Gkr.CanonicalSoundness.scalarBound, ``ZkcSecurity.Realizations.Gkr.CanonicalSchedule.schedule, ``ZkcSecurity.Realizations.Gkr.CanonicalSchedule.price, ``ZkcSecurity.Realizations.Gkr.CanonicalSchedule.priceBound, ``ZkcSecurity.Realizations.Gkr.CanonicalSchedule.validatorCost, ``ZkcSecurity.Realizations.Gkr.CanonicalSchedule.scalarBound, ``ZkcSecurity.Claims.CompiledSoundness.uniformSchedule]
  theoremMethods := [(⟨"fs.keyed_soundness", 0⟩, ``ZkcSecurity.Realizations.Gkr.Generated.Soundness.scalar_meaning),
    (⟨"fs.keyed_charged", 0⟩, ``ZkcSecurity.Realizations.Gkr.Generated.Soundness.charged_meaning)]

end ZkcSecurity.Realizations.Gkr.Generated.SubjectSoundnessRegistration
