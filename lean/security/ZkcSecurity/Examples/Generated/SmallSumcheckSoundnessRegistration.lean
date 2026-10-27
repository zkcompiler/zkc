module

public import ZkcSecurity.Examples.Generated.SmallSumcheck
public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckSoundness
public import ZkcSecurity.Tools.ClaimConstruction

@[expose] public section

/-! Generated physical registration. Canonical authority fixes the meaning;
theorem exports are applied without per-request proof wrappers. -/
set_option autoImplicit false
noncomputable section

namespace ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessRegistration
open Zkc.Claims ZkcSecurity.Claims

abbrev subject := ZkcSecurity.Examples.Generated.SmallSumcheck.validatorSubject
abbrev capabilities := ZkcSecurity.Examples.Generated.Components.SmallSumcheckSoundness.capabilities
def authority := CanonicalAuthority.domains (ZkcSecurity.Examples.Generated.SmallSumcheck.validatorArtifacts) capabilities

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
  theoremNormalization := [``ZkcSecurity.Examples.Generated.Components.SmallSumcheckSoundness.schedule, ``ZkcSecurity.Examples.Generated.Components.SmallSumcheckSoundness.validatorCost, ``ZkcSecurity.Examples.Generated.Components.SmallSumcheckSoundness.scalarBound, ``ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness.schedule, ``ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness.price, ``ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness.priceBound, ``ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness.budget, ``ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness.validatorCost, ``ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness.scalarBound, ``ZkcSecurity.Claims.CompiledSoundness.uniformSchedule]
  theoremMethods := [(⟨"fs.keyed_soundness", 0⟩, ``ZkcSecurity.Examples.Generated.Components.SmallSumcheckSoundness.scalar_meaning),
    (⟨"fs.keyed_charged", 0⟩, ``ZkcSecurity.Examples.Generated.Components.SmallSumcheckSoundness.charged_meaning)]

end ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessRegistration
