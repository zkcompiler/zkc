module

public import ZkcSecurity.Examples.Generated.SmallSumcheck
public import ZkcSecurity.Examples.Components.SumcheckSoundnessRoots
public import ZkcSecurity.Tools.ClaimConstruction

@[expose] public section

/-! Generated physical registration. Canonical authority fixes the meaning;
theorem exports are applied without per-request proof wrappers. -/
set_option autoImplicit false
noncomputable section

namespace ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessRegistration
open Zkc.Claims ZkcSecurity.Claims

abbrev subject := ZkcSecurity.Examples.Generated.SmallSumcheck.validatorSubject
abbrev capabilities := ZkcSecurity.Examples.Components.SumcheckSoundnessRoots.Small.capabilities
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
  theoremNormalization := [``ZkcSecurity.Examples.Components.SumcheckSoundnessRoots.price, ``ZkcSecurity.Examples.Components.SumcheckSoundnessRoots.priceBound, ``ZkcSecurity.Examples.Components.SumcheckSoundnessRoots.Small.schedule, ``ZkcSecurity.Claims.CompiledSoundness.uniformSchedule]
  theoremMethods := [(⟨"fs.keyed_soundness", 0⟩, ``ZkcSecurity.Examples.Components.SumcheckSoundnessRoots.Small.scalar_meaning),
    (⟨"fs.keyed_charged", 0⟩, ``ZkcSecurity.Examples.Components.SumcheckSoundnessRoots.Small.charged_meaning)]

end ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessRegistration
