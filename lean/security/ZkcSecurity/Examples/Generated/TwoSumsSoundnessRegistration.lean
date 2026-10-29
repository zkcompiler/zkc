module

public import ZkcSecurity.Examples.Generated.TwoSums
public import ZkcSecurity.Examples.Generated.Components.TwoSumsSoundness
public import ZkcSecurity.Tools.ClaimConstruction

@[expose] public section

/-! Generated physical registration. Canonical authority fixes the meaning;
theorem exports are applied without per-request proof wrappers. -/
set_option autoImplicit false
noncomputable section

namespace ZkcSecurity.Examples.Generated.TwoSumsSoundnessRegistration
open Zkc.Claims ZkcSecurity.Claims

abbrev subject := ZkcSecurity.Examples.Generated.TwoSums.validatorSubject
abbrev capabilities := ZkcSecurity.Examples.Generated.Components.TwoSumsSoundness.capabilities
def authority := CanonicalAuthority.domains (ZkcSecurity.Examples.Generated.TwoSums.validatorArtifacts) capabilities

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
  theoremNormalization := [``ZkcSecurity.Examples.Generated.Components.TwoSumsSoundness.schedule, ``ZkcSecurity.Examples.Generated.Components.TwoSumsSoundness.validatorCost, ``ZkcSecurity.Examples.Generated.Components.TwoSumsSoundness.scalarBound, ``ZkcSecurity.Examples.RootProperties.TwoSums.Soundness.schedule, ``ZkcSecurity.Examples.RootProperties.TwoSums.Soundness.price, ``ZkcSecurity.Examples.RootProperties.TwoSums.Soundness.priceBound, ``ZkcSecurity.Examples.RootProperties.TwoSums.Soundness.budget, ``ZkcSecurity.Examples.RootProperties.TwoSums.Soundness.validatorCost, ``ZkcSecurity.Examples.RootProperties.TwoSums.Soundness.scalarBound, ``ZkcSecurity.Claims.CompiledSoundness.uniformSchedule]
  theoremMethods := [(⟨"fs.keyed_soundness", 0⟩, ``ZkcSecurity.Examples.Generated.Components.TwoSumsSoundness.scalar_meaning),
    (⟨"fs.keyed_charged", 0⟩, ``ZkcSecurity.Examples.Generated.Components.TwoSumsSoundness.charged_meaning)]

end ZkcSecurity.Examples.Generated.TwoSumsSoundnessRegistration
