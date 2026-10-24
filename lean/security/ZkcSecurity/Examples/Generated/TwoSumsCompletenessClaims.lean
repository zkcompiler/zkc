module

public import ZkcSecurity.Examples.Generated.TwoSums
public import ZkcSecurity.Examples.Generated.Components.TwoSumsCompleteness
public import ZkcSecurity.Tools.ClaimConstruction

@[expose] public section

/-! Generated fixed compiled-pair request and canonical receipt. The
selected theorem is checked against the meaning before attribution. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
noncomputable section

namespace ZkcSecurity.Examples.Generated.TwoSumsCompletenessClaims
open Zkc.Claims ZkcSecurity.Claims
open ZkcSecurity.Examples.Generated.TwoSums (original imported selected)

def capabilities := ZkcSecurity.Domains.PrimeField.blsCapabilities original (by decide +kernel)
def authority := CanonicalAuthority.authoredPair imported selected capabilities
def subject := ULift.up.{1} ZkcSecurity.Examples.Generated.TwoSums.subject
def models : Registry authority.ModelExport := ⟨[authority.modelEntry ()]⟩
noncomputable def properties := authority.properties models

def completeData : Wire.Request := {
  subject := subject.down.reference
  property := ⟨"completeness", 0⟩
  parameters := subject.down.inputPolicy.parameters
  model := ⟨HonestPair.honestModelIdentifier, []⟩
  target := subject.down.targetReference
  accept := subject.down.acceptance
  quantity := .scalar (.natural 0)
  capabilities := [] }

def library : ZkcSecurity.Tools.ClaimConstruction.Library where
  subject := ``subject
  authority := some ``authority
  properties := ``properties
  models := ``models
  normalization := [``subject, ``authority, ``properties, ``models, ``capabilities]
  theoremMethods := [(⟨"fs.honest_completeness", 0⟩, ``ZkcSecurity.Examples.Generated.Components.TwoSumsCompleteness.compiled_ideal_complete)]

claim_request completeData using library method
  (some (⟨⟨"fs.honest_completeness", 0⟩, []⟩ : Wire.Application))

#print axioms completeReceipt

end ZkcSecurity.Examples.Generated.TwoSumsCompletenessClaims
