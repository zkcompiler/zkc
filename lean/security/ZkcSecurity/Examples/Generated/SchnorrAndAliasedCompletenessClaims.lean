module

public import ZkcSecurity.Examples.Generated.SchnorrAndAliased
public import ZkcSecurity.Examples.Generated.Components.SchnorrAndAliasedCompleteness
public import ZkcSecurity.Tools.ClaimConstruction

@[expose] public section

/-! Generated fixed compiled-pair request and canonical receipt. The
selected theorem is checked against the meaning before attribution. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
noncomputable section

namespace ZkcSecurity.Examples.Generated.SchnorrAndAliasedCompletenessClaims
open Zkc.Claims ZkcSecurity.Claims
open ZkcSecurity.Examples.Generated.SchnorrAndAliased (original imported selected)

def capabilities := ZkcSecurity.Domains.PrimeField.blsCapabilities original (by decide +kernel)
def authority := CanonicalAuthority.authoredPair imported selected capabilities
def subject := ULift.up.{1} ZkcSecurity.Examples.Generated.SchnorrAndAliased.subject
def models : Registry authority.ModelExport := ⟨[authority.modelEntry ()]⟩
noncomputable def properties := authority.properties models

def completeData : Wire.Request := {
  subject := subject.down.reference
  property := ⟨"completeness", 0⟩
  model := ⟨HonestPair.honestModelIdentifier, [(some "producer", .application "producers.compiled" (some 0) [])]⟩
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
  theoremNormalization := []
  theoremMethods := [(⟨"fs.honest_completeness", 0⟩, ``ZkcSecurity.Examples.Generated.Components.SchnorrAndAliasedCompleteness.compiled_ideal_complete)]

claim_request completeData using library method
  (some (⟨⟨"fs.honest_completeness", 0⟩, []⟩ : Wire.Application))

#print axioms completeReceipt

end ZkcSecurity.Examples.Generated.SchnorrAndAliasedCompletenessClaims
