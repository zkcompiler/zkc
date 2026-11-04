module

public import ZkcSecurityExamples.Generated.SmallSumcheckSoundnessRegistration
public meta import ZkcSecurityExamples.Generated.SmallSumcheckSoundnessRegistration

@[expose] public section

/-! Generated exact source requests. Regenerate with `lean/checks/check_subject_roots.py --exports DIRECTORY --write`. The common data renderer emits no property or proof wrapper. -/

namespace ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessClaims
open Zkc.Claims ZkcSecurity.Tools.ClaimConstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact source request; attachment and method are separate. -/
def request0Data : Wire.Request :=
{
  subject := ⟨"sha256:a97cec552c7c3eb40577b93eb195965de358090ac6b786cd718ffae4847ed51e", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", .compiledIdeal, [⟨"constructed-participant", "sha256:c7698d09e1962c0b0c5d5f13ece4ce9fd307f824bab26e86bbd696e7932f84aa"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 2) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .retained "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071" 1 "public_sum"
  accept := ⟨true, 0, 1, []⟩
  quantity := .scalar (.binary .div (.binary .add (.reference "Q") (.natural 2)) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))
  capabilities := []
}

def request0Method : Option Wire.Application := some ⟨⟨"fs.keyed_soundness", 0⟩, []⟩

claim_request request0Data using ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessRegistration.library method request0Method

/-- Exact source request; attachment and method are separate. -/
def request1Data : Wire.Request :=
{
  subject := ⟨"sha256:a97cec552c7c3eb40577b93eb195965de358090ac6b786cd718ffae4847ed51e", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", .compiledIdeal, [⟨"constructed-participant", "sha256:c7698d09e1962c0b0c5d5f13ece4ce9fd307f824bab26e86bbd696e7932f84aa"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 2) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .retained "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071" 1 "public_sum"
  accept := ⟨true, 0, 1, []⟩
  quantity := .charged [("reduce.challenge", (.binary .div (.natural 1) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))])))]
  capabilities := []
}

def request1Method : Option Wire.Application := some ⟨⟨"fs.keyed_charged", 0⟩, []⟩

claim_request request1Data using ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessRegistration.library method request1Method

end ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessClaims
