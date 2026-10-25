module

public import ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessRegistration
public meta import ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessRegistration

@[expose] public section

/-! Generated exact source requests. The common data renderer emits no property or proof wrapper. -/

namespace ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessClaims
open Zkc.Claims ZkcSecurity.Tools.ClaimConstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact source request; attachment and method are separate. -/
def request0Data : Wire.Request :=
{
  subject := ⟨"sha256:e3ae53d4706b17e7f5a468996a1dbf8cc57a06576986392388b288fffe1a99af", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", .compiledIdeal, [⟨"constructed-participant", "sha256:ea0efdd843435f477577106f7c7bcb9df6b2a19067491b95530c5cc154875bcd"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 2) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .retained "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071" 0 "public_sum"
  accept := ⟨true, 0, 1, []⟩
  quantity := .scalar (.binary .div (.binary .add (.reference "Q") (.natural 2)) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))
  capabilities := []
}

def request0Method : Option Wire.Application := some ⟨⟨"fs.keyed_soundness", 0⟩, []⟩

claim_request request0Data using ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessRegistration.library method request0Method

/-- Exact source request; attachment and method are separate. -/
def request1Data : Wire.Request :=
{
  subject := ⟨"sha256:e3ae53d4706b17e7f5a468996a1dbf8cc57a06576986392388b288fffe1a99af", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", .compiledIdeal, [⟨"constructed-participant", "sha256:ea0efdd843435f477577106f7c7bcb9df6b2a19067491b95530c5cc154875bcd"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 2) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .retained "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071" 0 "public_sum"
  accept := ⟨true, 0, 1, []⟩
  quantity := .charged [("reduce.challenge", (.binary .div (.natural 1) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))])))]
  capabilities := []
}

def request1Method : Option Wire.Application := some ⟨⟨"fs.keyed_charged", 0⟩, []⟩

claim_request request1Data using ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessRegistration.library method request1Method

end ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessClaims
