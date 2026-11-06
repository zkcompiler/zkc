module

public import ZkcSecurityExamples.Generated.TwoSumsSoundnessRegistration
public meta import ZkcSecurityExamples.Generated.TwoSumsSoundnessRegistration

@[expose] public section

/-! Generated exact source requests. Regenerate with `lean/checks/check_subject_roots.py --exports DIRECTORY --write`. The common data renderer emits no property or proof wrapper. -/

namespace ZkcSecurity.Examples.Generated.TwoSumsSoundnessClaims
open Zkc.Claims ZkcSecurity.Tools.ClaimConstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact source request; attachment and method are separate. -/
def request0Data : Wire.Request :=
{
  subject := ⟨"sha256:2a0351c54dc5de3d1b3cebb46e0172df3fff348683601797ad7fe58e349a2a96", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", .compiledIdeal, [⟨"constructed-participant", "sha256:106ab6342905e53d8ecd73b1c1c87a5cd176a2019840a04ae705c7595c53bbf6"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 8) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .retained "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d" 2 "public_sums"
  accept := ⟨true, 0, 1, []⟩
  quantity := .scalar (.binary .div (.binary .add (.reference "Q") (.natural 8)) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))
  capabilities := []
}

def request0Method : Option Wire.Application := some ⟨⟨"fs.keyed_soundness", 0⟩, []⟩

claim_request request0Data using ZkcSecurity.Examples.Generated.TwoSumsSoundnessRegistration.library method request0Method

/-- Exact source request; attachment and method are separate. -/
def request1Data : Wire.Request :=
{
  subject := ⟨"sha256:2a0351c54dc5de3d1b3cebb46e0172df3fff348683601797ad7fe58e349a2a96", "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d", .compiledIdeal, [⟨"constructed-participant", "sha256:106ab6342905e53d8ecd73b1c1c87a5cd176a2019840a04ae705c7595c53bbf6"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 8) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .retained "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d" 2 "public_sums"
  accept := ⟨true, 0, 1, []⟩
  quantity := .charged [("left.challenge", (.binary .div (.natural 1) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), ("right.challenge", (.binary .div (.natural 1) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))])))]
  capabilities := []
}

def request1Method : Option Wire.Application := some ⟨⟨"fs.keyed_charged", 0⟩, []⟩

claim_request request1Data using ZkcSecurity.Examples.Generated.TwoSumsSoundnessRegistration.library method request1Method

end ZkcSecurity.Examples.Generated.TwoSumsSoundnessClaims
