module

public import ZkcSecurityTools.ClaimConstruction
public import ZkcSecurityExamples.Gkr.Generated.SubjectSoundnessRegistration
public meta import ZkcSecurityExamples.Gkr.Generated.SubjectSoundnessRegistration

@[expose] public section

/-! Generated source requests and typed receipts. Regenerate with `lean/bridges/subject.py --write`. Typed library exports fix the subject and registry; source requests select the property and method. -/

namespace ZkcSecurity.Realizations.Gkr.Generated.SubjectSoundnessClaims
open Zkc.Claims ZkcSecurity.Tools.ClaimConstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact source request; attachment and method are separate. -/
def request0Data : Wire.Request :=
{
  subject := ⟨"sha256:56939f44b7084b9a929d7858dd0f5d85ef15d5486befff392fa0eab76f3eb756", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", .compiledIdeal, [⟨"constructed-participant", "sha256:73a70bb859999c94d1bdcb74b5e8ed9e2369ae9449182277ae5c49e64ecabaec"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 160) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .retained "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" 1 "circuit_outputs"
  accept := ⟨true, 0, 1, []⟩
  quantity := .scalar (.binary .div (.binary .mul (.natural 4) (.binary .add (.reference "Q") (.natural 40))) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))
  capabilities := []
}

def request0Method : Option Wire.Application := some ⟨⟨"fs.keyed_soundness", 0⟩, []⟩

claim_request request0Data using ZkcSecurity.Realizations.Gkr.Generated.SubjectSoundnessRegistration.library method request0Method

/-- Exact source request; attachment and method are separate. -/
def request1Data : Wire.Request :=
{
  subject := ⟨"sha256:56939f44b7084b9a929d7858dd0f5d85ef15d5486befff392fa0eab76f3eb756", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", .compiledIdeal, [⟨"constructed-participant", "sha256:73a70bb859999c94d1bdcb74b5e8ed9e2369ae9449182277ae5c49e64ecabaec"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 160) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .retained "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" 1 "circuit_outputs"
  accept := ⟨true, 0, 1, []⟩
  quantity := .charged [("output", (.binary .div (.natural 4) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), ("left.challenge", (.binary .div (.natural 4) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), ("right.challenge", (.binary .div (.natural 4) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), ("line_challenge", (.binary .div (.natural 4) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))])))]
  capabilities := []
}

def request1Method : Option Wire.Application := some ⟨⟨"fs.keyed_charged", 0⟩, []⟩

claim_request request1Data using ZkcSecurity.Realizations.Gkr.Generated.SubjectSoundnessRegistration.library method request1Method

end ZkcSecurity.Realizations.Gkr.Generated.SubjectSoundnessClaims
