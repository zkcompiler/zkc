module

public import ZkcSecurity.Tools.ClaimConstruction
public import ZkcArkLib.Examples.Subjects.Guess.Endpoints
public import ZkcArkLib.Examples.Subjects.Guess.Registration
public meta import ZkcArkLib.Examples.Subjects.Guess.Registration

@[expose] public section

/-! Generated source requests and typed receipts. Regenerate with `lean/bridges/subject.py --write`. Maintained Endpoints are independent regression clients, never source claim authority. -/

namespace ZkcSecurity.Examples.Subjects.Guess
open Zkc.Claims ZkcSecurity.Tools.ClaimConstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact source request; attachment and method are separate. -/
def request0Data : Wire.Request :=
{
  subject := ⟨"sha256:2d6581776370c9e834d35c333ac1287a112e6b791fef5bd1b46a7cbf9515bbed", "zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", .compiledIdeal, [⟨"constructed-participant", "sha256:58627dd075b34a1f236b8ff703a18631ce9868dd376ebcaf059c2b54896e1e0e"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 1) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .importedLanguage "zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748" ⟨⟨"languages.guess", 0⟩, []⟩
  accept := ⟨true, 0, 1, []⟩
  quantity := .scalar (.binary .div (.binary .add (.reference "Q") (.natural 1)) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))
  capabilities := []
}

def request0Method : Option Wire.Application := some ⟨⟨"fs.keyed_soundness", 0⟩, []⟩

claim_request request0Data using Registration.library method request0Method

/-- Exact source request; attachment and method are separate. -/
def request1Data : Wire.Request :=
{
  subject := ⟨"sha256:2d6581776370c9e834d35c333ac1287a112e6b791fef5bd1b46a7cbf9515bbed", "zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", .compiledIdeal, [⟨"constructed-participant", "sha256:58627dd075b34a1f236b8ff703a18631ce9868dd376ebcaf059c2b54896e1e0e"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 1) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .importedLanguage "zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748" ⟨⟨"languages.guess", 0⟩, []⟩
  accept := ⟨true, 0, 1, []⟩
  quantity := .charged [("challenge", (.binary .div (.natural 1) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))])))]
  capabilities := []
}

def request1Method : Option Wire.Application := some ⟨⟨"fs.keyed_charged", 0⟩, []⟩

claim_request request1Data using Registration.library method request1Method

end ZkcSecurity.Examples.Subjects.Guess
