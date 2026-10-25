module

public import ZkcSecurity.Tools.ClaimConstruction
public import ZkcArkLib.Examples.Subjects.Sumcheck.Endpoints
public import ZkcArkLib.Examples.Subjects.Sumcheck.Registration
public meta import ZkcArkLib.Examples.Subjects.Sumcheck.Registration

@[expose] public section

/-! Generated source requests and typed receipts. Regenerate with `lean/bridges/subject.py --write`. Maintained Endpoints are independent regression clients, never source claim authority. -/

namespace ZkcSecurity.Examples.Subjects.Sumcheck
open Zkc.Claims ZkcSecurity.Tools.ClaimConstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact source request; attachment and method are separate. -/
def request0Data : Wire.Request :=
{
  subject := ⟨"sha256:e3ae53d4706b17e7f5a468996a1dbf8cc57a06576986392388b288fffe1a99af", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", .executableBytes, [⟨"constructed-participant", "sha256:d8e195b77fb6d88b6a4ae35e1417cdca9432b8b5a3c683e4bf23445436168d78"⟩, ⟨"verifier-program", "sha256:9c11f210ff0771b8a692e9b1af11dd52bf4d8932928058a0339475c8b57039c0"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.bytes")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 2) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .retained "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071" 0 "public_sum"
  accept := ⟨true, 0, 1, []⟩
  quantity := .scalar (.binary .div (.binary .add (.reference "Q") (.natural 2)) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))
  capabilities := []
}

def request0Method : Option Wire.Application := some ⟨⟨"fs.keyed_soundness", 0⟩, []⟩

claim_request request0Data using Registration.library method request0Method

/-- Exact source request; attachment and method are separate. -/
def request1Data : Wire.Request :=
{
  subject := ⟨"sha256:e3ae53d4706b17e7f5a468996a1dbf8cc57a06576986392388b288fffe1a99af", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", .compiledIdeal, [⟨"constructed-participant", "sha256:d8e195b77fb6d88b6a4ae35e1417cdca9432b8b5a3c683e4bf23445436168d78"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 2) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .retained "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071" 0 "public_sum"
  accept := ⟨true, 0, 1, []⟩
  quantity := .scalar (.binary .div (.binary .add (.reference "Q") (.natural 2)) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))
  capabilities := []
}

def request1Method : Option Wire.Application := some ⟨⟨"fs.keyed_soundness", 0⟩, []⟩

claim_request request1Data using Registration.library method request1Method

/-- Exact source request; attachment and method are separate. -/
def request2Data : Wire.Request :=
{
  subject := ⟨"sha256:e3ae53d4706b17e7f5a468996a1dbf8cc57a06576986392388b288fffe1a99af", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", .compiledIdeal, [⟨"constructed-participant", "sha256:d8e195b77fb6d88b6a4ae35e1417cdca9432b8b5a3c683e4bf23445436168d78"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 2) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .retained "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071" 0 "public_sum"
  accept := ⟨true, 0, 1, []⟩
  quantity := .charged [("reduce.challenge", (.binary .div (.natural 1) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))])))]
  capabilities := []
}

def request2Method : Option Wire.Application := some ⟨⟨"fs.keyed_charged", 0⟩, []⟩

claim_request request2Data using Registration.library method request2Method

end ZkcSecurity.Examples.Subjects.Sumcheck
