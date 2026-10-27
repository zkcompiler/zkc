module

public import ZkcSecurity.Tools.ClaimConstruction
public import ZkcSecurity.Examples.Subjects.Schnorr.Endpoints
public import ZkcSecurity.Examples.Subjects.Schnorr.Registration
public meta import ZkcSecurity.Examples.Subjects.Schnorr.Registration

@[expose] public section

/-! Generated source requests and typed receipts. Regenerate with `lean/bridges/subject.py --write`. Maintained Endpoints are independent regression clients, never source claim authority. -/

namespace ZkcSecurity.Examples.Subjects.Schnorr
open Zkc.Claims ZkcSecurity.Tools.ClaimConstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact source request; attachment and method are separate. -/
def request0Data : Wire.Request :=
{
  subject := ⟨"sha256:96e7911cc0127e0d751223fec8d3d4fb6f2b6f518f1fd884290251e35893be4a", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .executableBytes, [⟨"constructed-participant", "sha256:81f6400d41f8d2cf31323c0f8f248e8de498b261a98b32a44253eae3854bd87c"⟩, ⟨"verifier-program", "sha256:d01f7638470e602c4a35c0124282a71c88226b9a978d6792bd81a78d5ee08f2c"⟩]⟩
  property := ⟨"knowledge", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.bytes")), (some "statement", (.reference "statements.fixed")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q"))]⟩
  target := .retained "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad" 0 "knowledge"
  accept := ⟨true, 0, 1, []⟩
  quantity := .guarantee ⟨⟨"guarantees.forking", 0⟩, [(some "challenges", (.application "cardinality" none [(none, (.reference "bls12-381.fr"))])), (some "cost", (.application "prover_runs" none [(none, (.natural 2))]))]⟩
  capabilities := []
}

def request0Method : Option Wire.Application := some ⟨⟨"fs.forking", 0⟩, []⟩

claim_request request0Data using Registration.library method request0Method

/-- Exact source request; attachment and method are separate. -/
def request1Data : Wire.Request :=
{
  subject := ⟨"sha256:96e7911cc0127e0d751223fec8d3d4fb6f2b6f518f1fd884290251e35893be4a", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .compiledIdeal, [⟨"constructed-participant", "sha256:81f6400d41f8d2cf31323c0f8f248e8de498b261a98b32a44253eae3854bd87c"⟩]⟩
  property := ⟨"knowledge", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.fixed")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q"))]⟩
  target := .retained "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad" 0 "knowledge"
  accept := ⟨true, 0, 1, []⟩
  quantity := .guarantee ⟨⟨"guarantees.forking", 0⟩, [(some "challenges", (.application "cardinality" none [(none, (.reference "bls12-381.fr"))])), (some "cost", (.application "prover_runs" none [(none, (.natural 2))]))]⟩
  capabilities := []
}

def request1Method : Option Wire.Application := some ⟨⟨"fs.forking", 0⟩, []⟩

claim_request request1Data using Registration.library method request1Method

/-- Exact source request; attachment and method are separate. -/
def request2Data : Wire.Request :=
{
  subject := ⟨"sha256:96e7911cc0127e0d751223fec8d3d4fb6f2b6f518f1fd884290251e35893be4a", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .compiledIdeal, [⟨"constructed-participant", "sha256:81f6400d41f8d2cf31323c0f8f248e8de498b261a98b32a44253eae3854bd87c"⟩]⟩
  property := ⟨"user.view_equal", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.fixed")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q"))]⟩
  target := .retained "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad" 0 "knowledge"
  accept := ⟨true, 0, 1, []⟩
  quantity := .scalar (.natural 0)
  capabilities := []
}

def request2Method : Option Wire.Application := some ⟨⟨"user.view_theorem", 0⟩, []⟩

claim_request request2Data using Registration.library method request2Method

/-- Exact source request; attachment and method are separate. -/
def request3Data : Wire.Request :=
{
  subject := ⟨"sha256:96e7911cc0127e0d751223fec8d3d4fb6f2b6f518f1fd884290251e35893be4a", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .compiledIdeal, [⟨"constructed-participant", "sha256:81f6400d41f8d2cf31323c0f8f248e8de498b261a98b32a44253eae3854bd87c"⟩]⟩
  property := ⟨"user.view_equal", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.fixed")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q"))]⟩
  target := .retained "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad" 0 "knowledge"
  accept := ⟨true, 0, 1, []⟩
  quantity := .scalar (.natural 0)
  capabilities := []
}

def request3Method : Option Wire.Application := some ⟨⟨"user.view_derivation", 0⟩, []⟩

claim_request request3Data using Registration.library method request3Method

/-- Exact source request; attachment and method are separate. -/
def request4Data : Wire.Request :=
{
  subject := ⟨"sha256:21d6dd8665904f0b0b0faf43f057f61c2fae5b5b12f0191e40fd88bda8b72c2e", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .interactive, []⟩
  property := ⟨"completeness", 0⟩
  parameters := none
  model := ⟨⟨"models.interactive", 0⟩, []⟩
  target := .retained "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad" 0 "knowledge"
  accept := ⟨true, 0, 1, []⟩
  quantity := .guarantee ⟨⟨"guarantees.perfect", 0⟩, []⟩
  capabilities := []
}

def request4Method : Option Wire.Application := none

claim_request request4Data using Registration.library method request4Method

/-- Exact source request; attachment and method are separate. -/
def request5Data : Wire.Request :=
{
  subject := ⟨"sha256:21d6dd8665904f0b0b0faf43f057f61c2fae5b5b12f0191e40fd88bda8b72c2e", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .interactive, []⟩
  property := ⟨"special_soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.interactive", 0⟩, []⟩
  target := .retained "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad" 0 "knowledge"
  accept := ⟨true, 0, 1, []⟩
  quantity := .guarantee ⟨⟨"guarantees.special_soundness", 0⟩, [(some "challenges", (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))]⟩
  capabilities := []
}

def request5Method : Option Wire.Application := none

claim_request request5Data using Registration.library method request5Method

end ZkcSecurity.Examples.Subjects.Schnorr
