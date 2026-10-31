module

public import ZkcSecurityTools.ClaimConstruction
public import ZkcSecurityExamples.Subjects.Schnorr.Registration
public meta import ZkcSecurityExamples.Subjects.Schnorr.Registration

@[expose] public section

/-! Generated source requests and typed receipts. Regenerate with `lean/bridges/subject.py --write`. Typed library exports fix the subject and registry; source requests select the property and method. -/

namespace ZkcSecurity.Examples.Subjects.Schnorr
open Zkc.Claims ZkcSecurity.Tools.ClaimConstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact source request; attachment and method are separate. -/
def request0Data : Wire.Request :=
{
  subject := ⟨"sha256:0cbec0aa0f21d140a9cd26730a2c5a60b9b3dd2561a25939a885e66c3abc4065", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .executableBytes, [⟨"constructed-participant", "sha256:ff8b1b8df4735c08917191fc12272ecf05648514498bc8c8ede71647f44d16e4"⟩, ⟨"verifier-program", "sha256:d01f7638470e602c4a35c0124282a71c88226b9a978d6792bd81a78d5ee08f2c"⟩]⟩
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
  subject := ⟨"sha256:0cbec0aa0f21d140a9cd26730a2c5a60b9b3dd2561a25939a885e66c3abc4065", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .compiledIdeal, [⟨"constructed-participant", "sha256:ff8b1b8df4735c08917191fc12272ecf05648514498bc8c8ede71647f44d16e4"⟩]⟩
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
  subject := ⟨"sha256:0cbec0aa0f21d140a9cd26730a2c5a60b9b3dd2561a25939a885e66c3abc4065", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .compiledIdeal, [⟨"constructed-participant", "sha256:ff8b1b8df4735c08917191fc12272ecf05648514498bc8c8ede71647f44d16e4"⟩]⟩
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
  subject := ⟨"sha256:0cbec0aa0f21d140a9cd26730a2c5a60b9b3dd2561a25939a885e66c3abc4065", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .compiledIdeal, [⟨"constructed-participant", "sha256:ff8b1b8df4735c08917191fc12272ecf05648514498bc8c8ede71647f44d16e4"⟩]⟩
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
  subject := ⟨"sha256:8d9ce2df85204c5452c1320612c96d84d567da2a526a89d776dcbe3909497561", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .interactive, []⟩
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
  subject := ⟨"sha256:8d9ce2df85204c5452c1320612c96d84d567da2a526a89d776dcbe3909497561", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .interactive, []⟩
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
