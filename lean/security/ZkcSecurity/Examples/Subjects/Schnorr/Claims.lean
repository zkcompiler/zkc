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
  subject := ⟨"sha256:7c4214ba8b6291c17f70289eda113d07b9d5a25c95aa1e3e9e1986189559364e", "example::Proof", .executableBytes, [⟨"constructed-participant", "sha256:36dccac628aefe119573db7e210b1f3a367e5eb7b86cc9718bfb742d7302662d"⟩, ⟨"verifier-program", "sha256:d44ad7e97f8d8ff5f80b6a18a546477181119c5aecef841cc9324683f8cb8b51"⟩]⟩
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
  subject := ⟨"sha256:7c4214ba8b6291c17f70289eda113d07b9d5a25c95aa1e3e9e1986189559364e", "example::Proof", .compiledIdeal, [⟨"constructed-participant", "sha256:36dccac628aefe119573db7e210b1f3a367e5eb7b86cc9718bfb742d7302662d"⟩]⟩
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
  subject := ⟨"sha256:7c4214ba8b6291c17f70289eda113d07b9d5a25c95aa1e3e9e1986189559364e", "example::Proof", .compiledIdeal, [⟨"constructed-participant", "sha256:36dccac628aefe119573db7e210b1f3a367e5eb7b86cc9718bfb742d7302662d"⟩]⟩
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
  subject := ⟨"sha256:7c4214ba8b6291c17f70289eda113d07b9d5a25c95aa1e3e9e1986189559364e", "example::Proof", .compiledIdeal, [⟨"constructed-participant", "sha256:36dccac628aefe119573db7e210b1f3a367e5eb7b86cc9718bfb742d7302662d"⟩]⟩
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
  subject := ⟨"sha256:f2c94c4ba120d711b25be07006417f56ca1f933eac20612b1551162a98c3d0bc", "schnorr::Schnorr::run_412d98bf3e90929028ee7f3d81dd5f4f39dbad1a68dc1f3abf34b5db43dee23a", .interactive, []⟩
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
  subject := ⟨"sha256:f2c94c4ba120d711b25be07006417f56ca1f933eac20612b1551162a98c3d0bc", "schnorr::Schnorr::run_412d98bf3e90929028ee7f3d81dd5f4f39dbad1a68dc1f3abf34b5db43dee23a", .interactive, []⟩
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
