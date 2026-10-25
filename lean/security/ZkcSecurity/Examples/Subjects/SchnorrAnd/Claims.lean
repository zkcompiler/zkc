module

public import ZkcSecurity.Tools.ClaimConstruction
public import ZkcSecurity.Examples.Subjects.SchnorrAnd.Endpoints
public import ZkcSecurity.Examples.Subjects.SchnorrAnd.Registration
public meta import ZkcSecurity.Examples.Subjects.SchnorrAnd.Registration

@[expose] public section

/-! Generated source requests and typed receipts. Regenerate with `lean/bridges/subject.py --write`. Maintained Endpoints are independent regression clients, never source claim authority. -/

namespace ZkcSecurity.Examples.Subjects.SchnorrAnd
open Zkc.Claims ZkcSecurity.Tools.ClaimConstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact source request; attachment and method are separate. -/
def request0Data : Wire.Request :=
{
  subject := ⟨"sha256:38886e48c95e08ed0368765f6c4e3b6b8a8927007ad5a3781ecf11d436abf420", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", .compiledIdeal, [⟨"constructed-participant", "sha256:20c88621b68939166296bc2930e1bea4e09639256324390f09af8c4e4e8a983a"⟩]⟩
  property := ⟨"knowledge", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.fixed")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q"))]⟩
  target := .retained "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c" 0 "knowledge"
  accept := ⟨true, 0, 1, []⟩
  quantity := .guarantee ⟨⟨"guarantees.forking", 0⟩, [(some "challenges", (.application "cardinality" none [(none, (.reference "bls12-381.fr"))])), (some "cost", (.application "prover_runs" none [(none, (.natural 2))]))]⟩
  capabilities := []
}

def request0Method : Option Wire.Application := some ⟨⟨"fs.forking", 0⟩, []⟩

claim_request request0Data using Registration.library method request0Method

end ZkcSecurity.Examples.Subjects.SchnorrAnd
