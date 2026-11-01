module

public import ZkcSecurityTools.ClaimConstruction
public import ZkcSecurityExamples.Subjects.SchnorrAnd.Registration
public meta import ZkcSecurityExamples.Subjects.SchnorrAnd.Registration

@[expose] public section

/-! Generated source requests and typed receipts. Regenerate with `lean/bridges/subject.py --write`. Typed library exports fix the subject and registry; source requests select the property and method. -/

namespace ZkcSecurity.Examples.Subjects.SchnorrAnd
open Zkc.Claims ZkcSecurity.Tools.ClaimConstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact source request; attachment and method are separate. -/
def request0Data : Wire.Request :=
{
  subject := ⟨"sha256:33847b80067c89544c7de4e20fc9fac580efd7210c59ba32df3a0390396ff149", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", .compiledIdeal, [⟨"constructed-participant", "sha256:8d97e5ae6bbe741cfd8f580e7bc70240111416e5114ad3ed080fbb48b5515fb2"⟩]⟩
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
