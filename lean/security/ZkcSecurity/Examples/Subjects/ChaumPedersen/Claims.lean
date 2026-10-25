module

public import ZkcSecurity.Tools.ClaimConstruction
public import ZkcSecurity.Examples.Subjects.ChaumPedersen.Endpoints
public import ZkcSecurity.Examples.Subjects.ChaumPedersen.Registration
public meta import ZkcSecurity.Examples.Subjects.ChaumPedersen.Registration

@[expose] public section

/-! Generated source requests and typed receipts. Regenerate with `lean/bridges/subject.py --write`. Maintained Endpoints are independent regression clients, never source claim authority. -/

namespace ZkcSecurity.Examples.Subjects.ChaumPedersen
open Zkc.Claims ZkcSecurity.Tools.ClaimConstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact source request; attachment and method are separate. -/
def request0Data : Wire.Request :=
{
  subject := ⟨"sha256:ef66cde675242086d335705bc59d7a70c4ae41771627cc6e4575a7134651aa6a", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", .compiledIdeal, [⟨"constructed-participant", "sha256:d879047e4d385d5b4ab40c20173504580352826f5a2f0dadf807ab8d56be5eb8"⟩]⟩
  property := ⟨"knowledge", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.fixed")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q"))]⟩
  target := .retained "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111" 0 "knowledge"
  accept := ⟨true, 0, 1, []⟩
  quantity := .guarantee ⟨⟨"guarantees.forking", 0⟩, [(some "challenges", (.application "cardinality" none [(none, (.reference "bls12-381.fr"))])), (some "cost", (.application "prover_runs" none [(none, (.natural 2))]))]⟩
  capabilities := []
}

def request0Method : Option Wire.Application := some ⟨⟨"fs.forking", 0⟩, []⟩

claim_request request0Data using Registration.library method request0Method

end ZkcSecurity.Examples.Subjects.ChaumPedersen
