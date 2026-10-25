module

public import ZkcSecurity.Tools.ClaimConstruction
public import ZkcSecurity.Examples.Subjects.Okamoto.Endpoints
public import ZkcSecurity.Examples.Subjects.Okamoto.Registration
public meta import ZkcSecurity.Examples.Subjects.Okamoto.Registration

@[expose] public section

/-! Generated source requests and typed receipts. Regenerate with `lean/bridges/subject.py --write`. Maintained Endpoints are independent regression clients, never source claim authority. -/

namespace ZkcSecurity.Examples.Subjects.Okamoto
open Zkc.Claims ZkcSecurity.Tools.ClaimConstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact source request; attachment and method are separate. -/
def request0Data : Wire.Request :=
{
  subject := ⟨"sha256:440eb60d922d4c53048d7ff1b38ba4e90dfd040306892f4cf1b638b77ca73eaf", "zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec", .compiledIdeal, [⟨"constructed-participant", "sha256:0370515aeeb176fb01c9de55d9d9b992547122a15f6395125f2b5332c093da1c"⟩]⟩
  property := ⟨"knowledge", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.fixed")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q"))]⟩
  target := .retained "zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec" 0 "knowledge"
  accept := ⟨true, 0, 1, []⟩
  quantity := .guarantee ⟨⟨"guarantees.forking", 0⟩, [(some "challenges", (.application "cardinality" none [(none, (.reference "bls12-381.fr"))])), (some "cost", (.application "prover_runs" none [(none, (.natural 2))]))]⟩
  capabilities := []
}

def request0Method : Option Wire.Application := some ⟨⟨"fs.forking", 0⟩, []⟩

claim_request request0Data using Registration.library method request0Method

end ZkcSecurity.Examples.Subjects.Okamoto
