module

public import ZkcSecurity.Examples.EmbeddingEqualityClaims
public meta import ZkcSecurity.Examples.EmbeddingEqualityClaims

@[expose] public section

/-! Constructor data from the actual frontend-bound source claim. The shared
binder checks the proof-alias/protocol association against the exact interface.
The common command resolves the canonical meaning before applying the proof. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace ZkcSecurity.Examples.EmbeddingEqualityClient
open Zkc.Claims ZkcSecurity.Claims
open ZkcSecurity.Examples.EmbeddingEqualityClaims

def idealData : Wire.Request := {
  subject := ⟨"sha256:198a275c8dc1a3b5e7ef78b30676d63ff0f07b151b292a0a486269b8bb0c15ea", "s7h6578616d706c6517h456d62656464696e67457175616c697479", .compiledIdeal, [⟨"constructed-participant", "sha256:51686b3d9ce3db7cf5e84aa1657cc0204fcbe9bd5c9666931b98423612bdc71b"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.fixed")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.natural 0))]⟩
  target := .retained "s7h6578616d706c6517h456d62656464696e67457175616c697479" 0 "equality"
  accept := ⟨true, 0, 1, []⟩
  quantity := .scalar (.natural 0)
  capabilities := []
}

theorem source_subject_matches : idealData.subject = subject.reference := rfl

/-- A raw frontend alias cannot substitute for the checked protocol association. -/
theorem unresolved_alias_refused : subject.check
    { idealData with subject := { idealData.subject with entry := "example::Proof" } } =
      .error .subjectMismatch := by
  decide +kernel

claim_request idealData using library method
  (some (⟨⟨"fs.keyed_soundness", 0⟩, []⟩ : Wire.Application))

#print axioms idealReceipt

end ZkcSecurity.Examples.EmbeddingEqualityClient
