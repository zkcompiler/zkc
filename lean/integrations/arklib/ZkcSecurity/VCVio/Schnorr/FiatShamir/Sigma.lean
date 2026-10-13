module

public import Zkc.Protocols.Schnorr.Common
public import VCVio.CryptoFoundations.FiatShamir.Sigma.KnowledgeExtraction

@[expose] public section

/-! Algebraic Schnorr adapter for the pinned VCVio Sigma extraction interface.
The extractor reuses zkc's existing two-response special-soundness theorem.
-/
namespace ZkcSecurity.VCVio.Schnorr.FiatShamir
open OracleComp OracleSpec Zkc.Protocols.Schnorr.Common

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq G] [SampleableType F]

def relation (base key : G) (witness : F) : Bool := decide (witness • base = key)

def sigma (base : G) : SigmaProtocol G F G F F F (relation base) where
  commit _ _ := do
    let nonce ← $ᵗ F
    pure (nonce • base, nonce)
  respond _ witness nonce challenge := pure (nonce + challenge * witness)
  verify key commitment challenge response :=
    decide (response • base = commitment + challenge • key)
  sim _ := do
    let nonce ← $ᵗ F
    pure (nonce • base)
  extract first responseFirst second responseSecond :=
    pure ((responseFirst - responseSecond) / (first - second))

theorem speciallySound (base : G) : (sigma (F := F) base).SpeciallySound := by
  intro key commitment first second responseFirst responseSecond distinct acceptFirst acceptSecond
    witness supported
  have witness_eq : witness = (responseFirst - responseSecond) / (first - second) := by
    simpa [sigma] using supported
  subst witness
  have first_eq : responseFirst • base = commitment + first • key := by
    simpa [sigma] using acceptFirst
  have second_eq : responseSecond • base = commitment + second • key := by
    simpa [sigma] using acceptSecond
  simpa [relation] using Zkc.Protocols.Schnorr.extract_public_key base key commitment
    first second responseFirst responseSecond distinct first_eq second_eq

/-- A witness/statement generator, with no hardness or efficiency claim. -/
def generable (base : G) : GenerableRelation G F (relation base) where
  gen := do let witness ← $ᵗ F; pure (witness • base, witness)
  gen_sound := by
    intro key witness supported
    simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨w, _, same⟩ := supported
    cases same
    simp [relation]

theorem actualVerifier_accepts_iff {wiring : Wiring} {program : Verifier F G}
    (certificate : VerifierContract wiring program) (base key commitment : G)
    (challenge response : F) (service : Nat) :
    (run program base key service ⟨commitment, fun _ => response⟩ challenge).outcome =
      .returned (some true) ↔
        (sigma base).verify key commitment challenge response = true := by
  rw [certificate.accepted_iff]
  simp [sigma]

end ZkcSecurity.VCVio.Schnorr.FiatShamir
