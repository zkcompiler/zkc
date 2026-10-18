module

public import ZkcSecurity.Examples.StructuredSchnorrSigma
public import VCVio.CryptoFoundations.FiatShamir.Sigma.KnowledgeExtraction

@[expose] public section

/-! Fiat–Shamir knowledge soundness of the actual imported Schnorr verifier.

The Sigma instance is `StructuredSchnorrSigma.sigma`: its verifier is the
decision observed at the admitted original-stage Interactive verifier's
returned boundary. VCVio's Fiat–Shamir transform hashes the context message
and the commitment with one random oracle shared by the prover and final
verification. VCVio's replay extractor then finds a witness of the authored
relation with the stated probability. The query budget counts every prover
oracle call, including repeated keys; the added one is final verification.

This theorem is about the Fiat–Shamir transform of the imported interactive
verifier. The compiled non-interactive verifier is treated separately in
`CompiledSchnorrFiatShamir`, through the transcript-construction rule and the
Proof Entry's own import; both reach VCVio's Schnorr Sigma protocol, here by
`sigma_eq`.
-/

namespace ZkcSecurity.Examples.StructuredSchnorrFiatShamir
open OracleComp OracleSpec
open ZkcExamples.Structured
open ZkcSecurity.Examples.StructuredSchnorrSigma

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [SampleableType G]

/-- A statement/witness generator, required by the transform's signature. It
carries no hardness or efficiency claim and plays no role in extraction. -/
def generable (base : G) :
    GenerableRelation G F (fun key witness => decide (witness • base = key)) where
  gen := do
    let witness ← $ᵗ F
    pure (witness • base, witness)
  gen_sound := by
    intro key witness supported
    simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨sampled, _, same⟩ := supported
    cases same
    simp

/-- The random-oracle computations of the transform with context `Message`. -/
abbrev Oracle (Message : Type) (F G : Type) := OracleComp (unifSpec + (Message × G →ₒ F))

/-- The Fiat–Shamir transform of the actual imported verifier. -/
abbrev transform (Message : Type) [DecidableEq Message] (base proverKey : G)
    (nonceService challengeService : Nat) :=
  _root_.FiatShamir (m := Oracle Message F G)
    (sigma (F := F) base proverKey nonceService challengeService) (generable base) Message

theorem speciallySound (base proverKey : G) (nonceService challengeService : Nat) :
    (sigma (F := F) base proverKey nonceService challengeService).SpeciallySound := by
  rw [sigma_eq]
  exact _root_.Schnorr.sigma_speciallySound F G base

/-- Final verification runs the imported verifier's observed decision on the
oracle's challenge for the context message and commitment. -/
theorem verify_eq (Message : Type) [DecidableEq Message] (base proverKey key : G)
    (nonceService challengeService : Nat) (message : Message) (proof : G × F) :
    (transform Message base proverKey nonceService challengeService).verify key message proof =
      ((HasQuery.query (spec := Message × G →ₒ F) (message, proof.1) : Oracle Message F G F) >>=
        fun challenge => pure (decision base key proof.1 challenge proof.2 challengeService)) := by
  rcases proof with ⟨commitment, response⟩
  simp only [_root_.FiatShamir, sigma]

variable [Fintype F] [Inhabited F]

/-- Knowledge soundness of the Fiat–Shamir transform of the actual imported
Schnorr verifier in the random-oracle model, for a statement and context fixed
before the prover runs. Subtraction is truncated in `ENNReal`. -/
theorem knowledge_soundness (Message : Type) [DecidableEq Message] (base proverKey : G)
    (nonceService challengeService : Nat)
    (prover : _root_.FiatShamir.KnowledgeProver G G F F Message) (key : G)
    (message : Message) (budget : Nat)
    (bounded : _root_.FiatShamir.nmaHashQueryBound (M := Message) (prover key message) budget) :
    let acceptance := _root_.FiatShamir.knowledgeAcceptance
      (sigma (F := F) base proverKey nonceService challengeService) (generable base) Message
      prover key message
    acceptance * (acceptance / (budget + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← _root_.FiatShamir.knowledgeExtractor
          (sigma (F := F) base proverKey nonceService challengeService) (generable base) Message
          prover message budget key}[SchnorrBinding.Relation base key witness] := by
  have upstream := _root_.FiatShamir.knowledgeExtractor_success
    (sigma (F := F) base proverKey nonceService challengeService) (generable base) Message
    (speciallySound base proverKey nonceService challengeService) prover key message budget bounded
  simpa only [relation_eq] using upstream

end ZkcSecurity.Examples.StructuredSchnorrFiatShamir
