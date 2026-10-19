module

public import ZkcExamples.Structured.SigmaLogicalContexts
public import Examples.Schnorr.SigmaProtocol
public import VCVio.CryptoFoundations.FiatShamir.Sigma.KnowledgeExtraction

@[expose] public section

/-! The imported Chaum–Pedersen verifier as VCVio's Schnorr Σ-protocol over the
product module `G × G`, and its Fiat–Shamir transform.

One witness, one nonce and one response at two bases are Schnorr at the base
pair: `response • (first, second) = commitment + challenge • (firstKey,
secondKey)` is exactly the two checked equations. Completeness, special
soundness and perfect HVZK are therefore the pinned upstream theorems, with no
new protocol mathematics; the shared witness is the product's single scalar.
Its prover algorithms are VCVio's; `prover_sends` shows that, for every nonce
and challenge, the values the admitted prover sends are possible outputs of
those algorithms, so completeness and HVZK concern VCVio's uniform-nonce prover.
Knowledge soundness of the Fiat–Shamir transform comes from VCVio's replay
extractor and is stated for the retained `DLogEquality` formula, which
`SigmaLogicalContexts.shared_iff` equates with the shared logical context at the
observed boundary of every actual verifier run. -/

namespace ZkcSecurity.Examples.ChaumPedersenSigma
open OracleComp OracleSpec
open ZkcExamples.Structured

set_option smartUnfolding false

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The actual verifier's selected decision on one transcript. -/
def decision (firstBase secondBase : G) (service : Nat) (keys : G × G) (commitments : G × G)
    (challenge response : F) : Bool :=
  decide (ChaumPedersenBinding.decisionSelector.read {} (ChaumPedersenBinding.observedBoundary firstBase
    keys.1 secondBase keys.2 service commitments challenge response) = some true)

/-- The decision is the Schnorr equation at the base pair. -/
theorem decision_eq (firstBase secondBase : G) (service : Nat) (keys : G × G) (commitments : G × G)
    (challenge response : F) :
    decision firstBase secondBase service keys commitments challenge response =
      decide (response • (firstBase, secondBase) = commitments + challenge • keys) := by
  rw [decision, decide_eq_decide]
  rw [ChaumPedersenBinding.observed_accepts_iff]
  simp [Prod.ext_iff]

/-- The retained formula is Schnorr's relation at the base pair. -/
theorem relation_eq (firstBase firstKey secondBase secondKey : G) (witness : F) :
    ChaumPedersenBinding.Relation firstBase firstKey secondBase secondKey witness ↔
      decide (witness • (firstBase, secondBase) = (firstKey, secondKey)) = true := by
  rw [ChaumPedersenBinding.relation_iff]
  simp only [decide_eq_true_eq, Prod.smul_mk, Prod.mk.injEq]
  exact ⟨fun ⟨first, second⟩ => ⟨first.symm, second.symm⟩,
    fun ⟨first, second⟩ => ⟨first.symm, second.symm⟩⟩

variable [SampleableType F] [SampleableType G]

/-- Schnorr at the base pair, with the actual verifier's decision. -/
def sigma (firstBase secondBase : G) (service : Nat) :
    SigmaProtocol (G × G) F (G × G) F F F (fun keys witness => decide (witness • (firstBase, secondBase) = keys)) where
  commit := (_root_.Schnorr.sigma F (G × G) (firstBase, secondBase)).commit
  respond := (_root_.Schnorr.sigma F (G × G) (firstBase, secondBase)).respond
  verify := decision firstBase secondBase service
  sim := (_root_.Schnorr.sigma F (G × G) (firstBase, secondBase)).sim
  extract := (_root_.Schnorr.sigma F (G × G) (firstBase, secondBase)).extract

theorem sigma_eq (firstBase secondBase : G) (service : Nat) :
    sigma (F := F) firstBase secondBase service = _root_.Schnorr.sigma F (G × G) (firstBase, secondBase) := by
  have decisions : decision (F := F) firstBase secondBase service =
      (_root_.Schnorr.sigma F (G × G) (firstBase, secondBase)).verify := by
    funext keys commitments challenge response
    rw [decision_eq]
    rfl
  unfold sigma
  rw [decisions]

/-- The pair's prover draws one nonce and answers with one response: the values
the admitted prover sends at both bases. -/
theorem prover_sends (firstBase firstKey secondBase secondKey : G) (witness : F)
    (service nonceService : Nat) (nonce challenge : F) :
    ((nonce • firstBase, nonce • secondBase), nonce) ∈
        support ((sigma (F := F) firstBase secondBase service).commit (firstKey, secondKey) witness) ∧
      nonce + challenge * witness ∈
        support ((sigma (F := F) firstBase secondBase service).respond (firstKey, secondKey) witness
          nonce challenge) ∧
      (ChaumPedersen.nonces nonce challenge).run
          (ChaumPedersenViews.program.participant F G 0 (ChaumPedersen.proverInputs firstBase firstKey
            secondBase secondKey witness nonceService)) =
        ⟨.returned (.cons none .nil), (),
          [.query ChaumPedersen.nonceSite Zkc.Source.Structured.scalarDomain (.cons nonceService .nil),
           .send (ty := .group Zkc.Source.Structured.groupDomain) ChaumPedersen.firstCommitmentSite 1
             (nonce • firstBase),
           .send (ty := .group Zkc.Source.Structured.groupDomain) ChaumPedersen.secondCommitmentSite 1
             (nonce • secondBase),
           .receive (.field Zkc.Source.Structured.scalarDomain) ChaumPedersen.deliverySite 1,
           .send (ty := .field Zkc.Source.Structured.scalarDomain) ChaumPedersen.responseSite 1
             (nonce + challenge * witness)]⟩ := by
  refine ⟨?_, ?_, ChaumPedersen.prover_run ..⟩
  · simp [sigma, _root_.Schnorr.sigma]
  · simp [sigma, _root_.Schnorr.sigma]

theorem complete (firstBase secondBase : G) (service : Nat) :
    (sigma (F := F) firstBase secondBase service).PerfectlyComplete := by
  rw [sigma_eq]
  exact _root_.Schnorr.sigma_complete F (G × G) (firstBase, secondBase)

theorem speciallySound (firstBase secondBase : G) (service : Nat) :
    (sigma (F := F) firstBase secondBase service).SpeciallySound := by
  rw [sigma_eq]
  exact _root_.Schnorr.sigma_speciallySound F (G × G) (firstBase, secondBase)

theorem hvzk [Finite F] (firstBase secondBase : G) (service : Nat) :
    (sigma (F := F) firstBase secondBase service).PerfectHVZK
      (_root_.Schnorr.simTranscript F (G × G) (firstBase, secondBase)) := by
  rw [sigma_eq]
  exact _root_.Schnorr.sigma_hvzk F (G × G) (firstBase, secondBase)

/-! ### Fiat–Shamir -/

/-- A statement/witness generator required by the transform's signature. It
carries no hardness or efficiency claim and plays no role in extraction. -/
def generable (firstBase secondBase : G) :
    GenerableRelation (G × G) F (fun keys witness => decide (witness • (firstBase, secondBase) = keys)) where
  gen := do
    let witness ← $ᵗ F
    pure (witness • (firstBase, secondBase), witness)
  gen_sound := by
    intro keys witness supported
    simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨sampled, _, same⟩ := supported
    cases same
    simp

variable [Fintype F] [Inhabited F]

/-- Knowledge soundness of the Fiat–Shamir transform of the imported
Chaum–Pedersen verifier, for a statement and context fixed before the prover
runs. The extracted scalar satisfies the retained `DLogEquality` formula: one
witness for both keys. -/
theorem knowledge_soundness (Message : Type) [DecidableEq Message] (firstBase secondBase : G)
    (service : Nat) (prover : _root_.FiatShamir.KnowledgeProver (G × G) (G × G) F F Message)
    (keys : G × G) (message : Message) (budget : Nat)
    (bounded : _root_.FiatShamir.nmaHashQueryBound (M := Message) (prover keys message) budget) :
    let acceptance := _root_.FiatShamir.knowledgeAcceptance
      (sigma (F := F) firstBase secondBase service) (generable firstBase secondBase) Message
      prover keys message
    acceptance * (acceptance / (budget + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← _root_.FiatShamir.knowledgeExtractor
          (sigma (F := F) firstBase secondBase service) (generable firstBase secondBase) Message
          prover message budget keys}[ChaumPedersenBinding.Relation firstBase keys.1 secondBase keys.2
            witness] := by
  have upstream := _root_.FiatShamir.knowledgeExtractor_success
    (sigma (F := F) firstBase secondBase service) (generable firstBase secondBase) Message
    (speciallySound firstBase secondBase service) prover keys message budget bounded
  simpa only [relation_eq] using upstream

end ZkcSecurity.Examples.ChaumPedersenSigma
