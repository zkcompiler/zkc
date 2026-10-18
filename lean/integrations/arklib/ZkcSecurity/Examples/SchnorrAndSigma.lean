module

public import ZkcExamples.Structured.SigmaLogicalContexts
public import ZkcSecurity.VCVio.SigmaAndSchnorr
public import VCVio.CryptoFoundations.FiatShamir.Sigma.KnowledgeExtraction

@[expose] public section

/-! The imported Schnorr AND verifier as the shared-challenge composition of two
VCVio Schnorr Σ-protocols, and its Fiat–Shamir transform.

The Σ-protocol's verifier is the decision observed at the admitted
original-stage verifier's returned boundary on one transcript. Its prover
algorithms are VCVio's; `prover_sends` shows that, for every nonce pair and
challenge, the values the admitted prover sends are possible outputs of those
algorithms. Completeness and HVZK therefore concern VCVio's uniform-nonce
prover; the admitted prover's own randomness is not modeled. Completeness,
special soundness and perfect HVZK come from the generic composition; knowledge
soundness of the Fiat–Shamir transform comes from VCVio's replay extractor and
is stated for the retained `DLogPair` formula, which
`SigmaLogicalContexts.independent_iff` equates with the independent logical
context at the observed boundary of every actual verifier run. -/

namespace ZkcSecurity.Examples.SchnorrAndSigma
open OracleComp OracleSpec
open ZkcExamples.Structured
open ZkcSecurity.VCVio ZkcSecurity.VCVio.SigmaAnd

set_option smartUnfolding false

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The actual verifier's selected decision on one transcript. -/
def decision (firstBase secondBase : G) (service : Nat) (keys : G × G) (commitments : G × G)
    (challenge : F) (responses : F × F) : Bool :=
  decide (SchnorrAndBinding.decisionSelector.read {} (SchnorrAndBinding.observedBoundary firstBase keys.1
    secondBase keys.2 service commitments challenge responses) = some true)

theorem decision_eq (firstBase secondBase : G) (service : Nat) (keys : G × G) (commitments : G × G)
    (challenge : F) (responses : F × F) :
    decision firstBase secondBase service keys commitments challenge responses =
      (decide (responses.1 • firstBase = commitments.1 + challenge • keys.1) &&
        decide (responses.2 • secondBase = commitments.2 + challenge • keys.2)) := by
  rw [decision, decide_eq_decide.mpr (SchnorrAndBinding.observed_accepts_iff ..), Bool.decide_and]

/-- Each component relation of the composition, normalized against the retained formula. -/
theorem relation_eq (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F) :
    SchnorrAndBinding.Relation firstBase firstKey secondBase secondKey firstWitness secondWitness ↔
      andRelation (fun key witness => decide (witness • firstBase = key))
        (fun key witness => decide (witness • secondBase = key)) (firstKey, secondKey)
        (firstWitness, secondWitness) = true := by
  rw [SchnorrAndBinding.relation_iff]
  simp only [andRelation, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨first, second⟩ => ⟨first.symm, second.symm⟩,
    fun ⟨first, second⟩ => ⟨first.symm, second.symm⟩⟩

variable [SampleableType F] [SampleableType G]

/-- The composition with the actual verifier's decision. -/
def sigma (firstBase secondBase : G) (service : Nat) :
    SigmaProtocol (G × G) (F × F) (G × G) (F × F) F (F × F)
      (andRelation (fun key witness => decide (witness • firstBase = key))
        (fun key witness => decide (witness • secondBase = key))) where
  commit := (SigmaAndSchnorr.sigma F G firstBase secondBase).commit
  respond := (SigmaAndSchnorr.sigma F G firstBase secondBase).respond
  verify := decision firstBase secondBase service
  sim := (SigmaAndSchnorr.sigma F G firstBase secondBase).sim
  extract := (SigmaAndSchnorr.sigma F G firstBase secondBase).extract

/-- Equality of the decision coordinate discharges the composed interface. -/
theorem sigma_eq (firstBase secondBase : G) (service : Nat) :
    sigma (F := F) firstBase secondBase service = SigmaAndSchnorr.sigma F G firstBase secondBase := by
  have decisions : decision (F := F) firstBase secondBase service =
      (SigmaAndSchnorr.sigma F G firstBase secondBase).verify := by
    funext keys commitments challenge responses
    rw [decision_eq]
    rfl
  unfold sigma
  rw [decisions]

/-- The composition's prover draws one nonce per statement and answers one
challenge in both components: the values the admitted prover sends. -/
theorem prover_sends (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F)
    (service nonceService : Nat) (firstNonce secondNonce challenge : F) :
    ((firstNonce • firstBase, secondNonce • secondBase), (firstNonce, secondNonce)) ∈
        support ((sigma (F := F) firstBase secondBase service).commit (firstKey, secondKey)
          (firstWitness, secondWitness)) ∧
      (firstNonce + challenge * firstWitness, secondNonce + challenge * secondWitness) ∈
        support ((sigma (F := F) firstBase secondBase service).respond (firstKey, secondKey)
          (firstWitness, secondWitness) (firstNonce, secondNonce) challenge) ∧
      (SchnorrAnd.nonces firstNonce secondNonce challenge).run
          (SchnorrAndViews.program.participant F G 0 (SchnorrAnd.proverInputs firstBase firstKey
            secondBase secondKey firstWitness secondWitness nonceService)) =
        ⟨.returned (.cons none .nil), (),
          [.query SchnorrAnd.firstNonceSite Zkc.Source.Structured.scalarDomain (.cons nonceService .nil),
           .query SchnorrAnd.secondNonceSite Zkc.Source.Structured.scalarDomain (.cons nonceService .nil),
           .send (ty := .group Zkc.Source.Structured.groupDomain) SchnorrAnd.firstCommitmentSite 1
             (firstNonce • firstBase),
           .send (ty := .group Zkc.Source.Structured.groupDomain) SchnorrAnd.secondCommitmentSite 1
             (secondNonce • secondBase),
           .receive (.field Zkc.Source.Structured.scalarDomain) SchnorrAnd.deliverySite 1,
           .send (ty := .field Zkc.Source.Structured.scalarDomain) SchnorrAnd.firstResponseSite 1
             (firstNonce + challenge * firstWitness),
           .send (ty := .field Zkc.Source.Structured.scalarDomain) SchnorrAnd.secondResponseSite 1
             (secondNonce + challenge * secondWitness)]⟩ := by
  refine ⟨?_, ?_, SchnorrAnd.prover_run ..⟩
  · simp [sigma, SigmaAnd.and, _root_.Schnorr.sigma]
  · simp [sigma, SigmaAnd.and, _root_.Schnorr.sigma]

theorem complete (firstBase secondBase : G) (service : Nat) :
    (sigma (F := F) firstBase secondBase service).PerfectlyComplete := by
  rw [sigma_eq]
  exact SigmaAndSchnorr.complete F G firstBase secondBase

theorem speciallySound (firstBase secondBase : G) (service : Nat) :
    (sigma (F := F) firstBase secondBase service).SpeciallySound := by
  rw [sigma_eq]
  exact SigmaAndSchnorr.speciallySound F G firstBase secondBase

theorem hvzk [Fintype F] (firstBase secondBase : G) (service : Nat) :
    (sigma (F := F) firstBase secondBase service).PerfectHVZK (challengeFirst
      (simulateAnd (SigmaAndSchnorr.simulate F G firstBase) (SigmaAndSchnorr.simulate F G secondBase))) := by
  rw [sigma_eq]
  exact SigmaAndSchnorr.hvzk F G firstBase secondBase

/-! ### Fiat–Shamir -/

/-- A statement/witness generator required by the transform's signature. It
carries no hardness or efficiency claim and plays no role in extraction. -/
def generable (firstBase secondBase : G) :
    GenerableRelation (G × G) (F × F) (andRelation (fun key witness => decide (witness • firstBase = key))
      (fun key witness => decide (witness • secondBase = key))) where
  gen := do
    let firstWitness ← $ᵗ F
    let secondWitness ← $ᵗ F
    pure ((firstWitness • firstBase, secondWitness • secondBase), (firstWitness, secondWitness))
  gen_sound := by
    intro keys witnesses supported
    simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨firstWitness, _, secondWitness, _, same⟩ := supported
    cases same
    simp [andRelation]

variable [Fintype F] [Inhabited F]

/-- Knowledge soundness of the Fiat–Shamir transform of the imported AND
verifier, for a statement and context fixed before the prover runs. The
extracted pair satisfies the retained `DLogPair` formula. -/
theorem knowledge_soundness (Message : Type) [DecidableEq Message] (firstBase secondBase : G)
    (service : Nat) (prover : _root_.FiatShamir.KnowledgeProver (G × G) (G × G) F (F × F) Message)
    (keys : G × G) (message : Message) (budget : Nat)
    (bounded : _root_.FiatShamir.nmaHashQueryBound (M := Message) (prover keys message) budget) :
    let acceptance := _root_.FiatShamir.knowledgeAcceptance
      (sigma (F := F) firstBase secondBase service) (generable firstBase secondBase) Message
      prover keys message
    acceptance * (acceptance / (budget + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witnesses ← _root_.FiatShamir.knowledgeExtractor
          (sigma (F := F) firstBase secondBase service) (generable firstBase secondBase) Message
          prover message budget keys}[SchnorrAndBinding.Relation firstBase keys.1 secondBase keys.2
            witnesses.1 witnesses.2] := by
  have upstream := _root_.FiatShamir.knowledgeExtractor_success
    (sigma (F := F) firstBase secondBase service) (generable firstBase secondBase) Message
    (speciallySound firstBase secondBase service) prover keys message budget bounded
  simpa only [relation_eq] using upstream

end ZkcSecurity.Examples.SchnorrAndSigma
