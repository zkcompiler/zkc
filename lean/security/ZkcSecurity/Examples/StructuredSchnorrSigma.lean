module

public import ZkcExamples.Structured.SchnorrContract
public import ZkcExamples.Structured.SchnorrCheckpoints
public import ZkcSecurity.VCVio.Schnorr
public import Examples.Schnorr.SigmaProtocol
public import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

/-! Actual reuse of the pinned VCVio Schnorr Sigma theorems. The coordinates
come from observed sends of the admitted prover and the admitted verifier's
selected decision. The successful delivery profile and fresh uniform sampling
are mathematical experiments, not native provider or joint scheduling proofs.

VCVio's bundled Sigma data additionally needs SampleableType G for its
commitment-only simulator. Its separate full transcript simulator uses field
samples. Fresh-challenge HVZK here does not replace fixed-challenge HVZK.
-/
namespace ZkcSecurity.Examples.StructuredSchnorrSigma
open ZkcExamples.Structured
open Zkc.Protocols.Schnorr.Common
open OracleComp

set_option smartUnfolding false

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

def decision (base key commitment : G) (challenge response : F) (service : Nat) : Bool :=
  decide (SchnorrBinding.decisionSelector.read {}
    (SchnorrContract.observedBoundary base key service
      ⟨commitment, fun _ => response⟩ challenge) = some true)

theorem decision_eq (base key commitment : G) (challenge response : F) (service : Nat) :
    decision base key commitment challenge response service =
      decide (response • base = commitment + challenge • key) := by
  apply decide_eq_decide.mpr
  exact (SchnorrContract.observed_accepts_iff base key service
    ⟨commitment, fun _ => response⟩ challenge).trans
      (SchnorrInteractive.accepted_iff base key service ⟨commitment, fun _ => response⟩ challenge)

/-- The full verifier outcome is retained when a transcript is made public. -/
def publicView (base key : G) (service : Nat) (transcript : G × F × F) :
    VCVio.Schnorr.View F G :=
  (transcript.1, transcript.2.1, transcript.2.2,
    (SchnorrInteractive.run base key service
      ⟨transcript.1, fun _ => transcript.2.2⟩ transcript.2.1).outcome)

variable [SampleableType F] [SampleableType G]

/-- Commit runs the proved source prefix with the sampled nonce. It has no
challenge reply, and returns exactly the observed send and retained private state. -/
def commit (base _proverKey : G) (nonceService : Nat) (_key : G) (_witness : F) :
    ProbComp (G × F) := do
  let nonce ← $ᵗ F
  pure (SchnorrCheckpoints.commitment base nonce nonceService)

def respond (base proverKey : G) (nonceService : Nat) (_key : G)
    (witness nonce challenge : F) : ProbComp F :=
  pure (SchnorrHonestProver.messages base proverKey witness nonce challenge nonceService).2

omit [DecidableEq F] in
theorem commit_eq (base proverKey key : G) (witness : F) (nonceService : Nat) :
    commit base proverKey nonceService key witness =
      (_root_.Schnorr.sigma F G base).commit key witness := by
  simp only [commit, SchnorrCheckpoints.commitment_eq, _root_.Schnorr.sigma]

theorem respond_eq (base proverKey key : G) (witness nonce challenge : F) (nonceService : Nat) :
    respond base proverKey nonceService key witness nonce challenge =
      (_root_.Schnorr.sigma F G base).respond key witness nonce challenge := by
  simp only [respond, SchnorrHonestProver.messages_eq, _root_.Schnorr.sigma]

omit [SampleableType F] [SampleableType G] in
/-- Source relation orientation is normalized explicitly against the actual
formula process. No source witness is required in the extraction conclusion. -/
theorem relation_eq (base key : G) (witness : F) :
    SchnorrBinding.Relation base key witness ↔ decide (witness • base = key) = true := by
  rw [SchnorrBinding.relation_iff]
  constructor
  · intro same
    exact decide_eq_true same.symm
  · intro same
    exact (of_decide_eq_true same).symm

def sigma (base proverKey : G) (nonceService challengeService : Nat) :
    SigmaProtocol G F G F F F (fun key witness => decide (witness • base = key)) where
  commit := commit base proverKey nonceService
  respond := respond base proverKey nonceService
  verify key commitment challenge response :=
    decision base key commitment challenge response challengeService
  sim := (_root_.Schnorr.sigma F G base).sim
  extract := (_root_.Schnorr.sigma F G base).extract

/-- Equality of each actual source coordinate discharges the upstream interface.
The prover's key copy is independent of the verifier statement throughout. -/
theorem sigma_eq (base proverKey : G) (nonceService challengeService : Nat) :
    sigma (F := F) base proverKey nonceService challengeService =
      _root_.Schnorr.sigma F G base := by
  have commits : commit base proverKey nonceService =
      (_root_.Schnorr.sigma F G base).commit := by
    funext key witness
    exact commit_eq base proverKey key witness nonceService
  have responses : respond base proverKey nonceService =
      (_root_.Schnorr.sigma F G base).respond := by
    funext key witness nonce challenge
    exact respond_eq base proverKey key witness nonce challenge nonceService
  have decisions : (fun key commitment challenge response =>
      decision base key commitment challenge response challengeService) =
        (_root_.Schnorr.sigma F G base).verify := by
    funext key commitment challenge response
    exact decision_eq base key commitment challenge response challengeService
  unfold sigma
  rw [commits, responses, decisions]

theorem complete (base proverKey key : G) (witness : F)
    (nonceService challengeService : Nat) (valid : SchnorrBinding.Relation base key witness) :
    𝒟[do
      let (commitment, state) ← commit base proverKey nonceService key witness
      let challenge ← $ᵗ F
      let response ← respond base proverKey nonceService key witness state challenge
      pure (decision base key commitment challenge response challengeService)] {true} = 1 := by
  have upstream : (sigma (F := F) base proverKey nonceService challengeService).PerfectlyComplete := by
    rw [sigma_eq]
    exact _root_.Schnorr.sigma_complete F G base
  exact upstream key witness ((relation_eq base key witness).mp valid)

/-- The concrete extractor is pure and therefore returns the displayed new
witness; this is stronger than leaving upstream's support premise undischarged. -/
theorem extract_relation (base key : G) (service : Nat) (prover : Strategy F G)
    (first second : F) (distinct : first ≠ second)
    (acceptFirst : (SchnorrInteractive.run base key service prover first).outcome =
      .returned (some true))
    (acceptSecond : (SchnorrInteractive.run base key service prover second).outcome =
      .returned (some true)) :
    SchnorrBinding.Relation base key
      ((prover.response first - prover.response second) / (first - second)) := by
  apply (relation_eq ..).mpr
  apply _root_.Schnorr.sigma_speciallySound F G base key prover.commitment first second
    (prover.response first) (prover.response second) distinct
  · exact decide_eq_true ((SchnorrInteractive.accepted_iff ..).mp acceptFirst)
  · exact decide_eq_true ((SchnorrInteractive.accepted_iff ..).mp acceptSecond)
  · simp [_root_.Schnorr.sigma, div_eq_mul_inv]

/-- Upstream special soundness also discharges the actual selected target at
the first source execution's returned boundary, with one new witness assignment. -/
theorem extracted_target (base key : G) (service : Nat) (prover : Strategy F G)
    (first second : F) (distinct : first ≠ second)
    (acceptFirst : SchnorrBinding.decisionSelector.read {}
      (SchnorrContract.observedBoundary base key service prover first) = some true)
    (acceptSecond : SchnorrBinding.decisionSelector.read {}
      (SchnorrContract.observedBoundary base key service prover second) = some true) :
    (SchnorrBinding.target (F := F) (G := G)).Holds {}
      (SchnorrContract.observedBoundary base key service prover first)
      (SchnorrBinding.assignments base
        ((prover.response first - prover.response second) / (first - second))) :=
  (SchnorrContract.extractionRequests base key service prover first second).resolve
    ⟨SchnorrContract.target_translation ..,
      (SchnorrBinding.relation_iff ..).mp (extract_relation base key service prover
        first second distinct ((SchnorrContract.observed_accepts_iff ..).mp acceptFirst)
          ((SchnorrContract.observed_accepts_iff ..).mp acceptSecond))⟩

local instance : MeasurableSpace (VCVio.Schnorr.View F G) := ⊤

/-- Full public observation, including the actual verifier outcome, under
independently fresh full-field nonce and challenge. Finite F is the upstream
HVZK theorem's assumption. The simulator has no witness argument. -/
theorem fresh_challenge_hvzk [Finite F] (base proverKey key : G) (witness : F)
    (nonceService challengeService : Nat) (valid : SchnorrBinding.Relation base key witness) :
    𝒟[publicView base key challengeService <$>
      (sigma (F := F) base proverKey nonceService challengeService).realTranscript key witness] =
    𝒟[publicView base key challengeService <$> _root_.Schnorr.simTranscript F G base key] := by
  rw [sigma_eq]
  have upstream := _root_.Schnorr.sigma_hvzk F G base key witness
    ((relation_eq base key witness).mp valid)
  exact (upstream.map (publicView base key challengeService)).evalDist_eq

end ZkcSecurity.Examples.StructuredSchnorrSigma
