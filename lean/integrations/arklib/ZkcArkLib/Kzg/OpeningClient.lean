module

public import ZkcArkLib.Kzg.EvaluationBinding
public import VCVio.OracleComp.QueryTracking.QueryBound

@[expose] public section

/-! A concrete noninteractive group/field client of the selected KZG game.
The client returns one commitment, one evaluation point, two claimed values
and two group proofs. Proofs are sent by the actual one-message upstream
prover; the verifier is the same KZG verifier used by the reduction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcArkLib.Kzg
open OracleComp OracleSpec ProtocolSpec KZG.CommitmentScheme

structure OpeningPair (p : Nat) (G : Type) where
  commitment : G
  point : ZMod p
  leftValue : ZMod p
  rightValue : ZMod p
  leftProof : G
  rightProof : G

variable {p n : Nat} [Fact (Nat.Prime p)]
  {G₁ G₂ Gₜ : Type} [Group G₁] [PrimeOrderWith G₁ p] [DecidableEq G₁]
  [Group G₂] [PrimeOrderWith G₂ p] [Group Gₜ] [PrimeOrderWith Gₜ p] [DecidableEq Gₜ]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] {g₁ : G₁} {g₂ : G₂}
  (pairing : Additive G₁ →ₗ[ZMod p] Additive G₂ →ₗ[ZMod p] Additive Gₜ)

@[instance_reducible] local instance openingEvaluationInterface : OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  toOC.spec := ZMod p →ₒ ZMod p
  toOC.impl z := do return (CompPoly.CPolynomial.ofFn (← read)).eval z

/-- There are no verifier challenges or additional opening-phase queries.
The only ambient oracle access belongs to the client's claim computation. -/
def messageProver : Prover unifSpec (G₁ × (_q : ZMod p) × ZMod p) G₁ Bool Unit
    ⟨!v[.P_to_V], !v[G₁]⟩ where
  PrvState := fun | 0 => G₁ | _ => Unit
  input := fun (_, proof) => proof
  sendMessage := fun ⟨0, _⟩ proof => pure (proof, ())
  receiveChallenge := fun ⟨i, impossible⟩ => by
    have : i = 0 := Fin.eq_zero i
    subst this
    nomatch impossible
  output := fun _ => pure (true, ())

def openingAdversary
    (client : (Vector G₁ (n + 1) × Vector G₂ 2) → OracleComp unifSpec (OpeningPair p G₁)) :
    KzgBindingAdversary p G₁ G₂ n unifSpec G₁ where
  claim := fun srs => (fun opening => (opening.commitment, ⟨opening.point,
    opening.leftValue, opening.rightValue, opening.leftProof, opening.rightProof⟩)) <$> client srs
  prover := fun _ => messageProver

omit [DecidableEq G₁] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- Concrete resource coordinate: the adapter preserves the client's uniform
oracle-query bound in the claim phase. This is not a machine-time bound. -/
theorem claim_query_bound (queries : Nat)
    (client : (Vector G₁ (n + 1) × Vector G₂ 2) → OracleComp unifSpec (OpeningPair p G₁))
    (bounded : ∀ srs, IsQueryBoundP (client srs) (fun _ => True) queries)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2) :
    IsQueryBoundP ((openingAdversary client).claim srs) (fun _ => True) queries := by
  unfold openingAdversary
  exact (isQueryBoundP_map_iff _ _ _).mpr (bounded srs)

/-- A direct experiment, stated entirely in the concrete client's records.
Setup randomness is private; the client never receives the trapdoor. -/
def openingExperiment
    (client : (Vector G₁ (n + 1) × Vector G₂ 2) → OracleComp unifSpec (OpeningPair p G₁)) :
    ProbComp (Observation p n G₁ G₂) := do
  let tau ← Groups.sampleNonzeroZMod (p := p)
  let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n tau
  let opening ← (simulateQ randomOracle (client srs)).run' ∅
  pure ⟨tau, srs, opening.commitment, opening.point, opening.leftValue, opening.rightValue,
    KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) pairing srs.2
      opening.commitment opening.leftProof opening.point opening.leftValue,
    KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) pairing srs.2
      opening.commitment opening.rightProof opening.point opening.rightValue,
    opening.leftProof, opening.rightProof⟩

omit [DecidableEq G₁] in
theorem message_run (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (commitment proof : G₁) (point value : ZMod p) :
    ((Reduction.mk messageProver
      ((kzg (n := n) (g₁ := g₁) (g₂ := g₂) pairing).opening (srs, srs)).verifier).run
        (commitment, ⟨point, value⟩) proof).run =
      pure (some ((fun ⟨0, _⟩ => proof, true, ()),
        KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) pairing srs.2 commitment proof point value)) := by
  simp [Reduction.run, Prover.run, Prover.runToRound, Prover.processRound,
    messageProver, kzg, Verifier.run, Fin.induction, Fin.induction.go, Transcript.concat]
  funext index
  fin_cases index
  rfl

omit [DecidableEq G₁] in
/-- Whole-computation equality preserves unsuccessful outcomes as well as
conflicts. The two openings have no hidden, stronger adversary access. -/
theorem experiment_openingAdversary
    (client : (Vector G₁ (n + 1) × Vector G₂ 2) → OracleComp unifSpec (OpeningPair p G₁)) :
    (experiment (g₁ := g₁) (g₂ := g₂) pairing (openingAdversary client)).run =
      some <$> openingExperiment (g₁ := g₁) (g₂ := g₂) pairing client := by
  unfold experiment
  rw [OptionT.run_map]
  change Option.map Observation.ofUpstream <$>
    (bindingGameExt (g₁ := g₁) (g₂ := g₂) G₁ (openingAdversary client)
      (kzg (n := n) (g₁ := g₁) (g₂ := g₂) pairing)).run = _
  unfold bindingGameExt openingExperiment
  dsimp only [openingAdversary, kzg]
  simp [Reduction.run, Prover.run, Prover.runToRound, Fin.induction,
    Fin.induction.go, Prover.processRound, messageProver, Verifier.run,
    liftComp_eq_liftM, QueryImpl.addLift_def,
    QueryImpl.simulateQ_add_liftM_left, StateT.run'_eq, Observation.ofUpstream]

omit [DecidableEq G₁] in
/-- The direct record client's success event is exactly the adapter's event. -/
theorem opening_success_eq
    (client : (Vector G₁ (n + 1) × Vector G₂ 2) → OracleComp unifSpec (OpeningPair p G₁)) :
    Pr{let observed ← (openingExperiment (g₁ := g₁) (g₂ := g₂) pairing client)}[observed.Conflict] =
      averageSuccess (g₁ := g₁) (g₂ := g₂) pairing (openingAdversary client) := by
  unfold averageSuccess
  rw [OptionT.prEvent_eq_run, experiment_openingAdversary, prEvent_map]
  rfl

omit [DecidableEq G₁] in
/-- Concrete selected opening client, with the same reduction and access scope. -/
theorem opening_success_le_tSdh [SampleableType G₁]
    (generator : g₁ ≠ 1) (nondegenerate : pairing g₁ g₂ ≠ 0)
    (client : (Vector G₁ (n + 1) × Vector G₂ 2) → OracleComp unifSpec (OpeningPair p G₁)) :
    Pr{let observed ← (openingExperiment (g₁ := g₁) (g₂ := g₂) pairing client)}[observed.Conflict] ≤
      Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) n
        (bindingReduction (g₁ := g₁) (g₂ := g₂) pairing G₁ (openingAdversary client)) := by
  rw [opening_success_eq]
  exact averageSuccess_le_tSdh pairing generator nondegenerate _

end ZkcArkLib.Kzg
