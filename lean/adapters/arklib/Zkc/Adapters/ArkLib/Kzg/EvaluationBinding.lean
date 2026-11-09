module

public import ArkLib.Commitments.Functional.KZG.Binding

@[expose] public section

/-! Selected KZG evaluation-binding experiment. Upstream source:
ArkLib 1e0241333c18d8b22cb68f9522da5f9fb88f9a06,
`ArkLib/Commitments/Functional/KZG/Binding.lean`.

The adversary receives only the SRS, chooses one point and two values, and
runs its opening prover twice with the selected private states. Setup samples
its nonzero trapdoor privately. Both openings share the same initially empty
uniform-oracle cache. This is average success over setup and oracle answers.
Computational admissibility is a separate, explicit predicate; the upstream
all-functions `tSdhAssumption` is deliberately not used. -/

set_option autoImplicit false
namespace ZkcArkLib.Kzg
open OracleComp OracleSpec
open KZG.CommitmentScheme

variable {p n : Nat} {G₁ G₂ : Type}

/-- Logical group/field observation, including the setup and both proof elements.
It has no native serialization or knowledge interpretation. -/
structure Observation (p n : Nat) (G₁ G₂ : Type) where
  trapdoor : ZMod p
  srs : Vector G₁ (n + 1) × Vector G₂ 2
  commitment : G₁
  point : ZMod p
  leftValue : ZMod p
  rightValue : ZMod p
  leftAccepted : Bool
  rightAccepted : Bool
  leftProof : G₁
  rightProof : G₁

def Observation.ofUpstream (output : BindingExtOutput (p := p) n G₁ G₂) : Observation p n G₁ G₂ :=
  let (tau, srs, cm, z, left, right, acceptedLeft, acceptedRight, proofLeft, proofRight) := output
  ⟨tau, srs, cm, z, left, right, acceptedLeft, acceptedRight, proofLeft, proofRight⟩

def Observation.toUpstream (observation : Observation p n G₁ G₂) : BindingExtOutput (p := p) n G₁ G₂ :=
  (observation.trapdoor, observation.srs, observation.commitment, observation.point,
    observation.leftValue, observation.rightValue, observation.leftAccepted,
    observation.rightAccepted, observation.leftProof, observation.rightProof)

@[simp] theorem Observation.roundtrip (output : BindingExtOutput (p := p) n G₁ G₂) :
    (Observation.ofUpstream output).toUpstream = output := by
  rcases output with ⟨_, _, _, _, _, _, _, _, _, _⟩
  rfl

@[simp] theorem Observation.of_toUpstream (observation : Observation p n G₁ G₂) :
    Observation.ofUpstream observation.toUpstream = observation := by
  cases observation
  rfl

/-- Two successful openings at the same point with different values. Failed
opening runs default to rejection in the actual upstream game. -/
def Observation.Conflict (observation : Observation p n G₁ G₂) : Prop :=
  observation.leftValue ≠ observation.rightValue ∧
    observation.leftAccepted = true ∧ observation.rightAccepted = true

variable {p n : Nat} [Fact (Nat.Prime p)]
  {G₁ G₂ Gₜ : Type} [Group G₁] [PrimeOrderWith G₁ p] [DecidableEq G₁]
  [Group G₂] [PrimeOrderWith G₂ p] [Group Gₜ] [PrimeOrderWith Gₜ p] [DecidableEq Gₜ]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  {g₁ : G₁} {g₂ : G₂}
  (pairing : Additive G₁ →ₗ[ZMod p] Additive G₂ →ₗ[ZMod p] Additive Gₜ)

local instance evaluationInterface : OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  toOC.spec := ZMod p →ₒ ZMod p
  toOC.impl z := do return (CompPoly.CPolynomial.ofFn (← read)).eval z

/-- The selected experiment uses the actual upstream opening protocol and its
adversary/access interface; only the result representation changes. -/
def experiment {Aux : Type} (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec Aux) :
    OptionT ProbComp (Observation p n G₁ G₂) :=
  Observation.ofUpstream <$> bindingGameExt (g₁ := g₁) (g₂ := g₂) Aux adversary
    (kzg (n := n) (g₁ := g₁) (g₂ := g₂) pairing)

noncomputable def averageSuccess {Aux : Type}
    (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec Aux) : ENNReal :=
  Pr{let observation ← experiment (g₁ := g₁) (g₂ := g₂) pairing adversary}[observation.Conflict]

omit [DecidableEq G₁] in
/-- Equality to the base evaluation-binding game checks both access and the
success predicate, rather than treating a citation as a connection theorem. -/
theorem averageSuccess_eq_bindingExperiment [SampleableType G₁] {Aux : Type}
    (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec Aux) :
    averageSuccess (g₁ := g₁) (g₂ := g₂) pairing adversary =
      Commitment.bindingExperiment (init := pure ∅) (impl := randomOracle)
        (kzg (n := n) (g₁ := g₁) (g₂ := g₂) pairing) Aux adversary := by
  unfold averageSuccess experiment Commitment.bindingExperiment
  rw [prEvent_map, binding_game_ext_eq_binding_game (pairing := pairing) adversary]
  rfl

omit [DecidableEq G₁] in
/-- Unconditional reduction inequality, before invoking any hardness claim. -/
theorem averageSuccess_le_tSdh [SampleableType G₁] (generator : g₁ ≠ 1)
    (nondegenerate : pairing g₁ g₂ ≠ 0) {Aux : Type}
    (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec Aux) :
    averageSuccess (g₁ := g₁) (g₂ := g₂) pairing adversary ≤
      Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) n
        (bindingReduction (g₁ := g₁) (g₂ := g₂) pairing Aux adversary) := by
  unfold averageSuccess experiment
  rw [prEvent_map]
  change Pr{let output ← (bindingGameExt (g₁ := g₁) (g₂ := g₂) Aux adversary
    (kzg (n := n) (g₁ := g₁) (g₂ := g₂) pairing))}[bindingCondExt output] ≤ _
  calc
    _ ≤ _ := binding_cond_le_t_sdh_cond (pairing := pairing) generator nondegenerate adversary
    _ = _ := (map_binding_instance_drag adversary _).trans
      (t_sdh_game_eq (g₁ := g₁) (g₂ := g₂) (pairing := pairing) adversary)

/-- Request-side resource/admissibility scope. These predicates must be given
an operational interpretation before making any efficient-adversary claim.
Closure is about this exact reduction, not all Lean functions. -/
structure Scope where
  bindingBudget : Nat
  sdhBudget : Nat
  bindingAllowed : Nat → {Aux : Type} → KzgBindingAdversary p G₁ G₂ n unifSpec Aux → Prop
  sdhAllowed : Nat → Groups.tSdhAdversary n (G₁ := G₁) (G₂ := G₂) (p := p) → Prop
  reductionClosed : ∀ {Aux} (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec Aux),
    bindingAllowed bindingBudget adversary →
      sdhAllowed sdhBudget (bindingReduction (g₁ := g₁) (g₂ := g₂) pairing Aux adversary)

/-- The only hardness premise ranges over the request's explicitly admitted
SDH algorithms. It does not use the upstream all-functions assumption. -/
def ScopedHardness (scope : Scope (n := n) (g₁ := g₁) (g₂ := g₂) pairing) (error : ENNReal) : Prop :=
  ∀ adversary, scope.sdhAllowed scope.sdhBudget adversary →
    Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) n adversary ≤ error

omit [DecidableEq G₁] in
theorem scoped_bound [SampleableType G₁] (generator : g₁ ≠ 1)
    (nondegenerate : pairing g₁ g₂ ≠ 0)
    (scope : Scope (n := n) (g₁ := g₁) (g₂ := g₂) pairing) (error : ENNReal)
    (hardness : ScopedHardness (g₁ := g₁) (g₂ := g₂) pairing scope error)
    {Aux : Type} (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec Aux)
    (admitted : scope.bindingAllowed scope.bindingBudget adversary) :
    averageSuccess (g₁ := g₁) (g₂ := g₂) pairing adversary ≤ error :=
  (averageSuccess_le_tSdh pairing generator nondegenerate adversary).trans
    (hardness _ (scope.reductionClosed adversary admitted))

end ZkcArkLib.Kzg
