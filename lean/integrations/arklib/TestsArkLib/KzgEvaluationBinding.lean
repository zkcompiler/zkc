import ZkcArkLib.Kzg.OpeningClient

set_option autoImplicit false
namespace TestsArkLib.KzgEvaluationBinding
open OracleComp OracleSpec ZkcArkLib.Kzg KZG.CommitmentScheme

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
abbrev F := ZMod 7
abbrev G := Multiplicative F
attribute [local instance] KZG.bindingOracleInterface
instance : PrimeOrderWith G 7 := ⟨by simp [Nat.card_eq_fintype_card, G, F]⟩
instance : Module F (Additive G) := inferInstanceAs (Module F F)

def pairing : Additive G →ₗ[F] Additive G →ₗ[F] Additive G :=
  LinearMap.mul F F

abbrev generator : G := Multiplicative.ofAdd (1 : F)

example : generator ≠ 1 := by decide +kernel
example : pairing generator generator ≠ 0 := by decide +kernel

/-- A real group/field opening pair for the zero polynomial. Both values are
zero, so acceptance of both proofs is never an evaluation-binding conflict. -/
def zeroOpening : OpeningPair 7 G := ⟨1, 2, 0, 0, 1, 1⟩

def client (_srs : Vector G 2 × Vector G 2) : ProbComp (OpeningPair 7 G) := pure zeroOpening

example : KZG.verifyOpening (g₁ := generator) (g₂ := generator) pairing
    (Groups.PowerSrs.generate (g₁ := generator) (g₂ := generator) 1 (3 : F)).2
    zeroOpening.commitment zeroOpening.leftProof zeroOpening.point zeroOpening.leftValue = true := by
  decide +kernel

example : (experiment (g₁ := generator) (g₂ := generator) pairing (openingAdversary client)).run =
    some <$> openingExperiment (g₁ := generator) (g₂ := generator) pairing client :=
  experiment_openingAdversary _ _

noncomputable instance : SampleableType G := SampleableType.ofFintype G

example : Pr{let observed ← (openingExperiment (g₁ := generator) (g₂ := generator) pairing client)}[
    observed.Conflict] ≤ Groups.tSdhExperiment (g₁ := generator) (g₂ := generator) 1
      (bindingReduction (g₁ := generator) (g₂ := generator) pairing G (openingAdversary client)) :=
  opening_success_le_tSdh pairing (by decide +kernel) (by decide +kernel) client

/-- Dropping nondegeneracy accepts incompatible openings. The reduction
cannot be invoked with this verifier as though it had the checked binding. -/
example : ¬ (0 : Additive G →ₗ[F] Additive G →ₗ[F] Additive G) generator generator ≠ 0 := by decide +kernel
example : KZG.verifyOpening (g₁ := generator) (g₂ := generator) (0 : Additive G →ₗ[F] Additive G →ₗ[F] Additive G)
    (Groups.PowerSrs.generate (g₁ := generator) (g₂ := generator) 1 (3 : F)).2 1 1 2 1 = true := by
  decide +kernel

example (srs : Vector G 2 × Vector G 2) :
    IsQueryBoundP ((openingAdversary client).claim srs) (fun _ => True) 0 :=
  claim_query_bound 0 client (by intro; simp [client, isQueryBoundP_pure]) srs

/-- An empty computational scope can satisfy a zero bound vacuously, but it
cannot admit even the concrete zero-query client. -/
def deniedScope : Scope (n := 1) (g₁ := generator) (g₂ := generator) pairing where
  bindingBudget := 0
  sdhBudget := 0
  bindingAllowed := fun _ {_} _ => False
  sdhAllowed := fun _ _ => False
  reductionClosed := fun _ impossible => impossible.elim

example : ScopedHardness pairing deniedScope 0 := fun _ impossible => impossible.elim
example : ¬ deniedScope.bindingAllowed deniedScope.bindingBudget (openingAdversary client) := by intro impossible; exact impossible

#print axioms averageSuccess_eq_bindingExperiment
#print axioms averageSuccess_le_tSdh
#print axioms scoped_bound
#print axioms experiment_openingAdversary
#print axioms opening_success_le_tSdh
end TestsArkLib.KzgEvaluationBinding
