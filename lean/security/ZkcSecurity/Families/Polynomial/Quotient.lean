module

public import Zkc.Obligations.ClaimRelation
public import Mathlib.LinearAlgebra.Lagrange

public section

/-! Exact entry into a quotient-polynomial claim. The finite evaluation domain
and degree budget are fixed parameters on both sides. This mathematical adapter
does not identify an application relation with its polynomial encoding, or
supply an executable quotient computation or a knowledge extractor. -/

set_option autoImplicit false
namespace ZkcSecurity.Families.Polynomial
open Zkc.Obligations _root_.Polynomial

variable {F : Type} [Field F]

@[expose] def evaluations (domain : Finset F) (budget : Nat) :
    ClaimRelation F[X] Unit :=
  .exact fun polynomial _ => polynomial.natDegree ≤ domain.card + budget ∧
    ∀ point ∈ domain, polynomial.eval point = 0

@[expose] def quotient (domain : Finset F) (budget : Nat) :
    ClaimRelation F[X] F[X] :=
  .exact fun polynomial witness =>
    polynomial = Lagrange.nodal domain id * witness ∧ witness.natDegree ≤ budget

theorem evaluations_of_quotient (domain : Finset F) (budget : Nat)
    (polynomial witness : F[X])
    (holds : (quotient domain budget).Holds polynomial witness) :
    (evaluations domain budget).Holds polynomial () := by
  rcases holds with ⟨rfl, bounded⟩
  constructor
  · exact natDegree_mul_le.trans (by simpa using Nat.add_le_add_left bounded domain.card)
  · intro point member
    have zero : (Lagrange.nodal domain id).eval point = 0 := by
      simpa only [id_eq] using Lagrange.eval_nodal_at_node (v := id) member
    rw [eval_mul, zero, zero_mul]

/-- Distinct domain points make their linear factors pairwise coprime.
The zero polynomial is included and has the zero quotient. -/
theorem exists_quotient (domain : Finset F) (budget : Nat) (polynomial : F[X])
    (holds : (evaluations domain budget).Holds polynomial ()) :
    ∃ witness, (quotient domain budget).Holds polynomial witness := by
  rcases holds with ⟨bounded, vanishes⟩
  have divides : Lagrange.nodal domain id ∣ polynomial := by
    apply Finset.prod_dvd_of_coprime
    · intro left _ right _ different
      exact pairwise_coprime_X_sub_C Function.injective_id different
    · intro point member
      exact dvd_iff_isRoot.mpr (vanishes point member)
  obtain ⟨witness, equal⟩ := divides
  by_cases zero : witness = 0
  · exact ⟨witness, equal, by simp [zero]⟩
  · refine ⟨witness, equal, ?_⟩
    rw [equal, natDegree_mul Lagrange.nodal_ne_zero zero, Lagrange.natDegree_nodal] at bounded
    exact Nat.le_of_add_le_add_left bounded

theorem quotient_honest (domain : Finset F) (budget : Nat) :
    (evaluations domain budget).HonestLink (quotient domain budget) id := by
  rintro polynomial ⟨_, holds⟩
  exact exists_quotient domain budget polynomial holds

theorem quotient_sound (domain : Finset F) (budget : Nat) :
    (evaluations domain budget).SoundLink (quotient domain budget) id := by
  rintro polynomial no ⟨witness, holds⟩
  exact no ⟨(), evaluations_of_quotient domain budget polynomial witness holds⟩

/-- An external application supplies its own adequacy theorem. The selected
encoding is an ordinary map; its name grants no authority over the relation. -/
theorem external_sound {Statement Witness : Type} (application : ClaimRelation Statement Witness)
    (domain : Finset F) (budget : Nat) (encode : Statement → F[X])
    (adequacy : ∀ statement, (evaluations domain budget).token.Yes (encode statement) →
      application.token.Yes statement) :
    application.SoundLink (quotient domain budget) encode := by
  rintro statement no ⟨quotientWitness, target⟩
  obtain ⟨witness, holds⟩ := adequacy statement
    ⟨(), evaluations_of_quotient domain budget (encode statement) quotientWitness target⟩
  exact application.no_excludes statement witness no holds

theorem external_honest {Statement Witness : Type} (application : ClaimRelation Statement Witness)
    (domain : Finset F) (budget : Nat) (encode : Statement → F[X])
    (realizes : ∀ statement, application.token.Yes statement →
      (evaluations domain budget).token.Yes (encode statement)) :
    application.HonestLink (quotient domain budget) encode := by
  intro statement yes
  exact quotient_honest domain budget (encode statement) (realizes statement yes)

end ZkcSecurity.Families.Polynomial
