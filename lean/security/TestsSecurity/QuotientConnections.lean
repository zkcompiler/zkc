import ZkcSecurity.Families.Polynomial.Quotient

set_option autoImplicit false
namespace TestsSecurity.QuotientConnections
open Zkc.Obligations Polynomial
open ZkcSecurity.Families.Polynomial

variable {F : Type} [Field F]

def equalityApplication : ClaimRelation (F × F) Unit := .exact fun pair _ => pair.1 = pair.2
noncomputable def equalityPolynomial (pair : F × F) : F[X] := C (pair.1 - pair.2)

theorem equality_adequacy (pair : F × F) :
    (evaluations {0} 0).token.Yes (equalityPolynomial pair) →
      equalityApplication.token.Yes pair := by
  rintro ⟨_, _, vanishes⟩
  exact ⟨(), sub_eq_zero.mp (by simpa [equalityPolynomial] using vanishes 0 (by simp))⟩

theorem equality_realizes (pair : F × F) :
    equalityApplication.token.Yes pair →
      (evaluations {0} 0).token.Yes (equalityPolynomial pair) := by
  rintro ⟨_, equal⟩
  have equal : pair.1 = pair.2 := equal
  refine ⟨(), ?_, ?_⟩
  · simp [equalityPolynomial, equal]
  · intro point _
    simp [equalityPolynomial, equal]

theorem equality_sound :
    (equalityApplication (F := F)).SoundLink (quotient {0} 0) equalityPolynomial :=
  external_sound equalityApplication {0} 0 equalityPolynomial equality_adequacy

theorem equality_honest :
    (equalityApplication (F := F)).HonestLink (quotient {0} 0) equalityPolynomial :=
  external_honest equalityApplication {0} 0 equalityPolynomial equality_realizes

/-- A second application reuses exactly the same quotient-entry law. Its
application adequacy is still an author-owned mathematical theorem. -/
def productApplication : ClaimRelation (F × F × F) Unit :=
  .exact fun triple _ => triple.1 * triple.2.1 = triple.2.2

noncomputable def productPolynomial (triple : F × F × F) : F[X] := C (triple.1 * triple.2.1 - triple.2.2)

theorem product_sound :
    (productApplication (F := F)).SoundLink (quotient {0} 0) productPolynomial := by
  apply external_sound
  rintro triple ⟨_, _, vanishes⟩
  exact ⟨(), sub_eq_zero.mp (by simpa [productPolynomial] using vanishes 0 (by simp))⟩

theorem product_honest :
    (productApplication (F := F)).HonestLink (quotient {0} 0) productPolynomial := by
  apply external_honest
  rintro triple ⟨_, equal⟩
  have equal : triple.1 * triple.2.1 = triple.2.2 := equal
  refine ⟨(), ?_, ?_⟩
  · simp [productPolynomial, equal]
  · intro point _
    simp [productPolynomial, equal]

/-- A quotient needs its degree bound even when the polynomial vanishes. -/
theorem excess_degree_refused :
    ¬ (quotient ({0} : Finset F) 0).token.Yes (X ^ 2) := by
  rintro ⟨witness, holds⟩
  have bounded := (evaluations_of_quotient {0} 0 (X ^ 2) witness holds).1
  norm_num at bounded

theorem larger_budget_is_a_different_claim :
    (quotient ({0} : Finset F) 1).token.Yes (X ^ 2) := by
  refine ⟨X, ?_, ?_⟩
  · simp [Lagrange.nodal, pow_two]
  · simp

/-- A nonzero quotient over two distinct roots exercises the degree accounting
in a genuine polynomial constraint, beyond the zero residuals above. -/
theorem nonconstant_quotient [DecidableEq F] :
    (quotient ({0, 1} : Finset F) 1).Holds
      (X * (X - C 1) * (X + C 2)) (X + C 2) := by
  constructor
  · simp [Lagrange.nodal]
  · simp

theorem nonconstant_evaluations [DecidableEq F] :
    (evaluations ({0, 1} : Finset F) 1).token.Yes
      (X * (X - C 1) * (X + C 2)) :=
  ⟨(), evaluations_of_quotient _ _ _ _ nonconstant_quotient⟩

theorem nonconstant_quotient_refuses_zero_witness [DecidableEq F] :
    ¬ (quotient ({0, 1} : Finset F) 1).Holds
      (X * (X - C 1) * (X + C 2)) 0 := by
  rintro ⟨identity, _⟩
  have nonzero : (X * (X - C 1) * (X + C 2) : F[X]) ≠ 0 :=
    mul_ne_zero (mul_ne_zero X_ne_zero (X_sub_C_ne_zero 1)) (X_add_C_ne_zero 2)
  exact nonzero (by simpa using identity)

/-- Field division is total at zero, but this does not produce a quotient
identity. A pointwise quotient formula must establish its nonzero denominator. -/
theorem zero_denominator_is_not_quotient :
    (1 : F) / 0 = 0 ∧ ¬ (quotient ({0} : Finset F) 0).token.Yes 1 := by
  refine ⟨div_zero _, ?_⟩
  rintro ⟨witness, holds⟩
  have zero := (evaluations_of_quotient {0} 0 1 witness holds).2 0 (by simp)
  simp at zero

def changedApplication : ClaimRelation (F × F) Unit := .exact fun pair _ => pair.1 + 1 = pair.2

theorem changed_meaning_refuses_old_link :
    ¬ (changedApplication (F := F)).SoundLink (quotient {0} 0) equalityPolynomial := by
  intro link
  have no : (changedApplication (F := F)).No (0, 0) := by
    simp [changedApplication, ClaimRelation.exact]
  have target : (quotient ({0} : Finset F) 0).token.Yes (equalityPolynomial (0, 0)) :=
    equality_honest (0, 0) ⟨(), rfl⟩
  exact link (0, 0) no target

#print axioms equality_sound
#print axioms equality_honest
#print axioms product_sound
#print axioms product_honest
#print axioms changed_meaning_refuses_old_link

end TestsSecurity.QuotientConnections
