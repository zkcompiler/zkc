import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

/-! Ordered contraction and factor-product laws.

The fixed input tables, applied prefix and multiplicity of each factor remain
explicit. Equal values on the Boolean cube do not identify the polynomial used
for a subsequent challenge. These are algebraic representation laws; probability,
wire formats and native storage require their own contracts.
-/

set_option autoImplicit false
open scoped BigOperators
namespace Zkc.Polynomial.Factors

section

variable {A B K : Type} [Fintype A] [CommRing K]

/-- A prefix contraction of an immutable input table. A indexes already
    contracted Boolean assignments; B indexes the remaining suffix. -/
def contraction (weight : A → K) (table : A → Bool → B → K) : Bool → B → K :=
  fun bit b => ∑ a, weight a * table a bit b

def storedFold (r : K) (h : Bool → B → K) (b : B) : K :=
  (1-r) * h false b + r * h true b

/-- Recompute from the old input/prefix, without assuming equality of the
    scratch buffers used by an implementation. -/
def recomputedFold (r : K) (weight : A → K)
    (table : A → Bool → B → K) (b : B) : K :=
  ∑ a, ((weight a * (1-r)) * table a false b + (weight a * r) * table a true b)

theorem checkpoint (r : K) (weight : A → K)
    (table : A → Bool → B → K) (b : B) :
    storedFold r (contraction weight table) b = recomputedFold r weight table b := by
  simp only [storedFold,contraction,recomputedFold,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The paired endpoint values of the next Sumcheck message agree after a
    switch to the same contracted representation. This is a local algebraic
    lemma, not a theorem about bytes, allocation, native code or soundness. -/
theorem contraction_sum [Fintype B] (weight : A → K) (table : A → Bool → B → K) (bit : Bool) :
    (∑ b, contraction weight table bit b) =
      ∑ a, weight a * (∑ b, table a bit b) := by
  simp only [contraction,Finset.mul_sum]
  exact Finset.sum_comm

theorem rebuild (r : K) (weight : A → K) (table : A → Bool → B → K)
    (materialized : B → K)
    (valid : ∀ b, materialized b = recomputedFold r weight table b) :
    ∀ b, materialized b = storedFold r (contraction weight table) b := by
  intro b
  exact (valid b).trans (checkpoint r weight table b).symm


end

section

variable {A B J U K : Type} [Fintype A] [Fintype B] [Fintype U] [CommRing K]

/-- Lists retain multiplicity: a term may use the same input table twice.
    This is a polynomial message at t, not a multilinear extension of the
    pointwise product table. -/
def message (coeff : U → K) (factors : U → List J)
    (values : J → B → K) : K :=
  ∑ b, ∑ u, coeff u * ((factors u).map (fun j => values j b)).prod

theorem message_congr (coeff : U → K) (factors : U → List J)
    (left right : J → B → K) (h : ∀ j b, left j b = right j b) :
    message coeff factors left = message coeff factors right := by
  have he : left = right := funext (fun j => funext (h j))
  rw [he]

/-- A prefix representation relation is lifted through sums of products,
    at every field point t (hence at every transmitted evaluation point).
    No field-size, interpolation, randomness or soundness claim is needed. -/
theorem product_checkpoint (coeff : U → K) (factors : U → List J)
    (weight : A → K) (table : J → A → Bool → B → K) (t : K) :
    message coeff factors
      (fun j => Zkc.Polynomial.Factors.storedFold t (Zkc.Polynomial.Factors.contraction weight (table j))) =
    message coeff factors
      (fun j => Zkc.Polynomial.Factors.recomputedFold t weight (table j)) := by
  apply message_congr
  intro j b
  exact Zkc.Polynomial.Factors.checkpoint t weight (table j) b

def affine (r a b : K) : K := (1-r)*a+r*b

/-- The missing cross term explains why collapsing multiplicands into one
    Boolean product table changes the polynomial between Boolean points. -/
theorem collapse_gap (r a0 a1 b0 b1 : K) :
    affine r (a0*b0) (a1*b1) - affine r a0 a1 * affine r b0 b1 =
      r*(1-r)*(a0-a1)*(b0-b1) := by
  unfold affine
  ring

theorem collapse_agrees_at_boolean (a0 a1 b0 b1 : K) :
    affine 0 (a0*b0) (a1*b1) = affine 0 a0 a1 * affine 0 b0 b1 ∧
    affine 1 (a0*b0) (a1*b1) = affine 1 a0 a1 * affine 1 b0 b1 := by
  simp [affine]

/-- Equal initial Boolean sums do not justify replacing a product-polynomial
    Sumcheck by Sumcheck of its multilinearized Boolean table. -/
theorem collapse_changes_integer_evaluation :
    affine (2 : Int) (0*0) (1*1) = 2 ∧
    affine (2 : Int) 0 1 * affine 2 0 1 = 4 := by decide


end

section
variable {A B J U K : Type} [Fintype A] [Fintype B] [Fintype U] [CommRing K]

/-- Hoist constant factor scales into product coefficients. Lists preserve
    multiplicity, so a repeated factor contributes its scale repeatedly.
    The factor graph is retained even for zero coefficients: no wire-degree
    or interpolation-format change is licensed by this equality. -/
theorem hoist_scales (coeff : U → K) (factors : U → List J)
    (scale : J → K) (values : J → B → K) :
    Zkc.Polynomial.Factors.message coeff factors (fun j b => scale j * values j b) =
      Zkc.Polynomial.Factors.message (fun u => coeff u * ((factors u).map scale).prod)
        factors values := by
  have hp (js : List J) (b : B) :
      (js.map (fun j => scale j * values j b)).prod =
        (js.map scale).prod * (js.map (fun j => values j b)).prod := by
    induction js with
    | nil => simp
    | cons j js ih => simp only [List.map_cons,List.prod_cons,ih]; ring
  simp only [Zkc.Polynomial.Factors.message,hp,mul_assoc]

/-- Explicit phase boundary: h represents the APPLIED prefix; r is received
    but pending. Exporting the completed factor requires this final fold. -/
theorem finalize_export (r : K) (weight : A → K) (table : A → Bool → Unit → K)
    (h : Bool → Unit → K)
    (rep : ∀ bit, h bit () = Zkc.Polynomial.Factors.contraction weight table bit ()) :
    h false () + r * (h true () - h false ()) =
      Zkc.Polynomial.Factors.recomputedFold r weight table () := by
  rw [← Zkc.Polynomial.Factors.checkpoint]
  simp only [Zkc.Polynomial.Factors.storedFold,← rep]
  ring

/-- Algebraic phase control, not a native benchmark or new cryptographic attack. -/
theorem pending_challenge_is_observable :
    (2 : Int) + 3 * (5-2) = 11 ∧ (2 : Int) ≠ 11 := by decide


end

end Zkc.Polynomial.Factors
