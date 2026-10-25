module

public import ZkcSecurity.Families.Sumcheck.Round
public import ZkcSecurity.Families.Sumcheck.TableReference
public import ZkcSecurity.Families.Sumcheck.FactorReference
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! Reuse tests and negative controls for reference mathematics. These are
kernel-checked mathematics, not endpoint, execution or native sampling tests. -/

set_option autoImplicit false

namespace TestsSecurity.SumcheckReference

open ZkcSecurity.Families.Sumcheck
open Zkc.Polynomial.Multilinear
open OracleComp OracleSpec
open scoped ENNReal

section Reuse
variable {F : Type} [Field F] {n : Nat}

theorem table_honest_step (table : Table F (n + 1)) (r : F) :
    (Message.endpoints F).boundary (Zkc.Protocols.Sumcheck.Multilinear.honestMessage table) =
        (TableReference.data F).total table ∧
      (Message.endpoints F).evaluate (Zkc.Protocols.Sumcheck.Multilinear.honestMessage table) r =
        (TableReference.data F).total ((TableReference.data F).restrict table r) ∧
      (TableReference.data F).admissible ((TableReference.data F).restrict table r) :=
  honest_round TableReference.laws Message.endpoints_laws table trivial _
    (TableReference.honest_polynomial table) r r rfl

theorem factor_honest_step (s : (FactorReference.data F).State (n + 1)) (r : F) :
    (Message.coefficients F).boundary
        (Zkc.Protocols.Sumcheck.roundPolynomial (productCoefficients _ s.1 s.2)) =
        (FactorReference.data F).total s ∧
      (Message.coefficients F).evaluate
        (Zkc.Protocols.Sumcheck.roundPolynomial (productCoefficients _ s.1 s.2)) r =
        (FactorReference.data F).total ((FactorReference.data F).restrict s r) ∧
      (FactorReference.data F).admissible ((FactorReference.data F).restrict s r) :=
  honest_round FactorReference.laws Message.coefficients_laws s trivial _
    (FactorReference.honest_polynomial s) r r rfl

theorem every_prefix_admissible (count : Nat) (table : Table F (n + count))
    (challenges : Fin count → F) :
    (TableReference.data F).admissible
      ((TableReference.data F).restrictPrefix count table challenges) :=
  Reference.admissible_restrictPrefix TableReference.laws count table challenges trivial

theorem factor_every_prefix_admissible (count : Nat)
    (s : (FactorReference.data F).State (n + count)) (challenges : Fin count → F) :
    (FactorReference.data F).admissible
      ((FactorReference.data F).restrictPrefix count s challenges) :=
  Reference.admissible_restrictPrefix FactorReference.laws count s challenges trivial

variable [Fintype F] [DecidableEq F] [SampleableType F]

/-- The same table laws prove the attacker step without honest-message equality. -/
theorem table_arbitrary_message (table : Table F (n + 1)) (claim : F)
    (wrong : claim ≠ booleanSum table) (m : F × F) (checked : m.1 + m.2 = claim) :
    Pr{let r ← $ᵗ F}[(Message.endpoints F).evaluate m r = booleanSum (fixFirst table r)] ≤
      1 / (Fintype.card F : ℝ≥0∞) := by
  simpa only [max_self, Nat.cast_one] using
    escape_uniform_le TableReference.laws Message.endpoints_laws table trivial claim wrong m checked

theorem factor_arbitrary_message (s : (FactorReference.data F).State (n + 1)) (claim : F)
    (wrong : claim ≠ (FactorReference.data F).total s)
    (m : Zkc.Protocols.AlgebraicRounds.Message F) (checked : m.boundary = claim) :
    Pr{let r ← $ᵗ F}[(Message.coefficients F).evaluate m r =
      (FactorReference.data F).total ((FactorReference.data F).restrict s r)] ≤
      2 / (Fintype.card F : ℝ≥0∞) := by
  simpa only [max_self, Nat.cast_ofNat] using
    escape_uniform_le FactorReference.laws Message.coefficients_laws s trivial claim wrong m checked

/-- Mixed degrees are safe only at the maximum of both actual degree bounds. -/
theorem quadratic_attacker_affine_reference (table : Table F (n + 1)) (claim : F)
    (wrong : claim ≠ booleanSum table) (m : F × F × F)
    (checked : (Message.coefficientTriples F).boundary m = claim) :
    Pr{let r ← $ᵗ F}[(Message.coefficientTriples F).evaluate m r = booleanSum (fixFirst table r)] ≤
      2 / (Fintype.card F : ℝ≥0∞) := by
  simpa only [show max 2 1 = 2 from rfl, Nat.cast_ofNat] using
    escape_uniform_le TableReference.laws Message.coefficientTriples_laws
      table trivial claim wrong m checked

end Reuse

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev K := ZMod 7

/-- A false input still has an admissible reference. -/
theorem false_input_reference_exists :
    (1 : K) ≠ (TableReference.data K).total (fun _ : Fin 1 → Bool => 0) ∧
      (TableReference.data K).admissible (fun _ : Fin 1 → Bool => 0) := by
  constructor
  · change (1 : K) ≠ 0 + 0
    decide +kernel
  · trivial

theorem boolean_agreement : ∀ b : Bool,
    (if b then (1 : K) else 0) = (if b then (1 : K) else 0) ^ 2 := by
  intro b
  cases b <;> decide +kernel

/-- Agreement on the Boolean cube does not determine future observations. -/
theorem off_cube_disagreement : (2 : K) ≠ (2 : K) ^ 2 := by decide +kernel

def coordinate : Table K 1 := fun bits => if bits 0 then 1 else 0

/-- Extending the product table gives X, while restricting both factors gives
X². Their sums agree initially, but their off-cube residual observations differ. -/
theorem product_table_is_not_factor_reference :
    (TableReference.data K).total
      ((TableReference.data K).restrict (fun bits => coordinate bits * coordinate bits) 2) ≠
    (FactorReference.data K).total
      ((FactorReference.data K).restrict (coordinate, coordinate) 2) := by
  change ((1 - 2) * (0 * 0) + 2 * (1 * 1) : K) ≠
    ((1 - 2) * 0 + 2 * 1) * ((1 - 2) * 0 + 2 * 1)
  decide +kernel

theorem endpoint_values_are_not_coefficients :
    (Message.endpoints K).evaluate (1, 2) 1 ≠
      (Message.coefficientTriples K).evaluate (1, 2, 0) 1 := by
  change ((1 - 1) * 1 + 1 * 2 : K) ≠ 1 + (2 * 1 + 0 * (1 * 1))
  decide +kernel

theorem endpoint_boundary_is_not_coefficient_boundary :
    (Message.endpoints K).boundary (1, 2) ≠
      (Message.coefficientTriples K).boundary (1, 2, 0) := by
  change (1 + 2 : K) ≠ (1 + (2 * 0 + 0 * (0 * 0))) + (1 + (2 * 1 + 0 * (1 * 1)))
  decide +kernel

/-- A quadratic message can meet a cubic reference at three challenges, even
though their boundary sums differ (3 versus 1). -/
theorem missing_reference_degree :
    (Finset.univ.filter (fun r : K => 3 + 2 * r + 2 * r ^ 2 = r ^ 3)).card = 3 := by
  decide +kernel

/-- Reversing the roles shows that bounding only the reference also fails. -/
theorem missing_message_degree :
    (Finset.univ.filter (fun r : K => r ^ 3 = 3 + 2 * r + 2 * r ^ 2)).card = 3 := by
  decide +kernel

theorem degree_counterexample_false_boundary : (3 : K) ≠ 1 := by decide +kernel

theorem six_is_even_but_restricts_to_odd :
    (List.replicate 6 (0 : K)).length % 2 = 0 ∧
      (restrictValues (List.replicate 6 (0 : K)) 2).length = 3 ∧
      (restrictValues (List.replicate 6 (0 : K)) 2).length % 2 ≠ 0 := by
  decide +kernel

theorem six_rejected_by_exact_shape :
    (ofList? 2 (List.replicate 6 (0 : K))).isSome = false := by decide +kernel

theorem three_rejected_after_bad_fold :
    (ofList? 1 (restrictValues (List.replicate 6 (0 : K)) 2)).isSome = false := by decide +kernel

/-- Two disjoint singleton escape sets have union size two, not one. -/
theorem shared_challenge_maximum_fails :
    (Finset.univ.filter (fun r : K => r = 0 ∨ r = 1)).card >
      max (Finset.univ.filter (fun r : K => r = 0)).card
        (Finset.univ.filter (fun r : K => r = 1)).card := by decide +kernel

noncomputable local instance : SampleableType K := SampleableType.ofFintype K

theorem shared_challenge_union_probability :
    Pr{let r ← $ᵗ K}[r = 0 ∨ r = 1] ≤
      1 / (Fintype.card K : ℝ≥0∞) + 1 / (Fintype.card K : ℝ≥0∞) := by
  apply shared_challenge_union_le
  · rw [SampleableType.prEvent_uniformSample]
    have count : (Finset.univ.filter (fun r : K => r = 0)).card = 1 := by decide +kernel
    rw [count, Nat.cast_one]
  · rw [SampleableType.prEvent_uniformSample]
    have count : (Finset.univ.filter (fun r : K => r = 1)).card = 1 := by decide +kernel
    rw [count, Nat.cast_one]

theorem shared_challenge_maximum_probability_fails :
    ¬ Pr{let r ← $ᵗ K}[r = 0 ∨ r = 1] ≤
      max (1 / (Fintype.card K : ℝ≥0∞)) (1 / (Fintype.card K : ℝ≥0∞)) := by
  rw [max_self, SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter (fun r : K => r = 0 ∨ r = 1)).card = 2 := by decide +kernel
  rw [count]
  norm_num
  rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  norm_num

/-- Message choice after seeing the challenge escapes at six of seven points;
the fresh uniform theorem fixes the message before the sample. -/
theorem post_challenge_message_selection_fails :
    (Finset.univ.filter (fun r : K =>
      ∃ a b : K, a + b = 1 ∧ (1 - r) * a + r * b = 0)).card = 6 := by
  decide +kernel

def dependentWeight (r : K) : Table K 0 := fun _ => r

theorem active_independence_is_required : ¬ FactorReference.ActiveIndependent dependentWeight := by
  intro independent
  have bad := independent 1 Fin.elim0
  exact one_ne_zero bad

theorem dependent_weight_breaks_evaluation :
    (FactorReference.weightedMessage (dependentWeight 0)
      (fun _ : Fin 1 → Bool => 1) (fun _ : Fin 1 → Bool => 1)).evaluate 1 ≠
      booleanSum (fun bits => dependentWeight 1 bits *
        (fixFirst (fun _ : Fin 1 → Bool => (1 : K)) 1 bits *
          fixFirst (fun _ : Fin 1 → Bool => (1 : K)) 1 bits)) := by
  change (0 + (0 * 1 + 0 * (1 * 1)) : K) ≠
    1 * (((1 - 1) * 1 + 1 * 1) * ((1 - 1) * 1 + 1 * 1))
  decide +kernel

#print axioms ZkcSecurity.Families.Sumcheck.escape_uniform_le
#print axioms ZkcSecurity.Families.Sumcheck.honest_round
#print axioms ZkcSecurity.Families.Sumcheck.TableReference.laws
#print axioms ZkcSecurity.Families.Sumcheck.FactorReference.laws
#print axioms ZkcSecurity.Families.Sumcheck.FactorReference.weighted_evaluation

end TestsSecurity.SumcheckReference
