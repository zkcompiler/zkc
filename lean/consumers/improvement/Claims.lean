import Zkc.Semantics.Relation
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Design experiment: cubic reduction, explicit residual openings and batching.

The environment denotes fixed objects for the proof. No verifier function takes
their private coefficients as input. Terminal PCS discharge remains a supplied
contract. This file is outside the maintained protocol API.
-/

set_option autoImplicit false

namespace Improvement.Claims

/-- The point type belongs to the object, so different arities/layouts can use
different point types. Object names acquire meaning only in a fixed environment. -/
structure Claim (Id : Type) (Point : Id → Type) (F : Type) where
  object : Id
  point : Point object
  value : F

def Holds {Id F : Type} {Point : Id → Type}
    (env : (id : Id) → Point id → F) (claim : Claim Id Point F) : Prop :=
  env claim.object claim.point = claim.value

/-- Every residual must be discharged. The ordered list also retains occurrences
for a later transcript/batching interpretation; truth alone ignores permutations. -/
def AllHold {Id F : Type} {Point : Id → Type}
    (env : (id : Id) → Point id → F) (claims : List (Claim Id Point F)) : Prop :=
  ∀ claim ∈ claims, Holds env claim

theorem allHold_append {Id F : Type} {Point : Id → Type}
    (env : (id : Id) → Point id → F) (left right : List (Claim Id Point F)) :
    AllHold env (left ++ right) ↔ AllHold env left ∧ AllHold env right := by
  simp only [AllHold, List.mem_append, or_imp, forall_and]

inductive Object (Id : Type) where
  | base : Id → Object Id
  | product : Id → Id → Id → Object Id

section Cubic
variable {Id F : Type} [Field F]

noncomputable def productPolynomial (env : Id → Polynomial F) (a b c : Id) : Polynomial F :=
  env a * env b * env c

noncomputable def evaluate (env : Id → Polynomial F) : Object Id → F → F
  | .base id, r => (env id).eval r
  | .product a b c, r => (productPolynomial env a b c).eval r

def reducedClaim (a b c : Id) (message : Polynomial F) (r : F) :
    Claim (Object Id) (fun _ => F) F :=
  ⟨.product a b c, r, message.eval r⟩

def booleanSum (p : Polynomial F) : F := p.eval 0 + p.eval 1

/-- Both the semantic degree and the arithmetic boundary check are obligations;
a declared degree label is insufficient. -/
def RoundChecks (claim : F) (message : Polynomial F) : Prop :=
  message.natDegree ≤ 3 ∧ booleanSum message = claim

def Collision (actual message : Polynomial F) (r : F) : Prop :=
  message ≠ actual ∧ message.eval r = actual.eval r

theorem product_degree (env : Id → Polynomial F) (a b c : Id)
    (ha : (env a).natDegree ≤ 1) (hb : (env b).natDegree ≤ 1)
    (hc : (env c).natDegree ≤ 1) :
    (productPolynomial env a b c).natDegree ≤ 3 := by
  exact Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le ha hb) hc

theorem round_reduction (env : Id → Polynomial F) (a b c : Id)
    (claim : F) (message : Polynomial F) (r : F) (checked : RoundChecks claim message) :
    PIR.Relation.ReductionContract
      (fun s => booleanSum (productPolynomial env a b c) = s)
      (Holds (evaluate env)) claim (reducedClaim a b c message r)
      (Collision (productPolynomial env a b c) message r) := by
  refine ⟨?_⟩
  intro residual
  by_cases same : message = productPolynomial env a b c
  · exact Or.inl (same ▸ checked.2)
  · exact Or.inr ⟨same, residual.symm⟩

def openings (a b c : Id) (r x y z : F) : List (Claim (Object Id) (fun _ => F) F) :=
  [⟨.base a, r, x⟩, ⟨.base b, r, y⟩, ⟨.base c, r, z⟩]

/-- Executable verifier arithmetic. It receives reported values, not the object
environment or a direct evaluator for committed polynomials. -/
def productCheck [DecidableEq F] (target x y z : F) : Bool :=
  decide (x * y * z = target)

theorem opening_reduction [DecidableEq F] (env : Id → Polynomial F) (a b c : Id)
    (message : Polynomial F) (r x y z : F)
    (checked : productCheck (message.eval r) x y z = true) :
    PIR.Relation.ReductionContract (Holds (evaluate env)) (AllHold (evaluate env))
      (reducedClaim a b c message r) (openings a b c r x y z) False := by
  refine ⟨?_⟩
  intro residual
  have hx := residual ⟨.base a, r, x⟩ (by simp [openings])
  have hy := residual ⟨.base b, r, y⟩ (by simp [openings])
  have hz := residual ⟨.base c, r, z⟩ (by simp [openings])
  change (env a).eval r = x at hx
  change (env b).eval r = y at hy
  change (env c).eval r = z at hz
  apply Or.inl
  change (env a * env b * env c).eval r = message.eval r
  simpa only [Polynomial.eval_mul, hx, hy, hz, productCheck, decide_eq_true_eq] using checked

/-- Two actual reductions consume exactly the same intermediate claim. -/
theorem composed_reduction [DecidableEq F] (env : Id → Polynomial F) (a b c : Id)
    (claim : F) (message : Polynomial F) (r x y z : F)
    (round : RoundChecks claim message)
    (product : productCheck (message.eval r) x y z = true) :
    PIR.Relation.ReductionContract
      (fun s => booleanSum (productPolynomial env a b c) = s)
      (AllHold (evaluate env)) claim (openings a b c r x y z)
      (Collision (productPolynomial env a b c) message r ∨ False) :=
  (round_reduction env a b c claim message r round).then
    (opening_reduction env a b c message r x y z product)

/-- A contracted PCS may discharge the whole residual bundle. This theorem
does not provide a PCS implementation or its soundness contract. -/
theorem terminal_sound [DecidableEq F] (env : Id → Polynomial F) (a b c : Id)
    (claim : F) (message : Polynomial F) (r x y z : F)
    (round : RoundChecks claim message)
    (product : productCheck (message.eval r) x y z = true)
    (verify : List (Claim (Object Id) (fun _ => F) F) → PIR.Continuation.Terminal Unit)
    (terminal : PIR.Relation.TerminalContract (AllHold (evaluate env)) verify)
    (accepted : verify (openings a b c r x y z) = .accepted ()) :
    booleanSum (productPolynomial env a b c) = claim ∨
      Collision (productPolynomial env a b c) message r := by
  simpa only [or_false] using PIR.Relation.terminal_sound
    (composed_reduction env a b c claim message r x y z round product) verify terminal () accepted

/-- Honest values supply completeness of the two algebraic checks and every
residual claim, for any challenge. This is separate from PCS completeness. -/
theorem honest_complete [DecidableEq F] (env : Id → Polynomial F) (a b c : Id) (r : F)
    (ha : (env a).natDegree ≤ 1) (hb : (env b).natDegree ≤ 1)
    (hc : (env c).natDegree ≤ 1) :
    RoundChecks (booleanSum (productPolynomial env a b c)) (productPolynomial env a b c) ∧
    productCheck ((productPolynomial env a b c).eval r)
      ((env a).eval r) ((env b).eval r) ((env c).eval r) = true ∧
    AllHold (evaluate env)
      (openings a b c r ((env a).eval r) ((env b).eval r) ((env c).eval r)) := by
  refine ⟨⟨product_degree env a b c ha hb hc, rfl⟩, ?_, ?_⟩
  · simp [productCheck, productPolynomial]
  · simp [AllHold, openings, Holds, evaluate]

end Cubic

section Roots
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A fixed pair of distinct degree-three polynomials coincides at at most
three field elements. Sampling/freshness is not a consequence of this count. -/
theorem collision_card (actual message : Polynomial F)
    (ha : actual.natDegree ≤ 3) (hm : message.natDegree ≤ 3) (different : message ≠ actual) :
    (Finset.univ.filter (fun r => message.eval r = actual.eval r)).card ≤ 3 := by
  have nonzero : message - actual ≠ 0 := sub_ne_zero.mpr different
  have roots :
      (Finset.univ.filter (fun r => message.eval r = actual.eval r)).val ⊆
        (message - actual).roots := by
    intro r hr
    apply (Polynomial.mem_roots nonzero).mpr
    have eq := (Finset.mem_filter.mp hr).2
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, sub_eq_zero] using eq
  exact (Polynomial.card_le_degree_of_subset_roots roots).trans
    ((Polynomial.natDegree_sub_le _ _).trans (max_le hm ha))

/-- The uniform probability bound for this fixed-pair collision experiment. -/
theorem collision_mass (actual message : Polynomial F)
    (ha : actual.natDegree ≤ 3) (hm : message.natDegree ≤ 3) (different : message ≠ actual) :
    ((Finset.univ.filter (fun r => message.eval r = actual.eval r)).card : ℚ) /
        Fintype.card F ≤ 3 / (Fintype.card F : ℚ) := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast collision_card actual message ha hm different)
    (Nat.cast_nonneg _)

end Roots

section Batching
variable {F : Type} [Field F]

noncomputable def batchError (e₀ e₁ : F) : Polynomial F :=
  Polynomial.C e₀ + Polynomial.X * Polynomial.C e₁

theorem batchError_nonzero (e₀ e₁ : F) (wrong : e₀ ≠ 0 ∨ e₁ ≠ 0) :
    batchError e₀ e₁ ≠ 0 := by
  intro zero
  have h₀ := congrArg (fun p : Polynomial F => p.coeff 0) zero
  have h₁ := congrArg (fun p : Polynomial F => p.coeff 1) zero
  simp [batchError] at h₀ h₁
  exact wrong.elim (fun h => h h₀) (fun h => h h₁)

/-- Two fixed erroneous claims have at most one cancelling batching challenge.
The errors must belong to the same fixed ordered input bundle for this theorem. -/
theorem fixed_batch_card [Fintype F] [DecidableEq F] (e₀ e₁ : F)
    (wrong : e₀ ≠ 0 ∨ e₁ ≠ 0) :
    (Finset.univ.filter (fun alpha => e₀ + alpha * e₁ = 0)).card ≤ 1 := by
  have roots : (Finset.univ.filter (fun alpha => e₀ + alpha * e₁ = 0)).val ⊆
      (batchError e₀ e₁).roots := by
    intro alpha h
    apply (Polynomial.mem_roots (batchError_nonzero e₀ e₁ wrong)).mpr
    change (batchError e₀ e₁).eval alpha = 0
    rw [batchError, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_C]
    exact (Finset.mem_filter.mp h).2
  apply (Polynomial.card_le_degree_of_subset_roots roots).trans
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · exact (Polynomial.natDegree_mul_le (p := Polynomial.X) (q := Polynomial.C e₁)).trans
      (by simp)

end Batching

section Countermodels

/-- Distinct object identities with equal point/value syntax need not agree. -/
theorem object_identity_matters :
    Holds (fun id : Bool => fun _ : Nat => if id then 2 else 1) ⟨false, 0, 1⟩ ∧
    ¬ Holds (fun id : Bool => fun _ : Nat => if id then 2 else 1) ⟨true, 0, 1⟩ := by
  norm_num [Holds]

/-- Ordered coordinates are semantic: the same arity does not justify swapping. -/
theorem point_order_matters :
    Holds (fun _ : Unit => fun p : Nat × Nat => p.1 + 2 * p.2) ⟨(), (1, 2), 5⟩ ∧
    ¬ Holds (fun _ : Unit => fun p : Nat × Nat => p.1 + 2 * p.2) ⟨(), (2, 1), 5⟩ := by
  norm_num [Holds]

theorem dropping_a_residual_is_unsound :
    AllHold (fun _ : Unit => fun x : Nat => x) [⟨(), 1, 1⟩] ∧
    ¬ AllHold (fun _ : Unit => fun x : Nat => x) [⟨(), 1, 1⟩, ⟨(), 2, 9⟩] := by
  simp [AllHold, Holds]

theorem degree_three_is_needed : (Polynomial.X ^ 3 : Polynomial ℚ).natDegree = 3 := by
  simp

/-- A cubic with the wrong Boolean sum can agree at a particular challenge. -/
theorem unlucky_challenge_is_possible :
    booleanSum (Polynomial.X ^ 3 : Polynomial ℚ) ≠ booleanSum 0 ∧
    (Polynomial.X ^ 3 : Polynomial ℚ).eval 0 = (0 : Polynomial ℚ).eval 0 := by
  norm_num [booleanSum]

/-- A malformed degree-four message must fail the actual degree check. -/
theorem degree_label_is_not_a_proof :
    ¬ RoundChecks (1 : ℚ) (Polynomial.X ^ 4) := by
  simp [RoundChecks]

/-- If errors may depend on the already-known batching challenge, nonzero
errors cancel for every challenge. A root bound for fixed errors cannot apply. -/
theorem adaptive_batching_breaks {F : Type} [Field F] (alpha : F) :
    ∃ e₀ e₁ : F, (e₀ ≠ 0 ∨ e₁ ≠ 0) ∧ e₀ + alpha * e₁ = 0 := by
  exact ⟨-alpha, 1, Or.inr one_ne_zero, by simp⟩

/-- Even fixed nonzero errors can cancel at one point; batched validity does
not imply individual validity deterministically. -/
theorem fixed_batching_needs_a_bad_event :
    (1 : ZMod 5) + 1 * (-1) = 0 ∧ (1 : ZMod 5) ≠ 0 := by
  exact ⟨by ring, by decide⟩

end Countermodels

end Improvement.Claims
