import Composition.Multilinear
import Zkc.Protocols.Sumcheck.Execution
import Zkc.Semantics.Relation
import Mathlib.Tactic.LinearCombination

/-! Two fixed evaluation claims at arbitrary ordered points reduce, through
arbitrarily many adaptive sumcheck rounds, to actual opening obligations at
one point. The verifier never receives either table. Ordinary soundness is
conditional on a sound terminal checker and independent uniform challenges. -/

set_option autoImplicit false

namespace Composition.Claims

open PIR Zkc.Polynomial Zkc.Probability Zkc.Protocols.Sumcheck
open AdaptiveTape (Tape)
open scoped BigOperators

structure Claim (Id F : Type) (n : Nat) where
  object : Id
  point : Fin n → F
  value : F

variable {Id F : Type} {n : Nat} [Field F] [DecidableEq F]

def Holds (env : Id → Table F n) (c : Claim Id F n) : Prop :=
  (env c.object).eval c.point = c.value

def AllHold (env : Id → Table F n) (claims : List (Claim Id F n)) : Prop :=
  ∀ c ∈ claims, Holds env c

def aggregate (env : Id → Table F n) (a b : Claim Id F n) (α : F) : Quadratic F n :=
  Quadratic.add ((env a.object).weighted a.point)
    (Quadratic.scale α ((env b.object).weighted b.point))

def scalar (a b : Claim Id F n) (α : F) : F := a.value + α * b.value

omit [DecidableEq F] in
theorem aggregate_sum (env : Id → Table F n) (a b : Claim Id F n) (α : F) :
    (aggregate env a b α).booleanSum =
      (env a.object).eval a.point + α * (env b.object).eval b.point := by
  simp [aggregate, Quadratic.booleanSum_add, Quadratic.booleanSum_scale, Table.weighted_sum]

structure Result (F : Type) (n : Nat) where
  point : Fin n → F
  value : F

def openings (a b : Claim Id F n) (result : Result F n) (values : F × F) :
    List (Claim Id F n) :=
  [⟨a.object, result.point, values.1⟩, ⟨b.object, result.point, values.2⟩]

omit [DecidableEq F] in
theorem openings_hold (env : Id → Table F n) (a b : Claim Id F n)
    (result : Result F n) (values : F × F) :
    AllHold env (openings a b result values) ↔
      (env a.object).eval result.point = values.1 ∧
      (env b.object).eval result.point = values.2 := by
  simp [AllHold, openings, Holds]

def valueCheck (a b : Claim Id F n) (α : F) (result : Result F n) (values : F × F) : Bool :=
  decide (result.value = Table.eqWeight n a.point result.point * values.1 +
    α * (Table.eqWeight n b.point result.point * values.2))

/-- The second component consumes the actual result returned by the first. -/
def finish (a b : Claim Id F n) (α : F) (result : Result F n) (values : F × F) :
    Option (List (Claim Id F n)) :=
  if valueCheck a b α result values then some (openings a b result values) else none

theorem opening_reduction (env : Id → Table F n) (a b : Claim Id F n) (α : F)
    (result : Result F n) (values : F × F) (passes : valueCheck a b α result values = true) :
    Relation.ReductionContract (fun r => r.value = (aggregate env a b α).eval r.point)
      (AllHold env) result (openings a b result values) False := by
  refine ⟨fun holds => Or.inl ?_⟩
  rw [openings_hold] at holds
  simpa only [valueCheck, decide_eq_true_eq, aggregate, Quadratic.eval_add,
    Quadratic.eval_scale, Table.weighted_eval, holds.1, holds.2] using passes

/-- Reuse the maintained effectful rounds; there is no polynomial input. -/
def rounds (count : Nat) (claim : F) : Proc (Zkc.Protocols.AlgebraicRounds.interface F) (Result F count) :=
  (Source.rounds count ⟨claim, []⟩).bind fun acc =>
    if acc.challenges.length = count then .done ⟨coordinates count acc.challenges, acc.claim⟩
    else .halt .refused

theorem rounds_outcome {S : Type} (send : S → Zkc.Protocols.AlgebraicRounds.Message F × S)
    (react : S → F → S) (count : Nat) (claim : F) (prover : S) (coins : Tape F count) :
    ((rounds count claim).run (Zkc.Protocols.Sumcheck.Execution.handler send react)
      (prover, tapeList count coins)).outcome =
      match finalClaim (Zkc.Protocols.Sumcheck.Execution.strategy send react count prover) claim coins with
      | none => .stopped .reject
      | some value => .returned ⟨tapePoint count coins, value⟩ := by
  rw [rounds, PIR.run_bind]
  simp only [PIR.Execution.follow]
  rw [Zkc.Protocols.Sumcheck.Execution.rounds_outcome]
  cases finalClaim (Zkc.Protocols.Sumcheck.Execution.strategy send react count prover) claim coins <;>
    simp [tapeList_ofFn, coordinates_ofFn, Proc.run]

def BatchCollision (env : Id → Table F n) (a b : Claim Id F n) (α : F) : Prop :=
  ¬ (Holds env a ∧ Holds env b) ∧ scalar a b α = (aggregate env a b α).booleanSum

def RoundCollision (p : Quadratic F n) (claim : F) (strategy : Strategy F n)
    (coins : Tape F n) : Prop :=
  claim ≠ p.booleanSum ∧ verify p claim strategy coins = true

omit [DecidableEq F] in
theorem batch_reduction (env : Id → Table F n) (a b : Claim Id F n) (α : F) :
    Relation.ReductionContract (fun _ : Unit => Holds env a ∧ Holds env b)
      (fun value => value = (aggregate env a b α).booleanSum) () (scalar a b α)
      (BatchCollision env a b α) := by
  refine ⟨fun same => ?_⟩
  by_cases valid : Holds env a ∧ Holds env b
  · exact Or.inl valid
  · exact Or.inr ⟨valid, same⟩

theorem round_reduction (p : Quadratic F n) (claim : F) (strategy : Strategy F n)
    (coins : Tape F n) (value : F) (receipt : finalClaim strategy claim coins = some value) :
    Relation.ReductionContract (fun c => c = p.booleanSum)
      (fun r : Result F n => r.value = p.eval r.point) claim ⟨tapePoint n coins, value⟩
      (RoundCollision p claim strategy coins) := by
  refine ⟨fun terminal => ?_⟩
  by_cases valid : claim = p.booleanSum
  · exact Or.inl valid
  · exact Or.inr ⟨valid, (verify_iff_final p claim strategy coins).mpr (terminal ▸ receipt)⟩

theorem composed_reduction (env : Id → Table F n) (a b : Claim Id F n) (α : F)
    (strategy : Strategy F n) (coins : Tape F n) (value : F) (values : F × F)
    (receipt : finalClaim strategy (scalar a b α) coins = some value)
    (passes : valueCheck a b α ⟨tapePoint n coins, value⟩ values = true) :
    Relation.ReductionContract (fun _ : Unit => Holds env a ∧ Holds env b)
      (AllHold env) () (openings a b ⟨tapePoint n coins, value⟩ values)
      ((BatchCollision env a b α ∨
        RoundCollision (aggregate env a b α) (scalar a b α) strategy coins) ∨ False) :=
  ((batch_reduction env a b α).then
    (round_reduction (aggregate env a b α) (scalar a b α) strategy coins value receipt)).then
      (opening_reduction env a b α _ values passes)

/-- Terminal checking is explicit. Returned obligations are not acceptance.
Replies may depend on the whole completed tape. -/
def accepted (a b : Claim Id F n) (α : F) (strategy : Strategy F n) (coins : Tape F n)
    (values : F × F) (terminal : List (Claim Id F n) → Bool) : Bool :=
  match finalClaim strategy (scalar a b α) coins with
  | none => false
  | some value => valueCheck a b α ⟨tapePoint n coins, value⟩ values &&
      terminal (openings a b ⟨tapePoint n coins, value⟩ values)

theorem accepted_implies_verify (env : Id → Table F n) (a b : Claim Id F n) (α : F)
    (strategy : Strategy F n) (coins : Tape F n) (values : F × F)
    (terminal : List (Claim Id F n) → Bool)
    (soundTerminal : ∀ claims, terminal claims = true → AllHold env claims)
    (passes : accepted a b α strategy coins values terminal = true) :
    verify (aggregate env a b α) (scalar a b α) strategy coins = true := by
  unfold accepted at passes
  cases receipt : finalClaim strategy (scalar a b α) coins with
  | none => simp [receipt] at passes
  | some value =>
      rw [receipt, Bool.and_eq_true] at passes
      have equation := (opening_reduction env a b α _ values passes.1).sound
        (soundTerminal _ passes.2)
      rcases equation with equation | impossible
      · exact (verify_iff_final _ _ _ _).mpr (equation ▸ receipt)
      · exact impossible.elim

theorem honest_complete (env : Id → Table F n) (a b : Claim Id F n)
    (valid : Holds env a ∧ Holds env b) (α : F) (coins : Tape F n)
    (terminal : List (Claim Id F n) → Bool)
    (completeTerminal : ∀ claims, AllHold env claims → terminal claims = true) :
    accepted a b α (honest (aggregate env a b α)) coins
      ((env a.object).eval (tapePoint n coins), (env b.object).eval (tapePoint n coins)) terminal = true := by
  have same : scalar a b α = (aggregate env a b α).booleanSum := by
    rw [aggregate_sum]; exact congrArg₂ (fun x y => x + α * y) valid.1.symm valid.2.symm
  have receipt := (verify_iff_final _ _ _ _).mp (completeness (aggregate env a b α) coins)
  simp only [accepted, same, receipt, Bool.and_eq_true]
  constructor
  · simp [valueCheck, aggregate, Quadratic.eval_add, Quadratic.eval_scale, Table.weighted_eval]
  · exact completeTerminal _ ((openings_hold _ _ _ _ _).mpr ⟨rfl, rfl⟩)

/-- The algebraic contract consumes a receipt of the maintained effectful
rounds and the bundle actually returned by finish, rather than a chosen bundle. -/
theorem source_reduction {S : Type} (env : Id → Table F n) (a b : Claim Id F n) (α : F)
    (send : S → Zkc.Protocols.AlgebraicRounds.Message F × S) (react : S → F → S)
    (prover : S) (coins : Tape F n) (result : Result F n) (values : F × F)
    (bundle : List (Claim Id F n))
    (receipt : ((rounds n (scalar a b α)).run (Zkc.Protocols.Sumcheck.Execution.handler send react)
      (prover, tapeList n coins)).outcome = .returned result)
    (finished : finish a b α result values = some bundle) :
    Relation.ReductionContract (fun _ : Unit => Holds env a ∧ Holds env b)
      (AllHold env) () bundle
      ((BatchCollision env a b α ∨ RoundCollision (aggregate env a b α) (scalar a b α)
        (Zkc.Protocols.Sumcheck.Execution.strategy send react n prover) coins) ∨ False) := by
  rw [rounds_outcome] at receipt
  cases claimed : finalClaim (Zkc.Protocols.Sumcheck.Execution.strategy send react n prover) (scalar a b α) coins with
  | none => simp [claimed] at receipt
  | some value =>
      simp only [claimed, Outcome.returned.injEq] at receipt
      subst result
      unfold finish at finished
      split at finished
      next passes =>
        cases Option.some.inj finished
        exact composed_reduction env a b α _ coins value values claimed passes
      next fails => simp at finished

variable [Fintype F]

/-- The source claims are fixed before alpha. -/
theorem batch_collision_card (env : Id → Table F n) (a b : Claim Id F n)
    (invalid : ¬ (Holds env a ∧ Holds env b)) :
    (Finset.univ.filter fun α => scalar a b α = (aggregate env a b α).booleanSum).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro α hα β hβ
  have ha := (Finset.mem_filter.mp hα).2
  have hb := (Finset.mem_filter.mp hβ).2
  rw [aggregate_sum] at ha hb
  unfold scalar at ha hb
  have delta : (α - β) * (b.value - (env b.object).eval b.point) = 0 := by
    linear_combination ha - hb
  rcases mul_eq_zero.mp delta with same | bValid
  · exact sub_eq_zero.mp same
  · have bv : Holds env b := (sub_eq_zero.mp bValid).symm
    have av : Holds env a := by
      unfold Holds at bv ⊢
      rw [bv] at ha
      exact (add_right_cancel ha).symm
    exact (invalid ⟨av, bv⟩).elim

def acceptance (a b : Claim Id F n) (α : F) (strategy : Strategy F n)
    (replies : Tape F n → F × F) (terminal : List (Claim Id F n) → Bool) : ℚ :=
  UniformTape.average n (fun coins => if accepted a b α strategy coins (replies coins) terminal then 1 else 0)

theorem acceptance_le_sumcheck (env : Id → Table F n) (a b : Claim Id F n) (α : F)
    (strategy : Strategy F n) (replies : Tape F n → F × F) (terminal : List (Claim Id F n) → Bool)
    (soundTerminal : ∀ claims, terminal claims = true → AllHold env claims) :
    acceptance a b α strategy replies terminal ≤
      Zkc.Protocols.Sumcheck.acceptance (aggregate env a b α) (scalar a b α) strategy := by
  apply UniformTape.monotone
  intro coins
  by_cases passes : accepted a b α strategy coins (replies coins) terminal = true
  · simp [passes, accepted_implies_verify env a b α strategy coins (replies coins) terminal soundTerminal passes]
  · simp [passes]; split <;> norm_num

set_option maxHeartbeats 800000 in
/-- One batching challenge, then n independent uniform round challenges.
Both strategy and final opening replies may adapt to alpha. -/
theorem soundness (env : Id → Table F n) (a b : Claim Id F n)
    (invalid : ¬ (Holds env a ∧ Holds env b)) (strategies : F → Strategy F n)
    (replies : F → Tape F n → F × F) (terminal : List (Claim Id F n) → Bool)
    (soundTerminal : ∀ claims, terminal claims = true → AllHold env claims) :
    UniformTape.average (F := F) 1 (fun coin =>
      acceptance a b coin.1 (strategies coin.1) (replies coin.1) terminal) ≤
      (1 + 2 * (n : ℚ)) / Fintype.card F := by
  have pointwise (α : F) : acceptance a b α (strategies α) (replies α) terminal ≤
      (if scalar a b α = (aggregate env a b α).booleanSum then (1 : ℚ) else 0) +
        (2 * (n : ℚ)) / Fintype.card F := by
    apply (acceptance_le_sumcheck env a b α _ _ _ soundTerminal).trans
    by_cases same : scalar a b α = (aggregate env a b α).booleanSum
    · rw [if_pos same]
      exact (acceptance_le_one _ _ _).trans (le_add_of_nonneg_right
        (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
          (le_of_lt (UniformTape.card_positive (F := F)))))
    · rw [if_neg same, zero_add]
      exact Zkc.Protocols.Sumcheck.soundness _ _ _ same
  have collisions : ((Finset.univ.filter fun α =>
      scalar a b α = (aggregate env a b α).booleanSum).card : ℚ) ≤ 1 := by
    exact_mod_cast batch_collision_card env a b invalid
  change (∑ α : F, acceptance a b α (strategies α) (replies α) terminal) / Fintype.card F ≤ _
  calc
    _ ≤ (∑ α : F, ((if scalar a b α = (aggregate env a b α).booleanSum then (1 : ℚ) else 0) +
        (2 * (n : ℚ)) / Fintype.card F)) / Fintype.card F :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun α _ => pointwise α))
        (le_of_lt (UniformTape.card_positive (F := F)))
    _ = ((Finset.univ.filter fun α => scalar a b α = (aggregate env a b α).booleanSum).card +
        2 * (n : ℚ)) / Fintype.card F := by
      rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const]
      simp only [Finset.card_univ, nsmul_eq_mul]
      congr 1
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith)
      (le_of_lt (UniformTape.card_positive (F := F)))

end Composition.Claims
