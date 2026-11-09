module

public import Zkc.Protocol.Library.Families.Stark.ConstraintBatching

@[expose] public section

/-! Identity tests with candidates chosen between challenges.

Constraint polynomials are fixed before batching. Quotient candidates may depend
on the batching challenge, but must be fixed before the evaluation challenge.
The list event is simultaneous, so the final choice among candidates may depend
on the evaluation point. Application relations and candidate-list coverage are
separate mathematical obligations.
-/

namespace ZkcSecurity.Families.Stark
open Polynomial OracleComp
open scoped BigOperators ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] {count : ℕ}

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Evaluating the constraints at one point commutes with power batching. -/
theorem powerBatch_constants (polynomials : Fin count → F[X]) (challenge point : F) :
    powerBatch (fun i ↦ C ((polynomials i).eval point)) challenge =
      C ((powerBatch polynomials challenge).eval point) := by
  rw [powerBatch_eval]
  simp only [powerBatch, map_sum, map_mul]

/-- A nonzero constraint value at a fixed domain point prevents every quotient
identity except at a bounded set of batching challenges. The quotient is allowed
to be chosen after that challenge, and no quotient degree assumption is needed. -/
theorem batch_at_domain_uniform_le (polynomials : Fin count → F[X]) (point : F)
    (invalid : ∃ i, (polynomials i).eval point ≠ 0) :
    Pr{let challenge ← $ᵗ F}[(powerBatch polynomials challenge).eval point = 0] ≤
      ((count - 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  have invalidConstants : ∃ i, C ((polynomials i).eval point) ≠ (0 : F[X]) := by
    obtain ⟨i, hi⟩ := invalid
    exact ⟨i, by simpa using hi⟩
  simpa only [powerBatch_constants, C_eq_zero] using
    powerBatch_zero_uniform_le (fun i ↦ C ((polynomials i).eval point)) invalidConstants

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Domain violation rules out a zero residual for every supplied quotient. -/
theorem residual_ne_zero_of_domain_violation (domain : Finset F) (numerator quotient : F[X])
    {point : F} (member : point ∈ domain) (invalid : numerator.eval point ≠ 0) :
    residual domain numerator quotient ≠ 0 := by
  intro zero
  have equality := congrArg (fun p : F[X] ↦ p.eval point) zero
  simp only [residual, eval_sub, eval_mul, eval_zero,
    (vanishing_eval_zero_iff domain point).mpr member, zero_mul, sub_zero] at equality
  exact invalid equality

omit [Fintype F] [SampleableType F] in
/-- Root counting simultaneously covers every member of a fixed finite family.
There is no assumption that the adversary selects a family member before the draw. -/
theorem candidate_roots_uniform_le {Candidate : Type} (candidates : Finset Candidate)
    (polynomial : Candidate → F[X])
    (nonzero : ∀ c ∈ candidates, polynomial c ≠ 0)
    {degree : ℕ} (bounded : ∀ c ∈ candidates, (polynomial c).natDegree ≤ degree)
    (points : Finset F) [SampleableType ↥points] :
    Pr{let x ← $ᵗ ↥points}[∃ c ∈ candidates, (polynomial c).eval (x : F) = 0] ≤
      candidates.card * ((degree : ℝ≥0∞) / points.card) := by
  apply prEvent_exists_finset_le_card_mul
  intro c hc
  exact (roots_on_set_uniform_le points (polynomial c) (nonzero c hc)).trans
    (ENNReal.div_le_div_right (by exact_mod_cast bounded c hc) _)

/-- Adaptive quotient lists: batching precedes quotient selection and then a
fresh uniform evaluation draw. Every accepted candidate is covered, even when
its final selection follows that draw. The list bound includes the empty list. -/
theorem adaptive_quotient_candidates_uniform_le
    (domain : Finset F) (polynomials : Fin count → F[X])
    (invalid : ∃ point ∈ domain, ∃ i, (polynomials i).eval point ≠ 0)
    (quotients : F → Finset F[X]) {listBound degree : ℕ}
    (size : ∀ challenge, (quotients challenge).card ≤ listBound)
    (bounded : ∀ challenge q, q ∈ quotients challenge →
      (residual domain (powerBatch polynomials challenge) q).natDegree ≤ degree)
    (points : Finset F) [SampleableType ↥points] :
    Pr{let challenge ← $ᵗ F; let x ← $ᵗ ↥points}[
      ∃ q ∈ quotients challenge,
        (residual domain (powerBatch polynomials challenge) q).eval (x : F) = 0] ≤
      ((count - 1 : ℕ) : ℝ≥0∞) / Fintype.card F +
        listBound * ((degree : ℝ≥0∞) / points.card) := by
  obtain ⟨point, member, invalid⟩ := invalid
  have step := prEvent_bind_le_prEvent_add_of_support ($ᵗ F)
    (fun challenge ↦ (fun x : points ↦ (challenge, x)) <$> ($ᵗ ↥points))
    (fun challenge ↦ (powerBatch polynomials challenge).eval point = 0)
    (fun result : F × points ↦ ∃ q ∈ quotients result.1,
      (residual domain (powerBatch polynomials result.1) q).eval (result.2 : F) = 0)
    (ε := listBound * ((degree : ℝ≥0∞) / points.card)) (by
      intro challenge _ notZero
      have roots := candidate_roots_uniform_le (quotients challenge)
        (fun q ↦ residual domain (powerBatch polynomials challenge) q)
        (fun q _ ↦ residual_ne_zero_of_domain_violation domain _ q member notZero)
        (bounded challenge) points
      have cardBound : ((quotients challenge).card : ℝ≥0∞) ≤ listBound := by
        exact_mod_cast size challenge
      simpa only [prEvent_map, Function.comp_def] using
        roots.trans (mul_le_mul cardBound le_rfl zero_le zero_le))
  simpa only [map_bind, Functor.map_map, Function.comp_def] using
    step.trans (add_le_add (batch_at_domain_uniform_le polynomials point invalid) le_rfl)

/-- Trace candidates are fixed before batching; quotient candidates may depend
on both the selected trace and the batching challenge. A union bound accounts
for every possible trace, including a trace selected after both challenges. -/
theorem trace_quotient_candidates_uniform_le {Trace : Type}
    (traces : Finset Trace) (domain : Finset F) (polynomials : Trace → Fin count → F[X])
    (invalid : ∀ trace ∈ traces, ∃ point ∈ domain, ∃ i,
      (polynomials trace i).eval point ≠ 0)
    (quotients : Trace → F → Finset F[X]) {listBound degree : ℕ}
    (size : ∀ trace ∈ traces, ∀ challenge, (quotients trace challenge).card ≤ listBound)
    (bounded : ∀ trace ∈ traces, ∀ challenge q, q ∈ quotients trace challenge →
      (residual domain (powerBatch (polynomials trace) challenge) q).natDegree ≤ degree)
    (points : Finset F) [SampleableType ↥points] :
    Pr{let challenge ← $ᵗ F; let x ← $ᵗ ↥points}[
      ∃ trace ∈ traces, ∃ q ∈ quotients trace challenge,
        (residual domain (powerBatch (polynomials trace) challenge) q).eval (x : F) = 0] ≤
      traces.card * (((count - 1 : ℕ) : ℝ≥0∞) / Fintype.card F +
        listBound * ((degree : ℝ≥0∞) / points.card)) := by
  have union := prEvent_exists_finset_le_card_mul traces
    ((fun (challenge : F) (x : points) ↦ (challenge, x)) <$> ($ᵗ F) <*> ($ᵗ ↥points))
    (fun trace result ↦ ∃ q ∈ quotients trace result.1,
      (residual domain (powerBatch (polynomials trace) result.1) q).eval (result.2 : F) = 0)
    (ε := ((count - 1 : ℕ) : ℝ≥0∞) / Fintype.card F +
      listBound * ((degree : ℝ≥0∞) / points.card)) (by
      intro trace member
      simpa only [seq_eq_bind_map, map_bind, bind_map_left, Functor.map_map, prEvent_map,
        Function.comp_def] using adaptive_quotient_candidates_uniform_le domain
          (polynomials trace) (invalid trace member) (quotients trace)
          (size trace member) (bounded trace member) points)
  simpa only [seq_eq_bind_map, map_bind, bind_map_left, Functor.map_map, prEvent_map,
    Function.comp_def] using union

/-- If acceptance would force a zero residual for each compatible candidate
assignment, absence of candidate collisions forces universal disagreement at
some component. This keeps the quantifiers needed by quotient separation. -/
theorem exists_component_disagrees_of_no_candidate_collision
    {Component : Type} {Candidate : Component → Type} {Claims : Type}
    (allowed : ∀ i, Set (Candidate i))
    (compatible : ∀ i, Candidate i → Claims → Prop) (claims : Claims)
    (collision : (∀ i, Candidate i) → Prop)
    (acceptance : ∀ chosen, (∀ i, chosen i ∈ allowed i) →
      (∀ i, compatible i (chosen i) claims) → collision chosen)
    (noCollision : ∀ chosen, (∀ i, chosen i ∈ allowed i) → ¬ collision chosen) :
    ∃ i, ∀ c ∈ allowed i, ¬ compatible i c claims := by
  classical
  by_contra h
  push Not at h
  choose chosen member agrees using h
  exact noCollision chosen member (acceptance chosen member agrees)

end ZkcSecurity.Families.Stark
