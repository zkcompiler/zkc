module

public import ZkcSecurity.Commitment.Experiment

@[expose] public section

/-! # Charges of hash computations and reshaped schemes

* `liftHash_queryBound` and `liftHash_costBound`: a hash computation with at most `n` calls, run on
  the joint oracle, makes at most `n` calls and is charged at most `n · hashError`.
* `Extractable.comap`: an extractable scheme read through a map of shapes, for verifiers whose
  commitments all have shapes of one family (for example one fixed tree depth).
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment

open OracleComp OracleSpec

variable {E Shape Shape' Value Query Y α : Type} {Raw : E → Type}

theorem liftHash_queryBound :
    ∀ (computation : OracleComp (Query →ₒ Y) α) (bound : ℕ), IsTotalQueryBound computation bound →
      IsTotalQueryBound (liftHash Raw Shape computation) bound := by
  intro computation
  induction computation using OracleComp.inductionOn with
  | pure value => intro _ _; trivial
  | query_bind query next ih =>
      intro bound bounded
      rw [isTotalQueryBound_query_bind_iff] at bounded
      simp only [liftHash, simulateQ_bind, simulateQ_spec_query, hashCall] at ih ⊢
      exact (isTotalQueryBound_query_bind_iff (spec := joint Raw Shape Y Query)
        (t := Sum.inr query)).mpr ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩

theorem liftHash_costBound (error : E → ENNReal) (hashError : ENNReal) :
    ∀ (computation : OracleComp (Query →ₒ Y) α) (bound : ℕ), IsTotalQueryBound computation bound →
      WorstCaseCostBound (liftHash Raw Shape computation)
        ⟨jointError (Shape := Shape) (Y := Y) (Query := Query) error hashError⟩
        (bound * hashError) := by
  intro computation
  induction computation using OracleComp.inductionOn with
  | pure value => intro _ _; exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | query_bind query next ih =>
      intro bound bounded
      rw [isTotalQueryBound_query_bind_iff] at bounded
      simp only [liftHash, simulateQ_bind, simulateQ_spec_query, hashCall] at ih ⊢
      refine (worstCaseCostBound_query_bind_iff (spec := joint Raw Shape Y Query) (Sum.inr query)
        _ _ _).mpr ?_
      intro reply cost member
      have tail := (worstCaseCostBound_iff_support_bound _ _ _).mp (ih reply _ (bounded.2 reply))
        cost member
      obtain ⟨count, rfl⟩ : ∃ count, bound = count + 1 := ⟨bound - 1, by omega⟩
      refine (add_le_add (le_refl _) tail).trans (le_of_eq ?_)
      show hashError + ((count + 1 - 1 : ℕ) : ENNReal) * hashError =
        ((count + 1 : ℕ) : ENNReal) * hashError
      rw [Nat.add_sub_cancel]
      push_cast
      ring

/-- An extractable scheme read through a map of shapes. -/
def Extractable.comap (scheme : Extractable Shape Value Query Y) (shapeOf : Shape' → Shape) :
    Extractable Shape' Value Query Y where
  authenticate shape := scheme.authenticate (shapeOf shape)
  extract log shape := scheme.extract log (shapeOf shape)
  inputs := scheme.inputs
  opening_agrees answer log shape := scheme.opening_agrees answer log (shapeOf shape)
  extract_append log entry shape := scheme.extract_append log entry (shapeOf shape)

end ZkcSecurity.Commitment
