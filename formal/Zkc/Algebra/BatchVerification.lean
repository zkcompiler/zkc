import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.BigOperators

/-! Exact fibers of a batch equation with one nonzero fixed residual.
    This is the algebra/count core, not a native verifier or RNG theorem. -/
set_option autoImplicit false

namespace Zkc.Algebra.BatchVerification

variable {K I : Type} [Field K]

theorem fixed_error_injective (e c : K) (he : e ≠ 0) :
    Function.Injective (fun a : K => a * e + c) := by
  intro a b hab
  exact mul_right_cancel₀ he (add_right_cancel hab)

theorem unique_cancelling_coefficient (e c : K) (he : e ≠ 0) :
    ∃! a : K, a * e + c = 0 := by
  refine ⟨-c / e, ?_, ?_⟩
  · dsimp
    rw [div_mul_cancel₀ _ he, neg_add_cancel]
  · intro a ha
    apply fixed_error_injective e c he
    dsimp
    rw [ha, div_mul_cancel₀ _ he, neg_add_cancel]

/-- The remaining contribution may be any fixed function of the other coins.
    It cannot depend on the distinguished coefficient. -/
def acceptingEquiv (e : K) (he : e ≠ 0) (rest : (I → K) → K) :
    {a : K × (I → K) // a.1 * e + rest a.2 = 0} ≃ (I → K) where
  toFun a := a.val.2
  invFun b := ⟨(-rest b / e, b), by
    dsimp
    rw [div_mul_cancel₀ _ he, neg_add_cancel]⟩
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · exact ((unique_cancelling_coefficient e (rest a.val.2) he).unique
        (by rw [div_mul_cancel₀ _ he, neg_add_cancel]) a.property)
    · rfl
  right_inv _ := rfl

/-- For m = 1 + card I independent uniform coefficients, there are exactly
    |K|^(m-1) accepting choices, among |K|^m total choices. -/
theorem exact_accepting_count [Fintype K] [Fintype I] [DecidableEq K] [DecidableEq I]
    (e : K) (he : e ≠ 0) (rest : (I → K) → K) :
    Fintype.card {a : K × (I → K) // a.1 * e + rest a.2 = 0}
      = Fintype.card K ^ Fintype.card I := by
  rw [Fintype.card_congr (acceptingEquiv e he rest)]
  exact Fintype.card_fun

theorem exact_linear_batch_count [Fintype K] [Fintype I]
    [DecidableEq K] [DecidableEq I] (e : K) (he : e ≠ 0) (errors : I → K) :
    Fintype.card {a : K × (I → K) // a.1 * e + ∑ i, a.2 i * errors i = 0}
      = Fintype.card K ^ Fintype.card I :=
  exact_accepting_count e he (fun b => ∑ i, b i * errors i)

end Zkc.Algebra.BatchVerification
