import ZkcSecurity.Transformations.FiatShamir.Obligations
import ZkcSecurityExamples.CommittedOpening
import TestsSecurity.Counterexamples.Support
import Mathlib.Data.ZMod.Basic

/-! Counterexamples for serialization, binding and explicit-input sharing.

- **Padding aliasing (serialization failure).** Absorbing a variable-length
  observation into a block of two coordinates padded with zeros, with no length,
  sends the distinct histories `[1]` and `[1, 0]` to one primitive input
  (`padded_alias`): the encoding is not injective and prefix-free
  (`padded_not_prefixFree`), and the two histories receive equal answers with
  probability one (`aliased_equal`). This refutes serialization, not soundness
  of a particular protocol. Encoding the length first separates them
  (`lengthPrefixed_separates`).
- **A truncated digest claimed as exact binding.** Absorbing an eight-valued
  digest as its low two bits is not injective (`truncated_not_injective`), so it
  can be at most a collision-bounded binding.
- **Duplicate explicit inputs given fresh cells.** Two batch positions with equal
  declared inputs share one cell in the explicit-input construction
  (`shared_shares`), so their evaluation points are equal with probability one
  (`shared_equal`). A construction that adds the position to the query does not
  share the cell (`fresh_not_shared`), and the two points are equal only with
  probability `1 / 5` (`fresh_equal`): the joint law differs.
-/

namespace TestsSecurity.Counterexamples.Encodings
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Obligations
open ZkcSecurity.Examples.CommittedOpening (prEvent_randomOracle_eq_one)
open TestsSecurity.Counterexamples

abbrev Scalar := ZMod 5

/-! ### Padding aliasing -/

/-- A block of two coordinates, padded with zeros, with no length. -/
def padded (observation : List Scalar) : List Scalar :=
  observation ++ List.replicate (2 - observation.length) 0

theorem padded_alias : padded [1] = padded [1, 0] := rfl

theorem padded_not_prefixFree : ¬ PrefixFreeEncoding padded := fun prefixFree =>
  absurd (prefixFree.injective padded_alias) (by decide)

/-- The two histories' requests, answered by the primitive oracle at their
encodings. -/
def aliased : OracleComp (List Scalar →ₒ Scalar) (Scalar × Scalar) := do
  let first ← liftM ((List Scalar →ₒ Scalar).query (padded [1]))
  let second ← liftM ((List Scalar →ₒ Scalar).query (padded [1, 0]))
  pure (first, second)

theorem aliased_equal :
    Pr{let answers ← (simulateQ randomOracle aliased).run' ∅}[answers.1 = answers.2] = 1 :=
  prEvent_randomOracle_eq_one _ _ fun _ => by
    simp only [aliased, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure]
    rfl

/-- The length, then the coordinates. -/
def lengthPrefixed (observation : List Scalar) : List Scalar :=
  (observation.length : Scalar) :: observation

theorem lengthPrefixed_separates : lengthPrefixed [1] ≠ lengthPrefixed [1, 0] := by decide

/-! ### A truncated digest -/

/-- The low two bits of an eight-valued digest. -/
def truncated (digest : Fin 8) : Fin 4 := ⟨digest.val % 4, Nat.mod_lt _ (by decide)⟩

theorem truncated_not_injective : ¬ Function.Injective truncated := fun injective =>
  absurd (injective (a₁ := 0) (a₂ := 4) rfl) (by decide)

/-! ### Duplicate explicit inputs given fresh cells -/

/-- Two batch positions with the same blob and commitment. -/
def declared : Fin 2 → Fin 2 × Fin 2 := fun _ => (0, 1)

/-- The explicit-input construction queries the declared input. -/
def sharedQuery : Fin 2 → Fin 2 × Fin 2 := declared

/-- A construction that adds the position to every query. -/
def freshQuery : Fin 2 → Fin 2 × (Fin 2 × Fin 2) := fun position => (position, declared position)

theorem shared_shares : SharesEqualInputs declared sharedQuery :=
  determines_of_factor id fun _ => rfl

theorem fresh_not_shared : ¬ SharesEqualInputs declared freshQuery :=
  not_determines (first := 0) (second := 1) rfl (by decide)

/-- Both positions' evaluation points through the explicit-input construction. -/
def sharedPoints : OracleComp (Fin 2 × Fin 2 →ₒ Scalar) (Scalar × Scalar) := do
  let first ← liftM ((Fin 2 × Fin 2 →ₒ Scalar).query (sharedQuery 0))
  let second ← liftM ((Fin 2 × Fin 2 →ₒ Scalar).query (sharedQuery 1))
  pure (first, second)

theorem shared_equal :
    Pr{let points ← (simulateQ randomOracle sharedPoints).run' ∅}[points.1 = points.2] = 1 :=
  prEvent_randomOracle_eq_one _ _ fun _ => by
    simp only [sharedPoints, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      evalWithAnswerFn_pure]
    rfl

/-- Both positions' evaluation points through fresh cells. -/
def freshPoints : OracleComp (Fin 2 × (Fin 2 × Fin 2) →ₒ Scalar) (Scalar × Scalar) := do
  let first ← liftM ((Fin 2 × (Fin 2 × Fin 2) →ₒ Scalar).query (freshQuery 0))
  let second ← liftM ((Fin 2 × (Fin 2 × Fin 2) →ₒ Scalar).query (freshQuery 1))
  pure (first, second)

theorem fresh_equal :
    Pr{let points ← (simulateQ randomOracle freshPoints).run' ∅}[points.1 = points.2] = 1 / 5 := by
  refine (prEvent_randomOracle_two freshPoints (fun points : Scalar × Scalar => points.1 = points.2)
    (first := freshQuery 0) (second := freshQuery 1) (by decide) (fun pair => pair.1 = pair.2)
    fun _ => by
      simp only [freshPoints, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
        evalWithAnswerFn_pure]
      rfl).trans ?_
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun pair : Scalar × Scalar => pair.1 = pair.2).card = 5 := by
    decide
  rw [count, Fintype.card_prod, ZMod.card]
  numerals

end TestsSecurity.Counterexamples.Encodings
