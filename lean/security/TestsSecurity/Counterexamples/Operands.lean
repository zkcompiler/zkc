import ZkcSecurity.Transformations.FiatShamir.Obligations
import ZkcSecurityExamples.CommittedOpening
import TestsSecurity.Counterexamples.Support

/-! Counterexamples for security operands.

- **A query count read from the proof (security attack).** A word over four
  positions with one bad position (distance `1 / 4`) is checked at as many
  positions as the proof states. A proof stating zero positions is accepted with
  probability one (`zeroCount_acceptance`), one stating one position with
  probability `3 / 4` (`oneCount_acceptance`). The count is neither fixed by the
  statement nor checked against an authenticated minimum
  (`count_not_authenticated`).
- **An attacker-chosen zero count.** A batch of zero items is accepted, and the
  event that some item is false is empty, so a per-item bound holds and
  certifies no item (`emptyBatch_accepted`, `emptyBatch_nothing_false`). An
  operand that admits zero does not support a production claim
  (`zeroCount_not_production`).
-/

namespace TestsSecurity.Counterexamples.Operands
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Obligations
open ZkcSecurity.Examples.CommittedOpening (prEvent_randomOracle_eq_one)
open TestsSecurity.Counterexamples
open scoped ENNReal

/-! ### A query count read from the proof -/

/-- The word's bad position. -/
def bad : Fin 4 := 3

/-- The verifier draws `count` positions, one key per position with the count
absorbed, and accepts when every drawn position is good. -/
def countVerifier (count : ℕ) : OracleComp (ℕ × ℕ →ₒ Fin 4) Bool := do
  let positions ← (List.range count).mapM fun index =>
    liftM ((ℕ × ℕ →ₒ Fin 4).query (count, index))
  pure (positions.all fun position => decide (position ≠ bad))

/-- A proof stating zero positions is accepted with probability one. -/
theorem zeroCount_acceptance :
    Pr{let accepted ← (simulateQ randomOracle (countVerifier 0)).run' ∅}[accepted = true] = 1 :=
  prEvent_randomOracle_eq_one _ _ fun _ => by simp [countVerifier]

/-- A proof stating one position is accepted with probability `3 / 4`. -/
theorem oneCount_acceptance :
    Pr{let accepted ← (simulateQ randomOracle (countVerifier 1)).run' ∅}[accepted = true] = 3 / 4 := by
  simp only [countVerifier, List.range_one, List.mapM_cons, List.mapM_nil, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, StateT.run'_eq, StateT.run_map, randomOracle.run_eq,
    QueryCache.empty_apply, map_pure, Functor.map_map]
  change Pr{let position ← $ᵗ (Fin 4)}[[position].all (fun position => decide (position ≠ bad)) =
    true] = 3 / 4
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun position : Fin 4 =>
      [position].all (fun position => decide (position ≠ bad)) = true).card = 3 := by
    decide
  rw [count, Fintype.card_fin]
  numerals

/-- The count enters the error but comes from the proof: the statement (the
word) does not fix it, and the verifier admits zero. -/
theorem count_not_authenticated :
    ¬ AuthenticatedOperand (fun _ : ℕ => bad) id (fun _ => True) (1 ≤ ·) := by
  rintro (fixed | checked)
  · exact absurd (fixed 0 1 rfl) (by decide)
  · exact absurd (checked 0 trivial) (by decide)

/-! ### An attacker-chosen zero count -/

/-- A batch verifier accepts when every item is valid. -/
def batchAccepts {Item : Type} (valid : Item → Bool) (items : List Item) : Bool := items.all valid

theorem emptyBatch_accepted {Item : Type} (valid : Item → Bool) : batchAccepts valid [] = true :=
  rfl

/-- The event that some item is false is empty at count zero. -/
theorem emptyBatch_nothing_false {Item : Type} (valid : Item → Bool) :
    ¬ ∃ item ∈ ([] : List Item), valid item = false := by
  simp

/-- A count the deployment admits at zero does not support a claim that needs at
least one item. -/
theorem zeroCount_not_production : ¬ ProductionRange (fun count : ℕ => count) (fun _ => True) (1 ≤ ·) :=
  fun production => absurd (production 0 trivial) (by decide)

end TestsSecurity.Counterexamples.Operands
