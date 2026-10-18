import ZkcSecurity.FiatShamir.Obligations
import ZkcSecurity.Examples.CommittedOpening
import TestsSecurity.Counterexamples.Support

/-! Counterexamples for security operands and proof-of-work gates.

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
- **Misplaced and incomplete gates (security attacks).** A gate whose request
  absorbs a producer message after the gate step, a gate whose input omits the
  transcript state, and a gate whose gated value is derived from a state that has
  not absorbed the witness each let one passing witness serve many challenges:
  with `k` gate attempts and `n` challenge attempts, the adversary succeeds with
  probability `(1 - (1 - ρ) ^ k) · (1 - (1 - ε) ^ n)` (`reuse_success`), whereas
  a placed gate gives each attempt `ρ · ε` (`placed_success`). With a 4-bit gate
  and a one-bit target, 32 gate attempts and 8 challenge attempts succeed with
  probability above `0.86` against below `0.72` for the same 40 attempts at a
  placed gate (`reuse_beats_placed`). The three gates violate placement
  (`misplaced_violates`), reading the state (`stateless_violates`) and absorbing
  the witness (`unabsorbed_violates`); a placed gate meets all three
  (`placed_meets`). In the random-oracle model the adversary's distinct keys
  receive independent uniform answers, which is the law of the uniform tuples
  below.
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

/-! ### Misplaced and incomplete gates -/

/-- With every attempt's answer uniform and independent, at least one of `n`
attempts hits an event of probability `1 - miss` with probability
`1 - miss ^ n`. -/
theorem prEvent_exists_uniform {B : Type} [SampleableType B] [Fintype B] (n : ℕ) (hit : B → Prop)
    {miss : ENNReal} (missing : Pr{let answer ← $ᵗ B}[¬ hit answer] = miss) :
    Pr{let answers ← $ᵗ (Fin n → B)}[∃ index, hit (answers index)] = 1 - miss ^ n := by
  have total := prEvent_add_prEvent_not_eq_prEvent_true ($ᵗ (Fin n → B))
    fun answers => ∃ index, hit (answers index)
  rw [(SampleableType.prEvent_uniformSample_eq_one_iff fun _ => True).mpr fun _ => trivial] at total
  have none : Pr{let answers ← $ᵗ (Fin n → B)}[¬ ∃ index, hit (answers index)] = miss ^ n := by
    rw [prEvent_congr _ _ (fun answers : Fin n → B => ∀ index, ¬ hit (answers index))
      fun _ => not_exists, prEvent_uniform_pi (fun _ answer => ¬ hit answer), missing,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [none] at total
  have finite : miss ^ n ≠ ⊤ := by
    rw [← none]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _ _)
  exact ENNReal.eq_sub_of_add_eq finite total

/-- A gate of four bits passes on zero; a challenge bit hits on zero. -/
abbrev passes (gate : Fin 16) : Prop := gate = 0

abbrev hits (challenge : Fin 2) : Prop := challenge = 0

theorem gate_miss : Pr{let gate ← $ᵗ (Fin 16)}[¬ passes gate] = 15 / 16 := by
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun gate : Fin 16 => ¬ passes gate).card = 15 := by decide
  rw [count, Fintype.card_fin]
  rfl

theorem challenge_miss : Pr{let challenge ← $ᵗ (Fin 2)}[¬ hits challenge] = 1 / 2 := by
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun challenge : Fin 2 => ¬ hits challenge).card = 1 := by decide
  rw [count, Fintype.card_fin, Nat.cast_one, Nat.cast_ofNat]

theorem placed_miss :
    Pr{let answer ← $ᵗ (Fin 16 × Fin 2)}[¬ (passes answer.1 ∧ hits answer.2)] = 31 / 32 := by
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun answer : Fin 16 × Fin 2 =>
      ¬ (passes answer.1 ∧ hits answer.2)).card = 31 := by
    decide
  rw [count, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rfl

/-- One passing witness serves every challenge: with `k` gate attempts and `n`
challenge attempts the adversary succeeds with probability
`(1 - (15 / 16) ^ k) · (1 - (1 / 2) ^ n)`. -/
theorem reuse_success (k n : ℕ) :
    Pr{let attempts ← $ᵗ ((Fin k → Fin 16) × (Fin n → Fin 2))}[
      (∃ index, passes (attempts.1 index)) ∧ ∃ index, hits (attempts.2 index)] =
      (1 - (15 / 16) ^ k) * (1 - (1 / 2) ^ n) := by
  rw [prEvent_uniform_prod (fun gates : Fin k → Fin 16 => ∃ index, passes (gates index))
    (fun challenges : Fin n → Fin 2 => ∃ index, hits (challenges index)),
    prEvent_exists_uniform k passes gate_miss, prEvent_exists_uniform n hits challenge_miss]

/-- At a placed gate each attempt passes and hits at once, with probability
`1 / 16 · 1 / 2`: `m` attempts succeed with probability `1 - (31 / 32) ^ m`. -/
theorem placed_success (attempts : ℕ) :
    Pr{let answers ← $ᵗ (Fin attempts → Fin 16 × Fin 2)}[
      ∃ index, passes (answers index).1 ∧ hits (answers index).2] = 1 - (31 / 32) ^ attempts :=
  prEvent_exists_uniform attempts (fun answer : Fin 16 × Fin 2 => passes answer.1 ∧ hits answer.2)
    placed_miss

/-- With 32 gate attempts and 8 challenge attempts the reusing adversary
succeeds with probability above `0.86`; 40 attempts at a placed gate succeed
with probability below `0.72`. -/
theorem reuse_beats_placed :
    (1 - (31 / 32 : ENNReal) ^ 40) < 72 / 100 ∧
      (86 / 100 : ENNReal) < (1 - (15 / 16) ^ 32) * (1 - (1 / 2) ^ 8) := by
  constructor
  · rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness),
      ENNReal.toReal_sub_of_le (pow_le_one₀ (by positivity) (by numerals)) ENNReal.one_ne_top]
    simp only [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num
  · rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness), ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le (pow_le_one₀ (by positivity) (by numerals)) ENNReal.one_ne_top,
      ENNReal.toReal_sub_of_le (pow_le_one₀ (by positivity) (by numerals)) ENNReal.one_ne_top]
    simp only [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num

/-- Contexts of one gate: the transcript state, the witness and a producer
message. -/
abbrev GateContext := Fin 2 × Fin 2 × Fin 2

/-- A producer message is absorbed between the gate step and the request. -/
def misplaced : GateSite GateContext (Fin 2 × Fin 2) (Fin 2) (Fin 2) GateContext :=
  ⟨fun context => (context.1, context.2.1), fun context => context.1, fun context => context.2.1, id⟩

/-- The gate step reads the witness only. -/
def stateless : GateSite GateContext (Fin 2) (Fin 2) (Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun context => context.2.1, fun context => context.1, fun context => context.2.1,
    fun context => (context.1, context.2.1)⟩

/-- The gated value is derived from the state alone. -/
def unabsorbed : GateSite GateContext (Fin 2 × Fin 2) (Fin 2) (Fin 2) (Fin 2) :=
  ⟨fun context => (context.1, context.2.1), fun context => context.1, fun context => context.2.1,
    fun context => context.1⟩

/-- The gate step and the gated value read the state and the witness. -/
def placed : GateSite GateContext (Fin 2 × Fin 2) (Fin 2) (Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun context => (context.1, context.2.1), fun context => context.1, fun context => context.2.1,
    fun context => (context.1, context.2.1)⟩

theorem misplaced_violates : ¬ misplaced.Placement :=
  not_determines (first := (0, 0, 0)) (second := (0, 0, 1)) rfl (by decide)

theorem stateless_violates : ¬ stateless.ReadsState :=
  not_determines (first := (0, 0, 0)) (second := (1, 0, 0)) rfl (by decide)

theorem unabsorbed_violates : ¬ unabsorbed.AbsorbsWitness :=
  not_determines (first := (0, 0, 0)) (second := (0, 1, 0)) rfl (by decide)

theorem placed_meets : placed.Placement ∧ placed.ReadsState ∧ placed.AbsorbsWitness :=
  ⟨determines_of_factor id fun _ => rfl, determines_of_factor Prod.fst fun _ => rfl,
    determines_of_factor Prod.snd fun _ => rfl⟩

end TestsSecurity.Counterexamples.Operands
