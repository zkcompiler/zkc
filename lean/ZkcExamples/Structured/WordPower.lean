module

public import Zkc.Source.Structured.ReferenceLaws

@[expose] public section

/-! Complete word-level references, before any supported mathematical specialization.
Inputs outside the word range retain their actual truncation and finite-domain admission.
-/

set_option autoImplicit false
namespace ZkcExamples.Structured.WordPower
open Zkc Zkc.Source Zkc.Source.Structured

/-- The two source results: remaining word, accumulated width. -/
def half (value offset amount : Nat) : Nat × Nat :=
  let shifted := logicalShiftRight value amount
  if shifted = 0 then (value, offset) else (shifted, wrappingAdd offset amount)

/-- Exactly the six binary-search stages in the original width helper. -/
def halves (value : Nat) : Nat × Nat :=
  [32, 16, 8, 4, 2, 1].foldl (fun state amount ↦ half state.1 state.2 amount) (value, 0)

def width (value : Nat) : Nat :=
  let state := halves value
  if state.1 = 0 then 0 else wrappingAdd state.2 1

structure State (F : Type) where
  result : F
  factor : F
  remaining : Nat
  deriving DecidableEq, Repr

def step {F : Type} [Mul F] (state : State F) : State F :=
  ⟨if bitAnd state.remaining 1 = 1 then state.result * state.factor else state.result,
    state.factor * state.factor, logicalShiftRight state.remaining 1⟩

/-- A counted reference for the same finite fold; the source callback ignores its index. -/
def run {F : Type} [Mul F] : Nat → State F → State F
  | 0, state => state
  | count + 1, state => run count (step state)

def pack (model : DomainModel) (d : String) (state : State (model.Field d)) :
    Values model.Value [.field d, .field d, .index] :=
  .cons state.result (.cons state.factor (.cons state.remaining .nil))

/-- Exact finite-domain refusal precedes any callback; no mathematical power is substituted. -/
def outcome (model : DomainModel) (d : String) (base : model.Field d) (exponent : Nat) :
    PIR.Outcome (Values model.Value [.field d]) :=
  if 0 < indexLimit ∧ width exponent < indexLimit then
    .returned (.cons (run (width exponent) ⟨1, base, exponent⟩).result .nil)
  else .stopped .refused

/-- One binary-search stage retains the exact quotient and tightens its bit bound. -/
theorem half_invariant (exponent value offset amount : Nat)
    (representable : value < wordModulus) (shiftBound : amount < 64)
    (sumBound : offset + amount < wordModulus)
    (quotient : value = exponent / 2 ^ offset)
    (bounded : value < 2 ^ (amount + amount))
    (zero : value = 0 → exponent = 0) :
    let next := half value offset amount
    next.1 = exponent / 2 ^ next.2 ∧ next.1 < 2 ^ amount ∧
      next.2 ≤ offset + amount ∧ (next.1 = 0 → exponent = 0) := by
  have shift : logicalShiftRight value amount = value / 2 ^ amount := by
    rw [logicalShiftRight_of_lt _ shiftBound, Nat.mod_eq_of_lt representable]
  have wrap : wrappingAdd offset amount = offset + amount := Nat.mod_eq_of_lt sumBound
  simp only [half, shift]
  split
  next empty =>
    refine ⟨quotient, ?_, by omega, zero⟩
    exact (Nat.div_eq_zero_iff.mp empty).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos amount))
  next nonempty =>
    rw [wrap]
    refine ⟨?_, ?_, Nat.le_refl _, fun h ↦ (nonempty h).elim⟩
    · rw [quotient, Nat.div_div_eq_div_mul, ← Nat.pow_add]
    · apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos amount)).mpr
      simpa only [Nat.pow_add] using bounded

/-- Word-level width covers every significant bit, including the 64th bit. -/
theorem width_covers (exponent : Nat) (representable : exponent < wordModulus) :
    width exponent ≤ 64 ∧ exponent < 2 ^ width exponent := by
  have large : 128 < wordModulus := by decide
  have first := half_invariant exponent exponent 0 32 representable (by decide) (by omega)
    (by simp) representable (fun h ↦ h)
  let a := half exponent 0 32
  change a.1 = exponent / 2 ^ a.2 ∧ a.1 < 2 ^ 32 ∧ a.2 ≤ 32 ∧
    (a.1 = 0 → exponent = 0) at first
  have second := half_invariant exponent a.1 a.2 16 (by
    exact first.2.1.trans (by decide)) (by decide) (by omega) first.1 first.2.1 first.2.2.2
  let b := half a.1 a.2 16
  change b.1 = exponent / 2 ^ b.2 ∧ b.1 < 2 ^ 16 ∧ b.2 ≤ a.2 + 16 ∧
    (b.1 = 0 → exponent = 0) at second
  have third := half_invariant exponent b.1 b.2 8 (second.2.1.trans (by decide))
    (by decide) (by omega) second.1 second.2.1 second.2.2.2
  let c := half b.1 b.2 8
  change c.1 = exponent / 2 ^ c.2 ∧ c.1 < 2 ^ 8 ∧ c.2 ≤ b.2 + 8 ∧
    (c.1 = 0 → exponent = 0) at third
  have fourth := half_invariant exponent c.1 c.2 4 (third.2.1.trans (by decide))
    (by decide) (by omega) third.1 third.2.1 third.2.2.2
  let d := half c.1 c.2 4
  change d.1 = exponent / 2 ^ d.2 ∧ d.1 < 2 ^ 4 ∧ d.2 ≤ c.2 + 4 ∧
    (d.1 = 0 → exponent = 0) at fourth
  have fifth := half_invariant exponent d.1 d.2 2 (fourth.2.1.trans (by decide))
    (by decide) (by omega) fourth.1 fourth.2.1 fourth.2.2.2
  let e := half d.1 d.2 2
  change e.1 = exponent / 2 ^ e.2 ∧ e.1 < 2 ^ 2 ∧ e.2 ≤ d.2 + 2 ∧
    (e.1 = 0 → exponent = 0) at fifth
  have sixth := half_invariant exponent e.1 e.2 1 (fifth.2.1.trans (by decide))
    (by decide) (by omega) fifth.1 fifth.2.1 fifth.2.2.2
  let f := half e.1 e.2 1
  change f.1 = exponent / 2 ^ f.2 ∧ f.1 < 2 ∧ f.2 ≤ e.2 + 1 ∧
    (f.1 = 0 → exponent = 0) at sixth
  have offset : f.2 ≤ 63 := by omega
  change (if f.1 = 0 then 0 else wrappingAdd f.2 1) ≤ 64 ∧
    exponent < 2 ^ (if f.1 = 0 then 0 else wrappingAdd f.2 1)
  by_cases empty : f.1 = 0
  · simp [empty, sixth.2.2.2 empty]
  · have wrap : wrappingAdd f.2 1 = f.2 + 1 := Nat.mod_eq_of_lt (by omega)
    simp only [empty, ↓reduceIte, wrap]
    refine ⟨by omega, ?_⟩
    have h := Nat.lt_mul_of_div_lt (sixth.1 ▸ sixth.2.1) (Nat.two_pow_pos f.2)
    simpa only [Nat.pow_succ, Nat.mul_comm] using h

/-- The actual masked low bit agrees with the natural remainder on a word. -/
theorem low_bit (remaining : Nat) (bounded : remaining < wordModulus) :
    bitAnd remaining 1 = remaining % 2 := by
  unfold bitAnd
  rw [Nat.mod_eq_of_lt bounded, Nat.mod_eq_of_lt (show 1 < wordModulus by decide)]
  exact Nat.and_two_pow_sub_one_eq_mod remaining 1

/-- Multiplication conserves result * factor^remaining at each reached source iteration. -/
theorem step_invariant {F : Type} [CommMonoid F] (state : State F)
    (bounded : state.remaining < wordModulus) :
    (step state).result * (step state).factor ^ (step state).remaining =
      state.result * state.factor ^ state.remaining := by
  have shift : logicalShiftRight state.remaining 1 = state.remaining / 2 := by
    rw [logicalShiftRight_of_lt _ (by decide), Nat.mod_eq_of_lt bounded]
  have decomposition := Nat.mod_add_div state.remaining 2
  rcases Nat.mod_two_eq_zero_or_one state.remaining with even | odd
  · simp only [step, low_bit _ bounded, even, Nat.zero_ne_one, ↓reduceIte, shift]
    rw [← pow_two, ← pow_mul]
    exact congrArg (fun n ↦ state.result * state.factor ^ n) (by omega)
  · simp only [step, low_bit _ bounded, odd, ↓reduceIte, shift]
    rw [← pow_two, ← pow_mul, mul_assoc, ← pow_succ']
    exact congrArg (fun n ↦ state.result * state.factor ^ n) (by omega)

/-- Counted invariant: enough remaining trips consume the full exponent without overflow. -/
theorem run_correct {F : Type} [CommMonoid F] (count : Nat) (state : State F)
    (bounded : state.remaining < wordModulus) (covered : state.remaining < 2 ^ count) :
    (run count state).result = state.result * state.factor ^ state.remaining := by
  induction count generalizing state with
  | zero =>
    have empty : state.remaining = 0 := by simpa using covered
    simp [run, empty]
  | succ count ih =>
    rw [run, ih (step state) (show (step state).remaining < wordModulus from
      logicalShiftRight_lt state.remaining 1), step_invariant state bounded]
    change logicalShiftRight state.remaining 1 < 2 ^ count
    rw [logicalShiftRight_of_lt _ (by decide), Nat.mod_eq_of_lt bounded]
    apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
    simpa only [Nat.pow_succ] using covered

/-- The exact complete-outcome reference returns mathematical power on representable words. -/
theorem outcome_power (model : DomainModel) (d : String) (base : model.Field d)
    (exponent : Nat) (representable : exponent < wordModulus) :
    outcome model d base exponent = .returned (.cons (base ^ exponent) .nil) := by
  obtain ⟨widthBound, covered⟩ := width_covers exponent representable
  have admitted : 0 < indexLimit ∧ width exponent < indexLimit := by
    change 0 < wordModulus ∧ width exponent < wordModulus
    exact ⟨wordModulus_pos, lt_of_le_of_lt widthBound (by decide)⟩
  simp only [outcome, admitted]
  rw [run_correct (width exponent) ⟨1, base, exponent⟩ representable covered]
  simp

end ZkcExamples.Structured.WordPower
