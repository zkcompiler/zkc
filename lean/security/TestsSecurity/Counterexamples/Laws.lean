import ZkcSecurity.FiatShamir.Obligations
import ZkcSecurity.FiatShamir.Grinding
import ZkcSecurity.Examples.CommittedOpening
import TestsSecurity.Counterexamples.Support
import Mathlib.Data.ZMod.Basic

/-! Counterexamples for realized laws and provider correspondence.

- **A correlated block (security attack).** A handler that decodes one uniform
  position into every entry of a block of two positions has uniform marginals,
  yet a word with one bad position among four (distance `1 / 4`) is accepted
  with probability `3 / 4` (`correlated_acceptance`), against `(3 / 4) ^ 2 = 9 / 16`
  for the joint product law (`product_good`). The handler's law is not the
  block's joint law (`correlated_not_realized`).
- **A correlated gate.** A provider that reads the gate bit `U = H(0‖k)` and
  the bit `V = H(1‖k)`, and derives the gated value from both, has the law of a
  uniform pair by role separation, yet passing the gate and the gated value are
  correlated: on the event that the value's first bit is zero its law is `1 / 2`,
  above the record's `γ · ν = 1 / 2 · 1 / 2` (`correlated_gate_not_realized`). The
  value derived from `V` alone has the record (`independent_gate_realized`).
- **A mislabelled law.** A fair-bit decoder that returns `0` on one outcome and
  refuses on the other is realized with factor one and no slack
  (`fairBit_realized`) but is not exact with refusal: it is constant on success
  (`fairBit_not_exact`).
- **Unintended cell sharing.** A history provider whose request input is its
  state, unchanged by the request, reaches one primitive input from two distinct
  reachable requests (`stateless_not_distinct`), and their answers are equal
  with probability one (`stateless_equal`). A provider that replaces its state by
  the encoding of the drawn value, as Monero's transcript does, keeps the two
  inputs distinct outside the event that the first answer equals the state
  (`replacing_distinct`), of probability `1 / 5` here (`replacing_collision`).
-/

namespace TestsSecurity.Counterexamples.Laws
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Obligations
open TestsSecurity.Counterexamples
open scoped ENNReal

/-! ### A correlated block -/

/-- A block of two positions among four. -/
abbrev Block := Fin 2 → Fin 4

/-- The correlated handler: one uniform position copied into the whole block. -/
def correlated (raw : Fin 4) : Option Block := some fun _ => raw

/-- Position `3` is the word's bad position; a block passes when it avoids it. -/
def Good (block : Block) : Prop := ∀ index, block index ≠ 3

instance : DecidablePred Good := fun block => inferInstanceAs (Decidable (∀ index, block index ≠ 3))

inductive Op where
  | positions

abbrev signature : PIR.Signature where
  Op := Op
  Reply
    | .positions => Block

inductive Event where
  | positions
  deriving DecidableEq

abbrev Raw : Event → Type := fun _ => Fin 4

/-- The history oracle answers every history by one position. -/
abbrev HistoryRaw : List Event → Type := fun _ => Fin 4

/-- The query phase requests one block through the correlated handler. -/
def absorb : Typed.Interface signature Event Unit Raw
  | .positions => .query .positions fun raw => correlated raw

/-- The validator of a word with one bad position: accept when the block avoids
it. -/
def validator : PIR.Process signature Bool := .call Op.positions fun block => .done (decide (Good block))

/-- The query-free prover sends nothing. -/
def cheater : OracleComp (OracleSpec.ofFn HistoryRaw) (List Unit) := pure []

theorem correlated_transform :
    Typed.transform absorb Typed.ask validator [] [] =
      (fun raw : Fin 4 => (PIR.Outcome.returned (decide (Good fun _ => raw)), ([] : List Unit))) <$>
        Typed.answer (R := HistoryRaw) [Event.positions] := by
  simp only [validator, Zkc.Transcript.transform, absorb, correlated, List.nil_append, Typed.ask,
    Typed.ReadsByOccurrence.read, Equiv.refl_apply, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]

/-- The word is accepted with probability `3 / 4`. -/
theorem correlated_acceptance :
    Pr{let result ← (simulateQ randomOracle (Typed.fixedExperiment absorb validator [] cheater)).run'
        ∅}[Accepted (· = true) result.1] = 3 / 4 := by
  rw [Typed.fixedExperiment, cheater, pure_bind, correlated_transform, simulateQ_map]
  simp only [Typed.answer, simulateQ_spec_query, StateT.run'_eq, StateT.run_map,
    randomOracle.run_eq, QueryCache.empty_apply, map_bind, map_pure, bind_assoc, pure_bind]
  change Pr{let raw ← $ᵗ (Fin 4)}[Accepted (· = true)
    (PIR.Outcome.returned (decide (Good fun _ => raw)))] = 3 / 4
  rw [prEvent_congr _ _ (fun raw : Fin 4 => raw ≠ 3) fun raw => by simp [Accepted, Good],
    SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun raw : Fin 4 => raw ≠ 3).card = 3 := by decide
  rw [count, Fintype.card_fin]
  numerals

/-- Under the joint product law the block avoids the bad position with
probability `9 / 16`. -/
theorem product_good : Pr{let block ← $ᵗ Block}[Good block] = 9 / 16 := by
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun block : Block => Good block).card = 9 := by decide
  rw [count, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  numerals

/-- The correlated handler does not realize the block's joint law. -/
theorem correlated_not_realized : ¬ Realized correlated 1 0 := by
  intro realized
  have bound := realized Good
  rw [one_mul, add_zero, product_good] at bound
  have decoded : Pr{let raw ← $ᵗ (Fin 4)}[∃ block, correlated raw = some block ∧ Good block] =
      3 / 4 := by
    rw [SampleableType.prEvent_uniformSample]
    have count : (Finset.univ.filter fun raw : Fin 4 =>
        ∃ block, correlated raw = some block ∧ Good block).card = 3 := by
      decide
    rw [count, Fintype.card_fin]
    numerals
  rw [decoded] at bound
  exact absurd bound (by rw [not_le]; numerals)

/-! ### A correlated gate -/

/-- The gate passes when `U = 0`; the gated value is derived from `U` and `V`. -/
def correlatedGate (raw : Fin 2 × Fin 2) : Option (Fin 2 × Fin 2) :=
  if raw.1 = 0 then some raw else none

/-- The gated value derived from `V` alone. -/
def independentGate (raw : Fin 2 × Fin 2) : Option (Fin 2) :=
  if raw.1 = 0 then raw.2 else none

/-- The gate passes with probability `1 / 2`. -/
theorem gate_passes : Pr{let bit ← $ᵗ (Fin 2)}[id bit = 0] = 1 / 2 := by
  change Pr{let bit ← $ᵗ (Fin 2)}[bit = 0] = 1 / 2
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
  numerals

/-- The record with coefficient `ρ · κ = 1 / 2 · 1` holds for the value derived
from `V` alone. -/
theorem independent_gate_realized : Realized independentGate (1 / 2 * 1) (1 / 2 * 0) := by
  have realized := gated_realized (B₁ := Fin 2) (B₂ := Fin 2) id 0 (fun bit => some bit)
    gate_passes.le (realized_of_bijective Function.bijective_id)
  exact realized

/-- Passing the gate and the gated value are correlated: on the event that the
value's first bit is zero, the realized law exceeds the record's coefficient
`1 / 2` times the uniform probability `1 / 2`. -/
theorem correlated_gate_not_realized : ¬ Realized correlatedGate (1 / 2 * 1) 0 := by
  intro realized
  have bound := realized fun value => value.1 = 0
  have decoded : Pr{let raw ← $ᵗ (Fin 2 × Fin 2)}[
      ∃ value, correlatedGate raw = some value ∧ value.1 = 0] = 1 / 2 := by
    rw [SampleableType.prEvent_uniformSample]
    have count : (Finset.univ.filter fun raw : Fin 2 × Fin 2 =>
        ∃ value, correlatedGate raw = some value ∧ value.1 = 0).card = 2 := by
      decide
    rw [count, Fintype.card_prod, Fintype.card_fin]
    numerals
  have uniform : Pr{let value ← $ᵗ (Fin 2 × Fin 2)}[value.1 = 0] = 1 / 2 := by
    rw [SampleableType.prEvent_uniformSample]
    have count : (Finset.univ.filter fun value : Fin 2 × Fin 2 => value.1 = 0).card = 2 := by
      decide
    rw [count, Fintype.card_prod, Fintype.card_fin]
    numerals
  rw [decoded, uniform, add_zero] at bound
  exact absurd bound (by rw [not_le]; numerals)

/-! ### A mislabelled law -/

/-- A fair bit decoded to `0` on one outcome and refused on the other. -/
def fairBit (raw : Fin 2) : Option (Fin 2) := if raw = 0 then some 0 else none

/-- The fair-bit decoder is realized with factor one and no slack. -/
theorem fairBit_realized : Realized fairBit 1 0 := by
  intro event
  rw [one_mul, add_zero]
  refine prEvent_mono _ _ event fun raw ⟨value, decoded, holds⟩ => ?_
  unfold fairBit at decoded
  split at decoded
  · rename_i zero
    cases Option.some.inj decoded
    rw [zero]
    exact holds
  · exact absurd decoded (by simp)

/-- It is not exact with refusal: it is constant on success, so the event
`value = 0` has probability `1 / 2`, not `1 / 2 · 1 / 2`. -/
theorem fairBit_not_exact : ¬ ExactWithRefusal fairBit := by
  intro exact
  have equal := exact fun value => value = 0
  have left : Pr{let raw ← $ᵗ (Fin 2)}[∃ value, fairBit raw = some value ∧ value = 0] = 1 / 2 := by
    rw [SampleableType.prEvent_uniformSample]
    have count : (Finset.univ.filter fun raw : Fin 2 =>
        ∃ value, fairBit raw = some value ∧ value = 0).card = 1 := by
      decide
    rw [count, Fintype.card_fin]
    numerals
  have success : Pr{let raw ← $ᵗ (Fin 2)}[(fairBit raw).isSome = true] = 1 / 2 := by
    rw [SampleableType.prEvent_uniformSample]
    have count : (Finset.univ.filter fun raw : Fin 2 => (fairBit raw).isSome = true).card = 1 := by
      decide
    rw [count, Fintype.card_fin]
    numerals
  have uniform : Pr{let value ← $ᵗ (Fin 2)}[value = 0] = 1 / 2 := by
    rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
    numerals
  rw [left, success, uniform] at equal
  exact absurd equal (by numerals)

/-! ### Unintended cell sharing -/

/-- The two reachable requests of a provider, by occurrence. -/
inductive Request where
  | first
  | second
  deriving DecidableEq

abbrev Element := ZMod 5

/-- A provider whose request input is its state `state`, unchanged by requests. -/
def statelessInput (state : Element) : Request → Element := fun _ => state

theorem stateless_not_distinct (state : Element) :
    ¬ DistinctPrimitiveInputs (fun _ : Request => True) (statelessInput state) :=
  fun distinct => absurd (distinct .first .second trivial trivial rfl) (by decide)

/-- The two requests of the stateless provider, answered by the primitive
oracle. -/
def statelessRequests (state : Element) : OracleComp (Element →ₒ Element) (Element × Element) := do
  let first ← liftM ((Element →ₒ Element).query (statelessInput state .first))
  let second ← liftM ((Element →ₒ Element).query (statelessInput state .second))
  pure (first, second)

/-- Their answers are equal with probability one. -/
theorem stateless_equal (state : Element) :
    Pr{let answers ← (simulateQ randomOracle (statelessRequests state)).run' ∅}[
      answers.1 = answers.2] = 1 :=
  ZkcSecurity.Examples.CommittedOpening.prEvent_randomOracle_eq_one _ _ fun table => by
    simp [statelessRequests, statelessInput]

/-- A provider that replaces its state by the drawn value before the next
request: the second input is the first answer. -/
def replacingInput (state answer : Element) : Request → Element
  | .first => state
  | .second => answer

/-- The inputs stay distinct unless the first answer equals the state. -/
theorem replacing_distinct (state answer : Element) (fresh : answer ≠ state) :
    DistinctPrimitiveInputs (fun _ : Request => True) (replacingInput state answer) := by
  intro one other _ _ same
  cases one <;> cases other
  · rfl
  · exact absurd same.symm fresh
  · exact absurd same fresh
  · rfl

/-- The first answer, a fresh uniform value, equals the state with probability
`1 / 5`. -/
theorem replacing_collision (state : Element) :
    Pr{let answer ← (simulateQ randomOracle
        (liftM ((Element →ₒ Element).query state) : OracleComp (Element →ₒ Element) Element)).run'
        ∅}[answer = state] = 1 / 5 := by
  simp only [simulateQ_spec_query, StateT.run'_eq, randomOracle.run_eq, QueryCache.empty_apply,
    map_bind, map_pure]
  change Pr{let answer ← $ᵗ Element}[answer = state] = 1 / 5
  rw [SampleableType.prEvent_uniformSample_eq_singleton, ZMod.card]
  numerals

end TestsSecurity.Counterexamples.Laws
