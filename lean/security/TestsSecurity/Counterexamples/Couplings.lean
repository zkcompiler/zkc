import ZkcSecurity.Transformations.FiatShamir.Obligations
import TestsSecurity.Counterexamples.Support

/-! Counterexamples for couplings and construction identity.

Each example refutes one property and violates one obligation of the
[construction obligations](../../../../../docs/spec/ir/construction-obligations.md).
None is a security attack, so none quantifies adversarial success.

- **A re-encoding that reads the selected answer.** Over two keys with uniform
  bits, sending the first key to a key whose answer is zero whenever one exists
  is a bijection for every table (`reencode_bijective`), yet the selected answer
  is zero with probability `3 / 4` against `1 / 2` (`reencoded_zero`,
  `direct_zero`): no coupling makes the two experiments equal in distribution.
  It is not causal (`reencode_not_causal`); injectivity alone is not enough.
- **A constant re-encoding.** Mapping every key to one key is causal
  (`constant_causal`) but collapses distinct keys (`constant_not_preserving`):
  two independent answers become equal with probability one against `1 / 2`
  (`constant_equal`, `direct_equal`).
- **A hash chain with an answer collision.** With one-bit chain states, the
  requests after two distinct one-event histories receive equal answers with
  probability `3 / 4` (`chain_equal`) where the history oracle gives `1 / 2`, so
  the chain is not equivalent to the history oracle with zero loss
  (`chain_not_zero_loss`). The gap is within the probability `1 / 2` of the
  collision of the two states (`chain_collision`, `chain_within_collision`):
  equivalence up to a bad event is the obligation.
- **Absorbing a constant at zero difficulty.** Absorbing a pinned witness before
  a request changes the request's key, so for some challenge function the two
  transforms differ (`pinned_differs`): the constructions are not the same
  construction (`pinned_not_correct`).
-/

namespace TestsSecurity.Counterexamples.Couplings
open OracleComp ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Obligations
open TestsSecurity.Counterexamples

/-! ### A re-encoding that reads the selected answer -/

/-- Two keys `0` and `1` with uniform bits. Key `0` goes to a key whose answer
is zero whenever one exists; key `1` goes to the other key. -/
def reencode (table : Fin 2 → Fin 2) : Fin 2 → Fin 2 := fun key =>
  if table 0 = 0 then key else if table 1 = 0 then 1 - key else key

theorem reencode_bijective (table : Fin 2 → Fin 2) : Function.Bijective (reencode table) := by
  revert table
  decide

/-- The re-encoding preserves query equality in both directions. -/
theorem reencode_preserving : PreservesQueryEquality reencode :=
  fun table => (reencode_bijective table).1

/-- No key is earlier than another: the two keys are first queries. -/
def noEarlier : Fin 2 → Fin 2 → Prop := fun _ _ => False

/-- The re-encoding reads the answer it selects, so it is not causal. -/
theorem reencode_not_causal : ¬ CausalReencoding noEarlier reencode := by
  intro causal
  have same := causal (fun _ => 1) (fun key => if key = 1 then 0 else 1) 0 fun _ earlier =>
    earlier.elim
  revert same
  decide

/-- Through the re-encoding, the selected answer is zero with probability
`3 / 4`. -/
theorem reencoded_zero :
    Pr{let table ← $ᵗ (Fin 2 → Fin 2)}[table (reencode table 0) = 0] = 3 / 4 := by
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun table : Fin 2 → Fin 2 => table (reencode table 0) = 0).card =
      3 := by decide
  rw [count, Fintype.card_fun, Fintype.card_fin]
  numerals

/-- Directly, the answer is zero with probability `1 / 2`. -/
theorem direct_zero : Pr{let table ← $ᵗ (Fin 2 → Fin 2)}[table 0 = 0] = 1 / 2 := by
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun table : Fin 2 → Fin 2 => table 0 = 0).card = 2 := by decide
  rw [count, Fintype.card_fun, Fintype.card_fin]
  numerals

/-! ### A constant re-encoding -/

/-- Every key goes to key `0`. -/
def constant : (Fin 2 → Fin 2) → Fin 2 → Fin 2 := fun _ _ => 0

theorem constant_causal : CausalReencoding noEarlier constant := fun _ _ _ _ => rfl

theorem constant_not_preserving : ¬ PreservesQueryEquality constant :=
  fun preserving => absurd (preserving (fun _ => 0) (a₁ := 0) (a₂ := 1) rfl) (by decide)

/-- Through the constant re-encoding, the answers of the two keys are equal with
probability one. -/
theorem constant_equal :
    Pr{let table ← $ᵗ (Fin 2 → Fin 2)}[table (constant table 0) = table (constant table 1)] = 1 :=
  (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr fun _ => rfl

/-- Directly, the answers of two keys are equal with probability `1 / 2`. -/
theorem direct_equal : Pr{let table ← $ᵗ (Fin 2 → Fin 2)}[table 0 = table 1] = 1 / 2 := by
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun table : Fin 2 → Fin 2 => table 0 = table 1).card = 2 := by
    decide
  rw [count, Fintype.card_fun, Fintype.card_fin]
  numerals

/-! ### A hash chain with an answer collision -/

/-- The primitive inputs of a one-bit chain: absorbing event `e` at state `s` is
input `2 s + e`, and a request at state `s` is input `4 + s`. Inputs `0` to `5`. -/
def absorbInput (state event : Fin 2) : Fin 6 := ⟨2 * state.val + event.val, by omega⟩

def requestInput (state : Fin 2) : Fin 6 := ⟨4 + state.val, by omega⟩

/-- The chain's answer to the request after the one-event history `[event]`,
from the binding state `0`. -/
def chainAnswer (hash : Fin 6 → Fin 2) (event : Fin 2) : Fin 2 :=
  hash (requestInput (hash (absorbInput 0 event)))

/-- The two histories' states collide. -/
abbrev Collision (hash : Fin 6 → Fin 2) : Prop :=
  hash (absorbInput 0 0) = hash (absorbInput 0 1)

/-- The chain's requests after the histories `[0]` and `[1]` receive equal
answers with probability `3 / 4`. -/
theorem chain_equal :
    Pr{let hash ← $ᵗ (Fin 6 → Fin 2)}[chainAnswer hash 0 = chainAnswer hash 1] = 3 / 4 := by
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun hash : Fin 6 → Fin 2 =>
      chainAnswer hash 0 = chainAnswer hash 1).card = 48 := by decide
  rw [count, Fintype.card_fun, Fintype.card_fin]
  numerals

/-- The two states collide with probability `1 / 2`. -/
theorem chain_collision : Pr{let hash ← $ᵗ (Fin 6 → Fin 2)}[Collision hash] = 1 / 2 := by
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun hash : Fin 6 → Fin 2 => Collision hash).card = 32 := by
    decide
  rw [count, Fintype.card_fun, Fintype.card_fin]
  numerals

/-- The history oracle answers the two distinct histories independently: equal
with probability `1 / 2` (`direct_equal`). With zero loss, the chain's
probability would be at most that. -/
theorem chain_not_zero_loss :
    ¬ Pr{let hash ← $ᵗ (Fin 6 → Fin 2)}[chainAnswer hash 0 = chainAnswer hash 1] ≤
      Pr{let table ← $ᵗ (Fin 2 → Fin 2)}[table 0 = table 1] + 0 := by
  rw [chain_equal, direct_equal, add_zero, not_le]
  numerals

/-- The gap is within the collision probability: equivalence up to the
collision event. -/
theorem chain_within_collision :
    Pr{let hash ← $ᵗ (Fin 6 → Fin 2)}[chainAnswer hash 0 = chainAnswer hash 1] ≤
      Pr{let table ← $ᵗ (Fin 2 → Fin 2)}[table 0 = table 1] +
        Pr{let hash ← $ᵗ (Fin 6 → Fin 2)}[Collision hash] := by
  rw [chain_equal, direct_equal, chain_collision, ENNReal.div_add_div_same]
  numerals

/-! ### Absorbing a constant at zero difficulty -/

/-- A validator that requests one bit, possibly after a pinned zero-difficulty
witness. -/
inductive Op where
  | pinned
  | draw
  deriving DecidableEq

abbrev signature : PIR.Signature where
  Op := Op
  Reply
    | .pinned => Unit
    | .draw => Fin 2

inductive Event where
  | pinned
  | draw
  deriving DecidableEq

abbrev Raw : Event → Type := fun _ => Fin 2

/-- The pinned witness is absorbed as a constant event. -/
def absorb : Typed.Interface signature Event Unit Raw
  | .pinned => .send .pinned ()
  | .draw => .query .draw fun raw => some raw

/-- Without the pinned witness: draw and return the bit. -/
def ungated : PIR.Process signature (Fin 2) := .call Op.draw fun bit => .done bit

/-- With the pinned witness absorbed first. -/
def pinnedFirst : PIR.Process signature (Fin 2) := .call Op.pinned fun _ => ungated

/-- A challenge function that reads the length of its key: the absorbed history
before the occurrence, followed by the occurrence. -/
def byLength : (preceding : List Event) → (event : Event) → Raw event :=
  fun preceding event => if (preceding ++ [event]).length = 1 then 0 else 1

theorem ungated_transform :
    Typed.transform (m := Id) absorb byLength ungated [] [] = (.returned 0, []) := rfl

theorem pinned_transform :
    Typed.transform (m := Id) absorb byLength pinnedFirst [] [] = (.returned 1, []) := rfl

theorem pinned_differs :
    Typed.transform (m := Id) absorb byLength ungated [] [] ≠
      Typed.transform (m := Id) absorb byLength pinnedFirst [] [] := by
  rw [ungated_transform, pinned_transform]
  intro same
  exact absurd (congrArg Prod.fst same) (by decide)

/-- The construction that absorbs the pinned witness is not the ungated
construction: they differ for some challenge function. -/
theorem pinned_not_correct :
    ¬ ConstructionCorrect (fun challenge => Typed.transform (m := Id) absorb challenge ungated [] [])
      (fun challenge => Typed.transform (m := Id) absorb challenge pinnedFirst [] []) :=
  fun correct => pinned_differs (correct byLength)

end TestsSecurity.Counterexamples.Couplings
