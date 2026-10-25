module

public import ZkcSecurity.Families.Sumcheck.TableReference
public import ZkcSecurity.Families.Sumcheck.FactorReference
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! Mathematical obligations for the exposed negated-storage experiment. These
prove a representation map, not its unresolved actual helper/process binding. -/

namespace TestsSecurity.ReferenceDiscovery
open Zkc.Polynomial.Multilinear ZkcSecurity.Families.Sumcheck

variable {F : Type} [Field F]

def encode {n : Nat} (table : Table F n) : Table F n := fun bits => - table bits

theorem encode_total {n : Nat} (table : Table F n) :
    -booleanSum (encode table) = booleanSum table := by
  suffices h : booleanSum (encode table) = -booleanSum table by rw [h, neg_neg]
  induction n with
  | zero => rfl
  | succ n ih =>
    change booleanSum (encode (half table false)) + booleanSum (encode (half table true)) =
      -(booleanSum (half table false) + booleanSum (half table true))
    rw [ih, ih, neg_add]

theorem encode_update {n : Nat} (table : Table F (n + 1)) (r : F) :
    fixFirst (encode table) r = encode (fixFirst table r) := by
  funext bits
  simp only [fixFirst, half, encode]
  ring

/-- The representation map is involutive, so private residuals can be decoded. -/
theorem encode_decode {n : Nat} (table : Table F n) : encode (encode table) = table := by
  funext bits
  simp [encode]

/-- The same installed reference laws remain available in every arm. -/
example : ReferenceLaws (TableReference.data F) 1 := TableReference.laws
example : ReferenceLaws (FactorReference.data F) 2 := FactorReference.laws

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev K := ZMod 7
private def coordinate : Table K 1 := fun bits => if bits 0 then 1 else 0

example : ∀ b : Bool, (if b then (1 : K) else 0) ^ 2 = (if b then (1 : K) else 0) := by
  intro b
  cases b <;> decide +kernel

example : (2 : K) ^ 2 ≠ 2 := by decide +kernel

/-- This refusal is about the future observation, not only the initial sum. -/
example : (TableReference.data K).total
      ((TableReference.data K).restrict (fun bits => coordinate bits * coordinate bits) 2) ≠
    (FactorReference.data K).total
      ((FactorReference.data K).restrict (coordinate, coordinate) 2) := by
  change ((1 - 2) * (0 * 0) + 2 * (1 * 1) : K) ≠
    ((1 - 2) * 0 + 2 * 1) * ((1 - 2) * 0 + 2 * 1)
  decide +kernel

example : 6 % 2 = 0 ∧ (6 / 2) % 2 ≠ 0 := by decide

/-- A false scalar claim cannot make the mathematical reference undefined. -/
example : (0 : K) ≠ (TableReference.data K).total (fun _ : Fin 0 → Bool => 1) ∧
    (TableReference.data K).admissible (fun _ : Fin 0 → Bool => 1) := by
  exact ⟨by decide +kernel, trivial⟩

end TestsSecurity.ReferenceDiscovery
