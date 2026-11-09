module

public import Mathlib.Data.List.Basic

@[expose] public section

/-! Canonical ascending coefficients without selecting algebra on the carrier.
The zero witness is explicit data. A field model checks it against its own zero
before consuming a polynomial. Thus two ring structures on one carrier never
silently share a polynomial interpretation. -/

namespace Zkc.Source.Structured

def CoefficientsCanonical {α : Type} (zero : α) : List α → Prop
  | [] => True
  | a :: rest => (rest = [] → a ≠ zero) ∧ CoefficientsCanonical zero rest

def normalizeCoefficients {α : Type} [DecidableEq α] (zero : α) : List α → List α
  | [] => []
  | a :: rest =>
    let tail := normalizeCoefficients zero rest
    if tail = [] ∧ a = zero then [] else a :: tail

theorem normalizeCoefficients_canonical {α : Type} [DecidableEq α] (zero : α)
    (values : List α) : CoefficientsCanonical zero (normalizeCoefficients zero values) := by
  induction values with
  | nil => trivial
  | cons a rest ih =>
    simp only [normalizeCoefficients]
    split
    · trivial
    · rename_i h
      exact ⟨fun empty equal ↦ h ⟨empty, equal⟩, ih⟩

theorem normalizeCoefficients_of_canonical {α : Type} [DecidableEq α] (zero : α)
    (values : List α) (canonical : CoefficientsCanonical zero values) :
    normalizeCoefficients zero values = values := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    rcases canonical with ⟨last, tail⟩
    simp only [normalizeCoefficients, ih tail]
    split
    · rename_i h
      exact False.elim (last h.1 h.2)
    · rfl

@[simp] theorem normalizeCoefficients_idempotent {α : Type} [DecidableEq α] (zero : α)
    (values : List α) : normalizeCoefficients zero (normalizeCoefficients zero values) =
      normalizeCoefficients zero values :=
  normalizeCoefficients_of_canonical zero _ (normalizeCoefficients_canonical zero values)

theorem normalizeCoefficients_length_le {α : Type} [DecidableEq α] (zero : α)
    (values : List α) : (normalizeCoefficients zero values).length ≤ values.length := by
  induction values with
  | nil => exact Nat.le_refl 0
  | cons a rest ih =>
    simp only [normalizeCoefficients]
    split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ ih

@[simp] theorem normalizeCoefficients_replicate {α : Type} [DecidableEq α] (zero : α)
    (n : Nat) : normalizeCoefficients zero (List.replicate n zero) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, normalizeCoefficients, ih]

/-- Nominal polynomial values. The explicit witness avoids requiring instances
on `Carriers`; numerical consumers refuse a witness different from model zero. -/
structure PolynomialValue (α : Type) where
  zero : α
  coefficients : List α
  canonical : CoefficientsCanonical zero coefficients
  deriving DecidableEq

def PolynomialValue.ofCoefficients {α : Type} [DecidableEq α] (zero : α)
    (values : List α) : PolynomialValue α :=
  ⟨zero, normalizeCoefficients zero values, normalizeCoefficients_canonical zero values⟩

@[simp] theorem PolynomialValue.roundtrip {α : Type} [DecidableEq α]
    (value : PolynomialValue α) :
    ofCoefficients value.zero value.coefficients = value := by
  cases value with
  | mk zero coefficients canonical =>
    simp only [ofCoefficients, normalizeCoefficients_of_canonical zero coefficients canonical]

end Zkc.Source.Structured
