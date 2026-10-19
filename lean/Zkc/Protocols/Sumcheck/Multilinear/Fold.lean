module

public import Zkc.Polynomial.Multilinear.ListRestriction
public import Zkc.Protocols.Sumcheck.Multilinear.Round

@[expose] public section

/-! Prover-side laws of the MSB-first folded table.

An honest multilinear Sumcheck prover keeps a flat table and fixes its leading
coordinate at each received challenge. `PartialEvaluation` says that a flat
list represents the partial evaluation of an original table at an ordered
point: its multilinear extension at every remaining point is the original
extension at the concatenated point. `roundEndpoint` is one endpoint of the
correct round polynomial: the original extension summed over the Boolean
points that complete the received point with a fixed next coordinate. The laws
connect both to the list operations an implementation performs; they assume no
interaction, delivery or challenge distribution.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Multilinear

open Zkc.Polynomial Zkc.Polynomial.Multilinear

variable {F : Type} [CommRing F]

/-- `entries` represents the partial evaluation of `table` at the ordered `point`. -/
def PartialEvaluation {N : Nat} (table : Table F N) (point entries : List F) : Prop :=
  point.length ≤ N ∧ ∃ residual : Table F (N - point.length),
    ofList? (N - point.length) entries = some residual ∧
    ∀ suffix : Fin (N - point.length) → F,
      extension (N - point.length) residual suffix =
        extension N table (coordinates N (point ++ List.ofFn suffix))

/-- The endpoint at `bit` of the correct round polynomial after `point`. -/
def roundEndpoint {N : Nat} (table : Table F N) (point : List F) (bit : F) : F :=
  cubeSum (N - point.length - 1)
    (fun tail => extension N table (coordinates N (point ++ bit :: List.ofFn tail)))

/-- The original flat table represents the partial evaluation at every prefix
that fits its dimension, after ordered list restriction. -/
theorem partialEvaluation_restrict {N : Nat} (raw : List F) (table : Table F N)
    (decoded : ofList? N raw = some table) (point : List F) (fits : point.length ≤ N) :
    PartialEvaluation table point (restrictPrefixValues raw point) := by
  refine ⟨fits, ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + point.length := ⟨N - point.length, (Nat.sub_add_cancel fits).symm⟩
  rw [Nat.add_sub_cancel]
  refine ⟨fixPrefix point.length table (coordinates point.length point),
    ofList?_restrictPrefixValues raw point table decoded, fun suffix => ?_⟩
  rw [extension_fixPrefix, ← coordinates_ofFn suffix,
    point_coordinates point.length point (List.ofFn suffix) rfl (List.length_ofFn), coordinates_ofFn]

/-- Equal-length halves interpolate to the interpolated sums. -/
theorem sum_zipWith_interpolate (low high : List F) (r : F) (same : low.length = high.length) :
    (List.zipWith (fun a b => a + (b - a) * r) low high).sum = (1 - r) * low.sum + r * high.sum := by
  induction low generalizing high with
  | nil =>
    cases high with
    | nil => simp
    | cons _ _ => simp at same
  | cons a low ih =>
    cases high with
    | nil => simp at same
    | cons b high =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      rw [ih high (by simpa using same)]
      ring

/-- One fold maps the claimed sum to the evaluation of the endpoint message. -/
theorem restrictValues_sum (xs : List F) (r : F) (even : xs.length % 2 = 0) :
    (restrictValues xs r).sum =
      (1 - r) * (xs.take (xs.length / 2)).sum + r * (xs.drop (xs.length / 2)).sum := by
  unfold restrictValues
  apply sum_zipWith_interpolate
  simp only [List.length_take, List.length_drop]
  omega

/-- The prover's two half sums are the endpoints of the correct round polynomial. -/
theorem partialEvaluation_endpoints {N : Nat} (table : Table F N) (point entries : List F)
    (represents : PartialEvaluation table point entries) (remaining : point.length < N) :
    (entries.take (entries.length / 2)).sum = roundEndpoint table point 0 ∧
      (entries.drop (entries.length / 2)).sum = roundEndpoint table point 1 := by
  obtain ⟨_, residual, decoded, values⟩ := represents
  obtain ⟨m, hm⟩ : ∃ m, N - point.length = m + 1 := ⟨N - point.length - 1, by omega⟩
  unfold roundEndpoint
  have arity : N - point.length - 1 = m := by omega
  rw [arity]
  revert residual
  rw [hm]
  intro residual decoded values
  have low := booleanSum_ofList? _ _ (decode_low_half entries residual decoded)
  have high := booleanSum_ofList? _ _ (decode_high_half entries residual decoded)
  rw [← low, ← high, ← cubeSum_extension, ← cubeSum_extension]
  constructor
  · congr 1
    funext tail
    have same := values (Fin.cons 0 tail)
    simp only [extension, Fin.cons_zero, sub_zero, one_mul, zero_mul, add_zero] at same
    rw [List.ofFn_succ, Fin.cons_zero] at same
    simp only [Fin.cons_succ] at same
    exact same
  · congr 1
    funext tail
    have same := values (Fin.cons 1 tail)
    simp only [extension, Fin.cons_zero, sub_self, zero_mul, one_mul, zero_add] at same
    rw [List.ofFn_succ, Fin.cons_zero] at same
    simp only [Fin.cons_succ] at same
    exact same

/-- After one received challenge, the folded list represents the next partial evaluation. -/
theorem partialEvaluation_fold {N : Nat} (table : Table F N) (point entries : List F)
    (represents : PartialEvaluation table point entries) (remaining : point.length < N) (r : F) :
    PartialEvaluation table (point ++ [r]) (restrictValues entries r) := by
  obtain ⟨_, residual, decoded, values⟩ := represents
  refine ⟨by simp; omega, ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, N - point.length = m + 1 := ⟨N - point.length - 1, by omega⟩
  have arity : N - (point ++ [r]).length = m := by simp; omega
  rw [arity]
  revert residual
  rw [hm]
  intro residual decoded values
  refine ⟨fixFirst residual r, ofList?_restrictValues entries residual r decoded, fun suffix => ?_⟩
  rw [extension_fixFirst, values (Fin.cons r suffix), List.ofFn_succ, Fin.cons_zero]
  simp only [Fin.cons_succ, List.append_assoc, List.singleton_append]

/-- The represented list sums to the residual claim: the original extension
summed over every Boolean completion of the point. -/
theorem partialEvaluation_sum {N : Nat} (table : Table F N) (point entries : List F)
    (represents : PartialEvaluation table point entries) :
    entries.sum = cubeSum (N - point.length)
      (fun suffix => extension N table (coordinates N (point ++ List.ofFn suffix))) := by
  obtain ⟨_, residual, decoded, values⟩ := represents
  rw [← booleanSum_ofList? entries residual decoded, ← cubeSum_extension]
  congr 1
  funext suffix
  exact values suffix

/-- A complete point leaves exactly the original extension value. -/
theorem partialEvaluation_complete {N : Nat} (table : Table F N) (point entries : List F)
    (represents : PartialEvaluation table point entries) (complete : point.length = N) :
    entries.sum = extension N table (coordinates N point) := by
  rw [partialEvaluation_sum table point entries represents]
  have zero : N - point.length = 0 := by omega
  revert represents
  rw [zero]
  intro _
  simp [cubeSum]

end Zkc.Protocols.Sumcheck.Multilinear
