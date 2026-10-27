module

public import ZkcExamples.Structured.SumcheckHelperLaws
public import Zkc.Protocols.Sumcheck.Multilinear.Reduction

@[expose] public section
namespace ZkcExamples.Structured.SumcheckHelperLaws
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws SumcheckHelperBodies
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open Zkc.Protocols.Sumcheck.Multilinear (honestMessage)

variable {bindings : MultilinearPrefixBodies.Bindings}
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] {n : Nat}

/-- Sums checks dimension representability, but never width or the shape predicate. -/
theorem sums_honestMessage_generic_body (helpers : Meanings F G) (halves : HalvesLaw helpers)
    (xs : List F) (table : Table F (n + 1)) (columns : Nat)
    (decoded : ofList? (n + 1) xs = some table) (dimensionBound : n + 1 < indexLimit) :
    sumsBody.denote (meaning F G helpers) (inputs xs (n + 1) columns).get =
      .done (messageResult (honestMessage table).1 (honestMessage table).2) := by
  have length := ofList?_length xs table decoded
  have split : 0 < xs.length ∧ xs.length % 2 = 0 := by
    rw [length, Nat.pow_succ]
    constructor
    · exact Nat.mul_pos (Nat.pow_pos (by decide)) (by decide)
    · omega
  rw [sums_generic_body helpers halves xs (n + 1) columns dimensionBound,
    ite_eq_left (Nat.zero_lt_succ _), ite_eq_left split]
  have low := booleanSum_ofList? _ _ (decode_low_half xs table decoded)
  have high := booleanSum_ofList? _ _ (decode_high_half xs table decoded)
  rw [← low, ← high]
  rfl

/-- The original one-column shaped form is a corollary of the width-independent law. -/
theorem sums_honestMessage_shaped (helpers : Meanings F G) (halves : HalvesLaw helpers)
    (xs : List F) (table : Table F (n + 1)) (shape : HasShape xs (n + 1) 1)
    (decoded : ofList? (n + 1) xs = some table) :
    sumsBody.denote (meaning F G helpers) (inputs xs (n + 1) 1).get =
      .done (messageResult (honestMessage table).1 (honestMessage table).2) :=
  sums_honestMessage_generic_body helpers halves xs table 1 decoded
    (Nat.lt_trans shape.2.1 (by decide +kernel))

/-- Public check agrees with the existing mathematical checker, also for malformed vectors. -/
theorem check_mathematical (helpers : Meanings F G) (laws : MapPrefixContracts.Laws helpers bindings)
    (callback : ∀ (xs point : List F) (claim : F),
      invoke helpers checkTableHelper (checkInputs xs point claim) =
        (checkTableBody bindings).denote (meaning F G helpers) (checkInputs xs point claim).get)
    (xs point : List F) (claim : F) (vectorBound : xs.length < indexLimit)
    (pointBound : point.length < indexLimit) :
    checkBody.denote (meaning F G helpers) (checkInputs xs point claim).get =
      .done (boolResult (Zkc.Protocols.Sumcheck.Multilinear.check
        (n := 0 + point.length) xs
        (Quadratic.point point.length (coordinates point.length point) Fin.elim0) claim)) := by
  rw [check_generic_body helpers laws callback xs point claim vectorBound pointBound]
  cases decoded : ofList? (0 + point.length) xs with
  | none =>
    have malformed : ¬ HasShape xs point.length 1 := by
      intro shape
      have present := (ofList?_isSome_iff (n := 0 + point.length) xs).mpr
        (by simpa only [Nat.zero_add, Nat.mul_one] using shape.length)
      rw [decoded] at present
      contradiction
    simp only [malformed, false_and, decide_false,
      Zkc.Protocols.Sumcheck.Multilinear.check, decoded]
  | some table =>
    have shape : HasShape xs point.length 1 := (hasShape_iff_length xs point.length vectorBound).mpr
      (by simpa only [Nat.zero_add] using ofList?_length xs table decoded)
    rw [complete_prefix_sum xs point table decoded]
    have pointEq : Quadratic.point point.length (coordinates point.length point) Fin.elim0 =
        coordinates (0 + point.length) point := by
      have empty : (Fin.elim0 : Fin 0 → F) = coordinates 0 [] := by
        funext i; exact Fin.elim0 i
      rw [empty, point_coordinates (n := 0) point.length point [] rfl rfl, List.append_nil]
    simp only [shape, true_and, Zkc.Protocols.Sumcheck.Multilinear.check, decoded, pointEq]

/-- Decoding and vector representability imply every successful dimension/point bound. -/
theorem check_mle_generic_body (helpers : Meanings F G) (laws : MapPrefixContracts.Laws helpers bindings)
    (callback : ∀ (xs point : List F) (claim : F),
      invoke helpers checkTableHelper (checkInputs xs point claim) =
        (checkTableBody bindings).denote (meaning F G helpers) (checkInputs xs point claim).get)
    (xs point : List F) (claim : F) (table : Table F (0 + point.length))
    (decoded : ofList? (0 + point.length) xs = some table)
    (vectorBound : xs.length < indexLimit) :
    checkBody.denote (meaning F G helpers) (checkInputs xs point claim).get =
      .done (boolResult (decide (extension (0 + point.length) table
        (coordinates (0 + point.length) point) = claim))) := by
  have shape := (hasShape_iff_length xs point.length vectorBound).mpr
    (by simpa only [Nat.zero_add] using ofList?_length xs table decoded)
  have pointBound : point.length < indexLimit := Nat.lt_trans shape.2.1 (by decide +kernel)
  rw [check_generic_body helpers laws callback xs point claim vectorBound pointBound,
    complete_prefix_sum xs point table decoded]
  simp only [shape, true_and]

/-- A decoded representable table supplies the constructor and point bounds. -/
theorem checkTable_mle_generic_body (helpers : Meanings F G) (laws : MapPrefixContracts.Laws helpers bindings)
    (xs point : List F) (claim : F) (table : Table F (0 + point.length))
    (decoded : ofList? (0 + point.length) xs = some table)
    (vectorBound : xs.length < indexLimit) :
    (checkTableBody bindings).denote (meaning F G helpers) (checkInputs xs point claim).get =
      .done (boolResult (decide (extension (0 + point.length) table
        (coordinates (0 + point.length) point) = claim))) := by
  have shape := (hasShape_iff_length xs point.length vectorBound).mpr
    (by simpa only [Nat.zero_add] using ofList?_length xs table decoded)
  have pointBound : point.length < indexLimit := Nat.lt_trans shape.2.1 (by decide +kernel)
  rw [checkTable_generic_body helpers laws xs point claim vectorBound pointBound,
    ite_eq_left shape, complete_prefix_sum xs point table decoded]

end ZkcExamples.Structured.SumcheckHelperLaws
