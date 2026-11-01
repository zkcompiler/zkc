module

public import ZkcSecurityExamples.Gkr.HonestLineShift

@[expose] public section

/-! The actual checked line-coefficient loop and its parametric invariant. -/

namespace ZkcSecurity.Realizations.Gkr.HonestLine
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceViews GkrSourceLaws
open ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Polynomial Zkc.Polynomial.Multilinear CoefficientRows LineCoefficients
open _root_.Polynomial

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
attribute [local implicit_reducible] Collection.type Collection.element Op.arguments Op.results Op.regions
attribute [local implicit_reducible] Primitive.arguments Primitive.results

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- One reached iteration follows the original checked read/map/fold ABI. -/
theorem loop_step (index : Nat) (xs start finish : List F) (position count m : Nat)
    (shape : xs.length = 2 * m) (nonempty : 0 < m)
    (bound : xs.length < indexLimit) (startBound : start.length < indexLimit)
    (finishBound : finish.length < indexLimit) (positionBound : position + 1 < indexLimit)
    (countBound : count < indexLimit) (positive : 0 < count) :
    Goals.lineCallback.denote (Evaluation.meaningOn (ringModel F G) SiteObservations.closed (helpers (F := F) (G := G)))
      (Goals.StepArguments.pack { iteration := index, values := xs, position, start, finish, count }).get =
      .done (Goals.Step.encode (ringModel F G)
        { values := step count xs (start[position]?.getD 0) (finish[position]?.getD 0),
          position := position + 1, start, finish, count }) := by
  have positionSmall : position < indexLimit := by omega
  have halfSize : xs.length / 2 = m := by omega
  have leftSize : (xs.take (xs.length / 2)).length = m := by simp [halfSize]; omega
  have rightSize : (xs.drop (xs.length / 2)).length = m := by simp [halfSize]; omega
  have split : primitiveOutcome (Primitive.evaluateOn (ringFieldModel F G)
      (.vectorSplit "bls12-381.fr") (.cons xs .nil)) =
      (.done (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) .nil)) :
        Closed (Values (assignment F G)
          [.vector "bls12-381.fr", .vector "bls12-381.fr"])) := by
    simp only [Primitive.evaluateOn, primitiveOutcome,
      show 0 < xs.length ∧ xs.length % 2 = 0 by omega, and_self, ite_true]
  simp only [Goals.StepArguments.pack]
  named_process Goals.stepProcess over F G
  rw [HonestHelpers.element_equation start position startBound positionSmall]
  named_reduce
  rw [HonestHelpers.element_equation finish position finishBound positionSmall]
  named_reduce
  rw [split]
  named_reduce
  rw [base_map _ _ _
    (by omega)
    (by omega)]
  named_reduce
  rw [difference]
  named_reduce
  rw [slope_map _ _ _ (by omega)
    (by omega)]
  named_reduce
  rw [shift_rows _ count (by simp only [List.length_zipWith, leftSize]; omega)
    countBound positive]
  named_reduce
  rw [total_map _ _
    (by simp only [linePoints, List.length_zipWith, leftSize]; omega)
    (by simp only [linePoints, shiftAux_length, List.length_zipWith])]
  simp only [PIR.Process.bind, Environment.prepend, Environment.push, Values.get_cons, Values.get, Primitive.evaluateOn, primitiveOutcome, checkedIndices,
    positionSmall, positionBound, show 1 < indexLimit by decide +kernel, and_self, ite_true]
  rfl

/-- All reached vector and index bounds are derived from initial capacity.
The pure row invariant is maintained by the actual counted loop. -/
theorem loop_invariant (values start finish : List F) (width : Nat)
    (shape : values.length = 2 ^ width)
    (capacity : 2 ^ width * (width + 1) < indexLimit)
    (startBound : start.length < indexLimit) (finishBound : finish.length < indexLimit) :
    Evaluation.denoteLoop Goals.LineState.types Goals.LineCaptures.types
      (fun args => Goals.lineCallback.denote (Evaluation.meaningOn (ringModel F G) SiteObservations.closed (helpers (F := F) (G := G))) args.get)
      0 width (Goals.LineState.pack { values := pack (width + 1) (values.map C), position := 0 })
      (Goals.LineCaptures.pack { start, finish, count := width + 1 }) =
      .done (Goals.LineState.pack { values := pack (width + 1) (stage values start finish width), position := width }) := by
  have countBound : width + 1 < indexLimit :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by positivity)) capacity
  have stateBound (i : Nat) (inside : i ≤ width) :
      (pack (width + 1) (stage values start finish i)).length < indexLimit := by
    rw [pack_length, stage_length values start finish width i shape inside]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))) capacity
  apply denoteLoop_states (F := F) (G := G) Goals.LineState.types Goals.LineCaptures.types _ width _
    (Goals.LineCaptures.pack { start, finish, count := width + 1 })
    (fun i => Goals.LineState.pack { values := pack (width + 1) (stage values start finish i), position := i }) rfl
  intro i inside
  have degreeStep : width - i = (width - (i + 1)) + 1 := by omega
  have rowShape : (stage values start finish i).length = 2 * 2 ^ (width - (i + 1)) := by
    rw [stage_length values start finish width i shape (by omega), degreeStep, pow_succ,
      Nat.mul_comm]
  have packedShape : (pack (width + 1) (stage values start finish i)).length =
      2 * (2 ^ (width - (i + 1)) * (width + 1)) := by
    rw [pack_length, rowShape, Nat.mul_assoc]
  have reached := loop_step (G := G) i _ start finish i (width + 1)
    (2 ^ (width - (i + 1)) * (width + 1)) packedShape (by positivity)
    (stateBound i (by omega)) startBound finishBound (by omega) countBound (by omega)
  rw [step_pack (width + 1) _ _ _ (2 ^ (width - (i + 1))) (by omega) rowShape,
    ← coordinate, ← stage_succ] at reached
  simpa only [Evaluation.invokeCallback, Goals.LineState.pack, Goals.LineCaptures.pack,
    Goals.StepArguments.pack, Goals.Step.encode, Values.append] using reached

/-- Actual helper69, for all admitted cube tables and all bounded coordinate
vectors. No premise assumes a helper or whole producer is correct. -/
theorem line_coefficients (values start finish : List F) (width : Nat)
    (shape : values.length = 2 ^ width)
    (capacity : 2 ^ width * (width + 1) < indexLimit)
    (startBound : start.length < indexLimit) (finishBound : finish.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper69Helper
      (Goals.Line.Inputs.pack (Value := assignment F G) { values, start, finish, width }) =
      .done (Goals.Line.encode (ringModel F G) ⟨pack (width + 1) (stage values start finish width)⟩) := by
  have countBound : width + 1 < indexLimit :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by positivity)) capacity
  have valuesBound : values.length < indexLimit := by
    rw [shape]
    exact lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) capacity
  rw [helper69_association.invoke unit.linked]
  named_process Goals.lineProcess over F G
  simp only [Primitive.evaluateOn, primitiveOutcome, checkedIndices,
    show width < indexLimit by omega, countBound,
    show 0 < indexLimit by decide +kernel, show 1 < indexLimit by decide +kernel,
    and_self, ↓reduceIte, PIR.Process.bind, Environment.prepend, Environment.push, Values.get_cons, Values.get]
  rw [constant_rows values [] width valuesBound (by omega)]
  named_reduce
  rw [← Evaluation.denoteLoop_eq_denoteLoopOn (F := F) (G := G)]
  rw [Evaluation.denoteLoop_congr (F := F) (G := G) Goals.LineState.types Goals.LineCaptures.types _
    (fun args => Goals.lineCallback.denote
      (Evaluation.meaningOn (ringModel F G) SiteObservations.closed (helpers (F := F) (G := G))) args.get)
    (by
      intro arguments
      obtain ⟨view, rfl⟩ := Goals.StepArguments.pack_surjective arguments
      symm
      simp only [Goals.StepArguments.pack]
      named_process Goals.stepProcess over F G
      simp only [Primitive.evaluateOn, primitiveOutcome, checkedIndices,
        show 0 < indexLimit by decide +kernel, show 1 < indexLimit by decide +kernel,
        and_self, ↓reduceIte, PIR.Process.bind]
      named_reduce
      simp only [show 0 < indexLimit by decide +kernel, show 1 < indexLimit by decide +kernel,
        and_true, and_self, ↓reduceIte])]
  rw [← pack_constants]
  simp only [List.nil_append]
  erw [loop_invariant (G := G) values start finish width shape capacity startBound finishBound]
  named_reduce

/-- The actual result is exactly `width + 1` constant-first coefficients of the
independent core line polynomial, including its highest possible coefficient. -/
theorem coefficients_correspond (width : Nat) (values start finish : List F)
    (table : Table F width) (decoded : ofList? width values = some table)
    (startSize : start.length = width) (finishSize : finish.length = width)
    (capacity : 2 ^ width * (width + 1) < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper69Helper
      (Goals.Line.Inputs.pack (Value := assignment F G) { values, start, finish, width }) =
      .done (Goals.Line.encode (ringModel F G) ⟨row (width + 1)
        (linePolynomial width table (coordinates width start) (coordinates width finish))⟩) := by
  have countBound : width + 1 < indexLimit :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by positivity)) capacity
  rw [line_coefficients values start finish width (ofList?_length values table decoded) capacity
    (by omega) (by omega), stage_complete width values start finish table decoded]
  simp

omit [DecidableEq F] in
/-- Parametric polynomial equality, rather than agreement at a finite set. -/
theorem polynomial_correspond (width : Nat) (table : Table F width) (start finish : List F) :
    coefficientPolynomial (row (width + 1)
      (linePolynomial width table (coordinates width start) (coordinates width finish))) =
      linePolynomial width table (coordinates width start) (coordinates width finish) :=
  coefficientPolynomial_row _ _ (lt_of_le_of_lt (linePolynomial_natDegree _ _ _) (by omega))

end ZkcSecurity.Realizations.Gkr.HonestLine
