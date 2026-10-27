module

public import ZkcSecurity.Realizations.Gkr.HonestLineShift

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

/-- The literal callback of helper69, retained for structural reassociation. -/
def lineLoopBody : Region dialect
    [.index, .vector "bls12-381.fr", .index, .vector "bls12-381.fr",
      .vector "bls12-381.fr", .index]
    [.vector "bls12-381.fr", .index, .vector "bls12-381.fr",
      .vector "bls12-381.fr", .index] :=
    .letOp (.mark "s14") .nil .nil <|
    .letOp (.invoke ⟨"zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", .local, [.vector "bls12-381.fr", .index], [.field "bls12-381.fr"]⟩) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)) .nil <|
    .letOp (.mark "s16") .nil .nil <|
    .letOp (.invoke ⟨"zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", .local, [.vector "bls12-381.fr", .index], [.field "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there .here))) .nil)) .nil <|
    .letOp (.mark "s18") .nil .nil <|
    .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there .here))) .nil) .nil <|
    .letOp (.mark "s22") .nil .nil <|
    .letOp (.invoke GkrSourceBodies.scopedHelper66Helper) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) .nil <|
    .letOp (.mark "s26") .nil .nil <|
    .letOp (.invoke GkrSourceBodies.scopedHelper67Helper) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
    .letOp (.mark "s27") .nil .nil <|
    .letOp (.invoke GkrSourceBodies.scopedHelper70Helper) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons .here .nil))) .nil <|
    .letOp (.mark "s29") .nil .nil <|
    .letOp (.invoke ⟨"zkl_3d3958243128671a7ae06c730aba5c78b4cae61932510ab43ba5bcabe7324295", .local, [.vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)) .nil <|
    .letOp (.mark "s30") .nil .nil <|
    .letOp (.invoke GkrSourceBodies.scopedHelper73Helper) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
    .letOp (.mark "s32") .nil .nil <|
    .letOp (.exec (.indexConstant 1)) .nil .nil <|
    .letOp (.mark "s33") .nil .nil <|
    .letOp (.exec (.indexAdd)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons .here .nil)) .nil <|
    .ret (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) .nil)))))

theorem line_body_eq : GkrSourceBodies.helper69Body = (
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.indexAdd)) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke ⟨"zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35", .local, [.vector "bls12-381.fr", .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s13") .nil .nil <|
  .letOp (.loop [.vector "bls12-381.fr", .index] [.vector "bls12-381.fr", .vector "bls12-381.fr", .index]) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there .here)) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there .here)))) .nil))))))) (.cons lineLoopBody .nil) <|
  .ret (.cons .here .nil)
) := rfl

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem loop_body (table : Meanings F G) (index : Nat) (xs start finish : List F)
    (position count : Nat) :
    lineLoopBody.denote (meaning F G table)
      (Values.cons index (.cons xs (.cons position
        (.cons start (.cons finish (.cons count .nil)))))).get =
      (invoke table GkrSourceBodies.helper57Helper
        (.cons start (.cons position .nil))).bind fun low =>
      (invoke table GkrSourceBodies.helper57Helper
        (.cons finish (.cons position .nil))).bind fun high =>
      (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorSplit "bls12-381.fr")
        (.cons xs .nil))).bind fun halves =>
      (invoke table GkrSourceBodies.scopedHelper66Helper
        (.cons (halves.get .here) (.cons (halves.get (.there .here))
          (.cons (low.get .here) .nil)))).bind fun base =>
      (invoke table GkrSourceBodies.scopedHelper67Helper
        (.cons (high.get .here) (.cons (low.get .here) .nil))).bind fun delta =>
      (invoke table GkrSourceBodies.scopedHelper70Helper
        (.cons (halves.get .here) (.cons (halves.get (.there .here))
          (.cons (delta.get .here) .nil)))).bind fun rise =>
      (invoke table GkrSourceBodies.helper66Helper
        (.cons (rise.get .here) (.cons count .nil))).bind fun shifted =>
      (invoke table GkrSourceBodies.scopedHelper73Helper
        (.cons (base.get .here) (.cons (shifted.get .here) .nil))).bind fun total =>
      (primitiveOutcome (Primitive.evaluate (F := F) (G := G) .indexAdd
        (.cons position (.cons 1 .nil)))).bind fun next =>
      .done (.cons (total.get .here) (.cons (next.get .here)
        (.cons start (.cons finish (.cons count .nil))))) := by
  derive_process

/-- One reached iteration follows the original checked read/map/fold ABI. -/
theorem loop_step (index : Nat) (xs start finish : List F) (position count m : Nat)
    (shape : xs.length = 2 * m) (nonempty : 0 < m)
    (bound : xs.length < indexLimit) (startBound : start.length < indexLimit)
    (finishBound : finish.length < indexLimit) (positionBound : position + 1 < indexLimit)
    (countBound : count < indexLimit) (positive : 0 < count) :
    lineLoopBody.denote (meaning F G (helpers (F := F) (G := G)))
      (Values.cons index (.cons xs (.cons position
        (.cons start (.cons finish (.cons count .nil)))))).get =
      .done (.cons (step count xs (start[position]?.getD 0) (finish[position]?.getD 0))
        (.cons (position + 1) (.cons start (.cons finish (.cons count .nil))))) := by
  have positionSmall : position < indexLimit := by omega
  have halfSize : xs.length / 2 = m := by omega
  have leftSize : (xs.take (xs.length / 2)).length = m := by simp [halfSize]; omega
  have rightSize : (xs.drop (xs.length / 2)).length = m := by simp [halfSize]; omega
  have split : primitiveOutcome (Primitive.evaluate (F := F) (G := G)
      (.vectorSplit "bls12-381.fr") (.cons xs .nil)) =
      (.done (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) .nil)) :
        Closed (Values (assignment F G)
          [.vector "bls12-381.fr", .vector "bls12-381.fr"])) := by
    simp only [Primitive.evaluate, primitiveOutcome,
      show 0 < xs.length ∧ xs.length % 2 = 0 by omega, and_self, ite_true]
  rw [loop_body, HonestHelpers.element_equation start position startBound positionSmall]
  simp only [PIR.Process.bind, Values.get]
  rw [HonestHelpers.element_equation finish position finishBound positionSmall]
  simp only [PIR.Process.bind, Values.get, split]
  dsimp only [Primitive.results, Values.get]
  rw [base_map _ _ _
    (by change (xs.drop (xs.length / 2)).length = (xs.take (xs.length / 2)).length; omega)
    (by omega)]
  simp only [PIR.Process.bind, Values.get]
  rw [difference]
  simp only [PIR.Process.bind, Values.get]
  rw [slope_map _ _ _ (by omega)
    (by change (xs.drop (xs.length / 2)).length = (xs.take (xs.length / 2)).length; omega)]
  simp only [PIR.Process.bind, Values.get]
  rw [shift_rows _ count (by simp only [List.length_zipWith, leftSize]; omega)
    countBound positive]
  simp only [PIR.Process.bind, Values.get]
  rw [total_map _ _
    (by simp only [linePoints, List.length_zipWith, leftSize]; omega)
    (by simp only [linePoints, shiftAux_length, List.length_zipWith])]
  simp only [PIR.Process.bind, Values.get, Primitive.evaluate, primitiveOutcome, checkedIndices,
    positionSmall, positionBound, show 1 < indexLimit by decide +kernel, and_self, ite_true]
  rfl

theorem line_body (table : Meanings F G) (values start finish : List F) (width : Nat)
    (small : width + 1 < indexLimit) :
    GkrSourceBodies.helper69Body.denote (meaning F G table)
      (Values.cons values (.cons start (.cons finish (.cons width .nil)))).get =
      (invoke table GkrSourceBodies.helper52Helper
        (.cons [] (.cons width (.cons values .nil)))).bind fun initial =>
      (Evaluation.denoteLoop [.vector "bls12-381.fr", .index]
        [.vector "bls12-381.fr", .vector "bls12-381.fr", .index]
        (fun args => lineLoopBody.denote (meaning F G table) args.get)
        0 width (.cons (initial.get .here) (.cons 0 .nil))
        (.cons start (.cons finish (.cons (width + 1) .nil)))).bind fun result =>
      .done (.cons (result.get .here) .nil) := by
  have widthBound : width < indexLimit := by omega
  rw [line_body_eq]
  simp only [Region.denote, meaning, Evaluation.meaning, Evaluation.operation, Operands.eval,
    Regions.denote, Values.get_cons, Environment.prepend, Environment.push,
    SiteObservations.closed, SiteObservations.silent, PIR.Process.bind, Primitive.evaluate,
    primitiveOutcome, checkedIndices, widthBound, small,
    show 0 < indexLimit by decide +kernel, show 1 < indexLimit by decide +kernel,
    and_self, ite_true, Values.split]
  congr 1
  funext initial
  rcases initial with _ | ⟨initial, _ | _⟩
  simp only [Environment.prepend, Environment.push, Values.get]
  congr 1
  funext result
  rcases result with _ | ⟨result, _ | ⟨position, _ | _⟩⟩
  rfl

/-- All reached vector and index bounds are derived from initial capacity.
The pure row invariant is maintained by the actual counted loop. -/
theorem loop_invariant (values start finish : List F) (width : Nat)
    (shape : values.length = 2 ^ width)
    (capacity : 2 ^ width * (width + 1) < indexLimit)
    (startBound : start.length < indexLimit) (finishBound : finish.length < indexLimit) :
    Evaluation.denoteLoop [.vector "bls12-381.fr", .index]
      [.vector "bls12-381.fr", .vector "bls12-381.fr", .index]
      (fun args => lineLoopBody.denote (meaning F G (helpers (F := F) (G := G))) args.get)
      0 width (.cons (pack (width + 1) (values.map C)) (.cons 0 .nil))
      (.cons start (.cons finish (.cons (width + 1) .nil))) =
      .done (.cons (pack (width + 1) (stage values start finish width)) (.cons width .nil)) := by
  have countBound : width + 1 < indexLimit :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by positivity)) capacity
  have stateBound (i : Nat) (inside : i ≤ width) :
      (pack (width + 1) (stage values start finish i)).length < indexLimit := by
    rw [pack_length, stage_length values start finish width i shape inside]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))) capacity
  apply denoteLoop_states (F := F) (G := G) [.vector "bls12-381.fr", .index]
    [.vector "bls12-381.fr", .vector "bls12-381.fr", .index] _ width _
    (.cons start (.cons finish (.cons (width + 1) .nil)))
    (fun i => .cons (pack (width + 1) (stage values start finish i)) (.cons i .nil)) rfl
  intro i inside
  have degreeStep : width - i = (width - (i + 1)) + 1 := by omega
  have rowShape : (stage values start finish i).length = 2 * 2 ^ (width - (i + 1)) := by
    rw [stage_length values start finish width i shape (by omega), degreeStep, pow_succ,
      Nat.mul_comm]
  have packedShape : (pack (width + 1) (stage values start finish i)).length =
      2 * (2 ^ (width - (i + 1)) * (width + 1)) := by
    rw [pack_length, rowShape, Nat.mul_assoc]
  simp only [Evaluation.invokeCallback, Values.append]
  rw [loop_step i _ start finish i (width + 1)
    (2 ^ (width - (i + 1)) * (width + 1)) packedShape (by positivity)
    (stateBound i (by omega)) startBound finishBound (by omega) countBound (by omega),
    step_pack (width + 1) _ _ _ (2 ^ (width - (i + 1))) (by omega) rowShape]
  change PIR.Process.done (Values.cons
    (pack (width + 1) (restrictValues (stage values start finish i) (coordinate start finish i)))
    (.cons (i + 1) (.cons start (.cons finish (.cons (width + 1) .nil)))) :
      Values (assignment F G) [.vector "bls12-381.fr", .index,
        .vector "bls12-381.fr", .vector "bls12-381.fr", .index]) = _
  rw [← stage_succ]

/-- Actual helper69, for all admitted cube tables and all bounded coordinate
vectors. No premise assumes a helper or whole producer is correct. -/
theorem line_coefficients (values start finish : List F) (width : Nat)
    (shape : values.length = 2 ^ width)
    (capacity : 2 ^ width * (width + 1) < indexLimit)
    (startBound : start.length < indexLimit) (finishBound : finish.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper69Helper
      (.cons values (.cons start (.cons finish (.cons width .nil)))) =
      .done (.cons (pack (width + 1) (stage values start finish width)) .nil) := by
  have countBound : width + 1 < indexLimit :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by positivity)) capacity
  have valuesBound : values.length < indexLimit := by
    rw [shape]
    exact lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) capacity
  rw [helper69_association.invoke unit.linked, line_body _ values start finish width countBound,
    constant_rows values [] width valuesBound (by omega)]
  change (Evaluation.denoteLoop [.vector "bls12-381.fr", .index]
    [.vector "bls12-381.fr", .vector "bls12-381.fr", .index]
    (fun args => lineLoopBody.denote (meaning F G (helpers (F := F) (G := G))) args.get)
    0 width (.cons (values.flatMap (fun v => v :: List.replicate width 0)) (.cons 0 .nil))
    (.cons start (.cons finish (.cons (width + 1) .nil)))).bind _ = _
  rw [← pack_constants, loop_invariant values start finish width shape capacity startBound finishBound]
  rfl

/-- The actual result is exactly `width + 1` constant-first coefficients of the
independent core line polynomial, including its highest possible coefficient. -/
theorem coefficients_correspond (width : Nat) (values start finish : List F)
    (table : Table F width) (decoded : ofList? width values = some table)
    (startSize : start.length = width) (finishSize : finish.length = width)
    (capacity : 2 ^ width * (width + 1) < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper69Helper
      (.cons values (.cons start (.cons finish (.cons width .nil)))) =
      .done (.cons (row (width + 1)
        (linePolynomial width table (coordinates width start) (coordinates width finish))) .nil) := by
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
