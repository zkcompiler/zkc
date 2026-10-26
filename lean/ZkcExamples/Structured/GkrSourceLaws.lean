module

public import ZkcExamples.Structured.GkrSourceViews
public import ZkcExamples.Structured.MapPrefixContracts
public import ZkcExamples.Structured.SumcheckHelperLaws
public import ZkcExamples.Structured.MapSourceExpansions
public import Zkc.Source.Structured.MapLaws
public import Zkc.Construction.Uniform.ProjectionSoundness
public import Zkc.Polynomial.Multilinear.ListRestriction
public import Zkc.Polynomial.Multilinear.Line

@[expose] public section

/-! Equations for the helpers the GKR verifier calls, read from the admitted
source's own helper table.

The standard multilinear and vector helpers of the unit are associated with the
bodies of the completed map packages, whose laws then apply unchanged; the GKR
library's own helpers are associated with their literal bodies in
`GkrSourceBodies`. Every equation below is about the closed meanings of the
admitted unit (`helpers`), which is the helper table of the admitted program
(`helperTable_eq`): the extension of a table at a complete point (`evaluate`),
the sum of a vector, the block of a stacked table at a position
(`selectBlock`), the extension of a wiring block at three concatenated points
(`evaluateWiring`), the power sum of line coefficients
(`evaluateCoefficients`) and the point on the line through two points
(`linePoint`). The `call_*` forms state them for the exported programs' helper
calls on transcript values.
-/

namespace ZkcExamples.Structured.GkrSourceLaws
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws MapPrefixLaws
open MapPrefixBodies GkrSourceViews
open Zkc.Polynomial Zkc.Polynomial.Multilinear


set_option maxRecDepth 20000 in
structured_associations GkrSourceViews
  [empty := SumcheckHelperBodies.empty, append := SumcheckHelperBodies.append,
    helper2 := MapFirstBodies.less, helper3 := MapFirstBodies.rows,
    helper4 := MapFirstBodies.shape, helper5 := MapFirstBodies.table,
    helper6 := MapFirstBodies.halves, helper7 := MapFirstBodies.interpolate,
    helper8 := MapFirstBodies.map, helper9 := MapFirstBodies.first,
    helper10 := MapPrefixBodies.step, helper11 := MapPrefixBodies.foldStep,
    helper12 := MapPrefixBodies.fold, helper13 := MapPrefixBodies.foldWrapper,
    helper14 := MapPrefixBodies.prefix, helper15 := MapFirstBodies.values,
    helper16 := MapFirstBodies.valuesRealization,
    evaluate := GkrSourceBodies.evaluate, helper18 := GkrSourceBodies.helper18,
    selectBlock := GkrSourceBodies.selectBlock, helper42 := GkrSourceBodies.helper42,
    helper43 := GkrSourceBodies.helper43, sum := GkrSourceBodies.sum,
    evaluateWiring := GkrSourceBodies.evaluateWiring, helper73 := GkrSourceBodies.helper73,
    helper74 := GkrSourceBodies.helper74, helper75 := GkrSourceBodies.helper75,
    helper76 := GkrSourceBodies.helper76, helper77 := GkrSourceBodies.helper77,
    helper78 := GkrSourceBodies.helper78, helper79 := GkrSourceBodies.helper79,
    helper80 := GkrSourceBodies.helper80,
    evaluateCoefficients := GkrSourceBodies.evaluateCoefficients,
    linePoint := GkrSourceBodies.linePoint]

theorem first_bodies : MapFirstContracts.Bodies unit.definitions :=
  ⟨helper2_association, helper3_association, helper4_association, helper5_association,
    helper6_association, helper7_association, helper8_association, helper9_association⟩

theorem prefix_bodies : MapPrefixContracts.Bodies unit.definitions :=
  ⟨helper10_association, helper11_association, helper12_association, helper13_association,
    helper14_association, helper15_association, helper16_association⟩

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The closed meanings of the admitted unit's helpers. -/
abbrev helpers : Meanings F G := closedMeanings unit.definitions

theorem prefix_laws : MapPrefixContracts.Laws (helpers (F := F) (G := G)) :=
  MapPrefixContracts.laws_of_bodies unit.linked prefix_bodies first_bodies

/-! ## Vectors -/

theorem empty_equation :
    invoke (helpers (F := F) (G := G)) SumcheckHelperBodies.emptyHelper .nil = .done (.cons [] .nil) :=
  (empty_association.invoke unit.linked .nil).trans (SumcheckHelperLaws.empty_body _)

theorem append_equation (xs : List F) (x : F) :
    invoke (helpers (G := G)) SumcheckHelperBodies.appendHelper (.cons xs (.cons x .nil)) =
      .done (.cons (xs ++ [x]) .nil) :=
  (append_association.invoke unit.linked (.cons xs (.cons x .nil))).trans
    (SumcheckHelperLaws.append_body _ xs x)

theorem sum_body (table : Meanings F G) (xs : List F) :
    GkrSourceBodies.sumBody.denote (meaning F G table) (Values.cons xs .nil).get =
      .done (.cons (xs.foldl (· + ·) 0) .nil) := rfl

theorem sum_equation (xs : List F) :
    invoke (helpers (G := G)) GkrSourceBodies.sumHelper (.cons xs .nil) = .done (.cons xs.sum .nil) := by
  rw [(sum_association.invoke unit.linked (.cons xs .nil)).trans (sum_body _ xs), List.sum_eq_foldl]

/-! ## Extensions at complete points -/

set_option backward.isDefEq.respectTransparency false in
/-- The table constructor, the prefix restriction at the point, the values
and their sum. -/
theorem evaluate_expansion (table : Meanings F G) (xs point : List F)
    (pointBound : point.length < indexLimit) :
    GkrSourceBodies.evaluateBody.denote (meaning F G table) (Values.cons xs (.cons point .nil)).get =
      (invoke table tableHelper (inputs xs point.length 1)).bind fun constructed =>
      (invoke table prefixHelper (constructed.append (.cons point .nil))).bind fun residual =>
      (invoke table valuesRealizationHelper residual).bind fun values =>
      .done (.cons (values.get .here).sum .nil) := by
  simp only [GkrSourceBodies.evaluateBody, inputs, Region.denote, meaning,
    Evaluation.meaning, Evaluation.operation, Operands.eval, Regions.denote,
    Values.get_cons, Values.get, SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    SumcheckHelperLaws.prepend_three,
    Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Process.bind, Primitive.evaluate, pointBound, ite_true, primitiveOutcome,
    show 1 < indexLimit by decide +kernel, ← List.sum_eq_foldl]
  congr 1
  funext constructed
  cases constructed with
  | cons xs rest =>
    cases rest with
    | cons n rest =>
      cases rest with
      | cons w rest =>
        cases rest
        congr 1
        funext residual
        cases residual with
        | cons xs rest =>
          cases rest with
          | cons n rest =>
            cases rest with
            | cons w rest => cases rest; rfl

theorem evaluate_generic_body (table : Meanings F G) (laws : MapPrefixContracts.Laws table)
    (xs point : List F) (vectorBound : xs.length < indexLimit) (pointBound : point.length < indexLimit) :
    GkrSourceBodies.evaluateBody.denote (meaning F G table) (Values.cons xs (.cons point .nil)).get =
      if HasShape xs point.length 1 then .done (.cons (restrictPrefixValues xs point).sum .nil)
      else .halt .reject := by
  rw [evaluate_expansion table xs point pointBound,
    laws.tableLaw xs point.length 1 vectorBound pointBound (by decide +kernel)]
  by_cases shape : HasShape xs point.length 1
  · simp only [shape, ite_true, PIR.Process.bind]
    change (invoke table prefixHelper (prefixInputs xs point.length 1 point)).bind _ = _
    rw [laws.fixPrefix xs point.length 1 point shape vectorBound pointBound]
    simp only [Nat.le_refl, ite_true, Nat.sub_self, PIR.Process.bind]
    rw [laws.values]
    rfl
  · simp only [shape, ite_false, PIR.Process.bind]

theorem evaluate_equation (xs point : List F) (vectorBound : xs.length < indexLimit)
    (pointBound : point.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.evaluateHelper (.cons xs (.cons point .nil)) =
      if HasShape xs point.length 1 then .done (.cons (restrictPrefixValues xs point).sum .nil)
      else .halt .reject :=
  (evaluate_association.invoke unit.linked (.cons xs (.cons point .nil))).trans
    (evaluate_generic_body _ prefix_laws xs point vectorBound pointBound)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Restricting a decoded table at a complete point leaves its extension
there. -/
theorem prefix_sum_extension (n : Nat) (xs point : List F) (table : Table F n)
    (decoded : ofList? n xs = some table) (length : point.length = n) :
    (restrictPrefixValues xs point).sum = extension n table (coordinates n point) := by
  have dimension : 0 + point.length = n := by omega
  subst dimension
  exact complete_prefix_sum xs point table decoded

/-- A decoded table of the point's dimension: the extension at the point. -/
theorem evaluate_extension (n : Nat) (xs point : List F) (table : Table F n)
    (decoded : ofList? n xs = some table) (length : point.length = n) (small : n < 64)
    (vectorBound : xs.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.evaluateHelper (.cons xs (.cons point .nil)) =
      .done (.cons (extension n table (coordinates n point)) .nil) := by
  have pointBound : point.length < indexLimit := by
    rw [length]; exact Nat.lt_trans small (by decide +kernel)
  have shape : HasShape xs point.length 1 := by
    refine ⟨by decide, by omega, Nat.mod_one _, ?_⟩
    rw [Nat.div_one, ofList?_length xs table decoded, length]
  rw [evaluate_equation xs point vectorBound pointBound, ite_eq_left shape,
    prefix_sum_extension n xs point table decoded length]

set_option backward.isDefEq.respectTransparency false in
/-- Three prefix restrictions of a table constructed at the summed dimension. -/
theorem evaluateWiring_expansion (table : Meanings F G) (xs gate left right : List F)
    (gateBound : gate.length < indexLimit) (leftBound : left.length < indexLimit)
    (rightBound : right.length < indexLimit) (pairBound : gate.length + left.length < indexLimit)
    (sumBound : gate.length + left.length + right.length < indexLimit) :
    GkrSourceBodies.evaluateWiringBody.denote (meaning F G table)
        (Values.cons xs (.cons gate (.cons left (.cons right .nil)))).get =
      (invoke table tableHelper (inputs xs (gate.length + left.length + right.length) 1)).bind
        fun constructed =>
      (invoke table prefixHelper (constructed.append (.cons gate .nil))).bind fun first =>
      (invoke table prefixHelper (first.append (.cons left .nil))).bind fun second =>
      (invoke table prefixHelper (second.append (.cons right .nil))).bind fun third =>
      (invoke table valuesRealizationHelper third).bind fun values =>
      .done (.cons (values.get .here).sum .nil) := by
  simp only [GkrSourceBodies.evaluateWiringBody, inputs, Region.denote, meaning,
    Evaluation.meaning, Evaluation.operation, Operands.eval, Regions.denote,
    Values.get_cons, Values.get, SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    SumcheckHelperLaws.prepend_three,
    Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Process.bind, Primitive.evaluate, checkedIndices, gateBound, leftBound, rightBound, pairBound,
    sumBound, and_self, ite_true, primitiveOutcome, show 1 < indexLimit by decide +kernel,
    ← List.sum_eq_foldl]
  congr 1
  funext constructed
  cases constructed with
  | cons xs rest =>
    cases rest with
    | cons n rest =>
      cases rest with
      | cons w rest =>
        cases rest
        congr 1
        funext first
        cases first with
        | cons xs rest =>
          cases rest with
          | cons n rest =>
            cases rest with
            | cons w rest =>
              cases rest
              congr 1
              funext second
              cases second with
              | cons xs rest =>
                cases rest with
                | cons n rest =>
                  cases rest with
                  | cons w rest =>
                    cases rest
                    congr 1
                    funext third
                    cases third with
                    | cons xs rest =>
                      cases rest with
                      | cons n rest =>
                        cases rest with
                        | cons w rest => cases rest; rfl

/-- Representable points of total length `n` and a table of `2 ^ n` values:
the values restricted at the concatenated point, summed. -/
theorem evaluateWiring_equation (xs gate left right : List F)
    (vectorBound : xs.length < indexLimit) (small : gate.length + left.length + right.length < 64)
    (shape : xs.length = 2 ^ (gate.length + left.length + right.length)) :
    invoke (helpers (G := G)) GkrSourceBodies.evaluateWiringHelper
        (.cons xs (.cons gate (.cons left (.cons right .nil)))) =
      .done (.cons (restrictPrefixValues xs (gate ++ left ++ right)).sum .nil) := by
  have bound : gate.length + left.length + right.length < indexLimit :=
    Nat.lt_trans small (by decide +kernel)
  have laws := prefix_laws (F := F) (G := G)
  refine (evaluateWiring_association.invoke unit.linked _).trans ?_
  rw [evaluateWiring_expansion _ xs gate left right (by omega) (by omega) (by omega) (by omega) bound,
    laws.tableLaw xs _ 1 vectorBound bound (by decide +kernel)]
  have tableShape : HasShape xs (gate.length + left.length + right.length) 1 :=
    ⟨by decide, small, Nat.mod_one _, by rw [Nat.div_one, shape]⟩
  simp only [tableShape, ite_true, PIR.Process.bind]
  change (invoke _ prefixHelper (prefixInputs xs (gate.length + left.length + right.length) 1 gate)).bind _ = _
  rw [laws.fixPrefix xs _ 1 gate tableShape vectorBound (by omega)]
  simp only [show gate.length ≤ gate.length + left.length + right.length by omega, ite_true,
    PIR.Process.bind]
  have firstLength : (restrictPrefixValues xs gate).length = 2 ^ (left.length + right.length) := by
    apply restrictPrefixValues_length
    rw [shape]; congr 1; omega
  have firstShape : HasShape (restrictPrefixValues xs gate)
      (gate.length + left.length + right.length - gate.length) 1 :=
    ⟨by decide, by omega, Nat.mod_one _, by rw [Nat.div_one, firstLength]; congr 1; omega⟩
  have firstBound : (restrictPrefixValues xs gate).length < indexLimit := by
    rw [firstLength]
    have below : 2 ^ (left.length + right.length) ≤ 2 ^ (gate.length + left.length + right.length) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have small' : 2 ^ (gate.length + left.length + right.length) < 2 ^ 64 :=
      Nat.pow_lt_pow_right (by decide) small
    unfold indexLimit
    omega
  change (invoke _ prefixHelper (prefixInputs (restrictPrefixValues xs gate)
    (gate.length + left.length + right.length - gate.length) 1 left)).bind _ = _
  rw [laws.fixPrefix _ _ 1 left firstShape firstBound (by omega)]
  simp only [show left.length ≤ gate.length + left.length + right.length - gate.length by omega,
    ite_true, PIR.Process.bind]
  have secondLength : (restrictPrefixValues (restrictPrefixValues xs gate) left).length =
      2 ^ right.length := by
    apply restrictPrefixValues_length
    rw [firstLength, Nat.add_comm]
  have secondShape : HasShape (restrictPrefixValues (restrictPrefixValues xs gate) left)
      (gate.length + left.length + right.length - gate.length - left.length) 1 :=
    ⟨by decide, by omega, Nat.mod_one _, by rw [Nat.div_one, secondLength]; congr 1; omega⟩
  have secondBound : (restrictPrefixValues (restrictPrefixValues xs gate) left).length < indexLimit := by
    rw [secondLength]
    have below : 2 ^ right.length ≤ 2 ^ (gate.length + left.length + right.length) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have small' : 2 ^ (gate.length + left.length + right.length) < 2 ^ 64 :=
      Nat.pow_lt_pow_right (by decide) small
    unfold indexLimit
    omega
  change (invoke _ prefixHelper (prefixInputs (restrictPrefixValues (restrictPrefixValues xs gate) left)
    (gate.length + left.length + right.length - gate.length - left.length) 1 right)).bind _ = _
  rw [laws.fixPrefix _ _ 1 right secondShape secondBound (by omega)]
  simp only [show right.length ≤ gate.length + left.length + right.length - gate.length - left.length
    by omega, ite_true, PIR.Process.bind]
  rw [laws.values]
  simp only [restrictPrefixValues_append]
  rfl

/-- A decoded wiring block at points of the width: the extension at the
concatenated point. -/
theorem evaluateWiring_extension (w : Nat) (xs gate left right : List F)
    (table : Table F (w + w + w)) (decoded : ofList? (w + w + w) xs = some table)
    (gateLength : gate.length = w) (leftLength : left.length = w) (rightLength : right.length = w)
    (small : w + w + w < 64) (vectorBound : xs.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.evaluateWiringHelper
        (.cons xs (.cons gate (.cons left (.cons right .nil)))) =
      .done (.cons (extension (w + w + w) table
        (coordinates (w + w + w) (gate ++ left ++ right))) .nil) := by
  have lengths : gate.length + left.length + right.length = w + w + w := by omega
  rw [evaluateWiring_equation xs gate left right vectorBound (by omega)
    (by rw [lengths]; exact ofList?_length xs table decoded)]
  have pointLength : (gate ++ left ++ right).length = w + w + w := by simp; omega
  rw [prefix_sum_extension (w + w + w) xs _ table decoded pointLength]

/-! ## Line points -/

theorem helper42_body_eq : GkrSourceBodies.helper42Body = MapFirstBodies.interpolateBody := rfl

theorem interpolate_equation (low high r : F) :
    invoke (helpers (G := G)) GkrSourceBodies.helper42Helper (.cons low (.cons high (.cons r .nil))) =
      .done (.cons (low + (high - low) * r) .nil) := by
  refine (helper42_association.invoke unit.linked (.cons low (.cons high (.cons r .nil)))).trans ?_
  rw [helper42_body_eq, MapSourceExpansions.first_interpolate]
  rfl

theorem map_body (table : Meanings F G) (start finish : List F) (t : F) :
    GkrSourceBodies.helper43Body.denote (meaning F G table)
        (Values.cons start (.cons finish (.cons t .nil))).get =
      (Evaluation.denoteMap table ⟨GkrSourceBodies.helper42Helper.name, "bls12-381.fr", [true, true, false]⟩
        (.cons start (.cons finish (.cons t .nil))) :
          PIR.Process closedInterface (Values (assignment F G) [.vector "bls12-381.fr"])).bind fun result =>
      .done (.cons (result.get .here) .nil) := by
  derive_process

theorem map_equation (start finish : List F) (t : F) (sameLength : finish.length = start.length)
    (small : start.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper43Helper (.cons start (.cons finish (.cons t .nil))) =
      .done (.cons (linePoints start finish t) .nil) := by
  refine (helper43_association.invoke unit.linked (.cons start (.cons finish (.cons t .nil)))).trans ?_
  rw [map_body]
  have mapped := Evaluation.denoteMap_twoRows_broadcast (helpers (F := F) (G := G))
    GkrSourceBodies.helper42Helper.name "bls12-381.fr" start finish t small sameLength
    (fun low high => low + (high - low) * t) (fun low high => interpolate_equation low high t)
  rw [mapped]
  rfl

theorem linePoint_body (table : Meanings F G) (start finish : List F) (t : F) :
    GkrSourceBodies.linePointBody.denote (meaning F G table)
        (Values.cons start (.cons finish (.cons t .nil))).get =
      (invoke table GkrSourceBodies.helper43Helper (.cons start (.cons finish (.cons t .nil)))).bind
        fun result => .done (.cons (result.get .here) .nil) := by
  derive_process

theorem linePoint_equation (start finish : List F) (t : F) (sameLength : finish.length = start.length)
    (small : start.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.linePointHelper (.cons start (.cons finish (.cons t .nil))) =
      .done (.cons (linePoints start finish t) .nil) := by
  refine (linePoint_association.invoke unit.linked (.cons start (.cons finish (.cons t .nil)))).trans ?_
  rw [linePoint_body, map_equation start finish t sameLength small]
  rfl

/-! ## Line coefficients -/

/-- The fold of `evaluate_coefficients` over the coefficient vector, with the
state `(accumulated, power)` and the point as its capture. -/
abbrev powerFold : FoldSpec :=
  ⟨⟨"finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_domain",
    [.vector "bls12-381.fr"], (.vector "bls12-381.fr"), .here, false⟩,
    [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"],
    "finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body", "", .local⟩

theorem helper73_body (table : Meanings F G) (accumulated power coefficient point : F) :
    GkrSourceBodies.helper73Body.denote (meaning F G table)
        (Values.cons accumulated (.cons power (.cons coefficient (.cons point .nil)))).get =
      .done (.cons (accumulated + coefficient * power) (.cons (power * point) .nil)) := rfl

theorem helper74_body (table : Meanings F G) (accumulated power coefficient point : F) :
    GkrSourceBodies.helper74Body.denote (meaning F G table)
        (Values.cons accumulated (.cons power (.cons coefficient (.cons point .nil)))).get =
      (invoke table GkrSourceBodies.helper73Helper
        (.cons accumulated (.cons power (.cons coefficient (.cons point .nil))))).bind fun result =>
      .done (.cons (result.get .here) (.cons (result.get (.there .here)) .nil)) := by
  derive_process

theorem helper75_body (table : Meanings F G) (accumulated power coefficient point : F) :
    GkrSourceBodies.helper75Body.denote (meaning F G table)
        (Values.cons accumulated (.cons power (.cons coefficient (.cons point .nil)))).get =
      (invoke table GkrSourceBodies.helper74Helper
        (.cons accumulated (.cons power (.cons coefficient (.cons point .nil))))).bind fun result =>
      .done (.cons (result.get .here) (.cons (result.get (.there .here)) .nil)) := by
  derive_process

theorem helper78_body (table : Meanings F G) (accumulated power coefficient : F)
    (coefficients : List F) (point : F) :
    GkrSourceBodies.helper78Body.denote (meaning F G table)
        (Values.cons accumulated (.cons power (.cons coefficient (.cons coefficients
          (.cons point .nil))))).get =
      (invoke table GkrSourceBodies.helper75Helper
        (.cons accumulated (.cons power (.cons coefficient (.cons point .nil))))).bind fun result =>
      .done (.cons (result.get .here) (.cons (result.get (.there .here)) .nil)) := by
  derive_process

theorem helper76_body (table : Meanings F G) :
    GkrSourceBodies.helper76Body.denote (meaning F G table) (Values.nil).get =
      .done (.cons ((0 : Nat) : F) (.cons ((1 : Nat) : F) .nil)) := rfl

theorem helper77_body (table : Meanings F G) :
    GkrSourceBodies.helper77Body.denote (meaning F G table) (Values.nil).get =
      (invoke table GkrSourceBodies.helper76Helper .nil).bind fun result =>
      .done (.cons (result.get .here) (.cons (result.get (.there .here)) .nil)) := by
  derive_process

theorem helper79_body (table : Meanings F G) (coefficients : List F) (accumulated power point : F) :
    GkrSourceBodies.helper79Body.denote (meaning F G table)
        (Values.cons coefficients (.cons accumulated (.cons power (.cons point .nil)))).get =
      (Evaluation.denoteFold table powerFold
        (.cons coefficients (.cons accumulated (.cons power (.cons point .nil))))).bind fun result =>
      .done (.cons (result.get .here) (.cons (result.get (.there .here)) .nil)) := by
  derive_process

theorem helper80_body (table : Meanings F G) (accumulated power point : F) (coefficients : List F) :
    GkrSourceBodies.helper80Body.denote (meaning F G table)
        (Values.cons accumulated (.cons power (.cons point (.cons coefficients .nil)))).get =
      (invoke table GkrSourceBodies.helper79Helper
        (.cons coefficients (.cons accumulated (.cons power (.cons point .nil))))).bind fun result =>
      .done (.cons (result.get .here) (.cons (result.get (.there .here)) .nil)) := by
  derive_process

theorem evaluateCoefficients_body (table : Meanings F G) (coefficients : List F) (point : F) :
    GkrSourceBodies.evaluateCoefficientsBody.denote (meaning F G table)
        (Values.cons coefficients (.cons point .nil)).get =
      (invoke table GkrSourceBodies.helper77Helper .nil).bind fun start =>
      (invoke table GkrSourceBodies.helper80Helper (.cons (start.get .here)
        (.cons (start.get (.there .here)) (.cons point (.cons coefficients .nil))))).bind fun result =>
      .done (.cons (result.get .here) .nil) := by
  derive_process

theorem powerStep_equation (accumulated power coefficient point : F) :
    invoke (helpers (G := G)) GkrSourceBodies.helper75Helper
        (.cons accumulated (.cons power (.cons coefficient (.cons point .nil)))) =
      .done (.cons (accumulated + coefficient * power) (.cons (power * point) .nil)) := by
  rw [helper75_association.invoke unit.linked, helper75_body,
    helper74_association.invoke unit.linked, helper74_body,
    helper73_association.invoke unit.linked, helper73_body]
  rfl

theorem step_equation (accumulated power coefficient : F) (coefficients : List F) (point : F) :
    invoke (helpers (G := G)) GkrSourceBodies.helper78Helper
        (.cons accumulated (.cons power (.cons coefficient (.cons coefficients (.cons point .nil))))) =
      .done (.cons (accumulated + coefficient * power) (.cons (power * point) .nil)) := by
  rw [helper78_association.invoke unit.linked, helper78_body, powerStep_equation]
  rfl

theorem powerStart_equation :
    invoke (helpers (F := F) (G := G)) GkrSourceBodies.helper77Helper .nil =
      .done (.cons 0 (.cons 1 .nil)) := by
  rw [helper77_association.invoke unit.linked, helper77_body,
    helper76_association.invoke unit.linked, helper76_body]
  simp only [Nat.cast_zero, Nat.cast_one]
  rfl

/-- The fold's step on the state `(accumulated, power)` and a coefficient. -/
def powerTransition (point : F) (state : F × F) (coefficient : F) : F × F :=
  (state.1 + coefficient * state.2, state.2 * point)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem powerTransition_fold (point : F) (coefficients : List F) (accumulated power : F) :
    coefficients.foldl (powerTransition point) (accumulated, power) =
      (accumulated + power * powerSum coefficients point, power * point ^ coefficients.length) := by
  induction coefficients generalizing accumulated power with
  | nil => simp [powerSum]
  | cons coefficient rest ih =>
      simp only [List.foldl_cons, powerTransition, ih, powerSum, List.length_cons, pow_succ]
      ext <;> simp only <;> ring

/-- The fold's step on structured values. -/
def powerReference (point : F) (state : Values (assignment F G) powerFold.state) (coefficient : F) :
    Values (assignment F G) powerFold.state :=
  .cons (state.get .here + coefficient * state.get (.there .here))
    (.cons (state.get (.there .here) * point) .nil)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem powerReference_fold (point : F) (coefficients : List F) (accumulated power : F) :
    coefficients.foldl (powerReference (G := G) point) (.cons accumulated (.cons power .nil)) =
      .cons (coefficients.foldl (powerTransition point) (accumulated, power)).1
        (.cons (coefficients.foldl (powerTransition point) (accumulated, power)).2 .nil) := by
  induction coefficients generalizing accumulated power with
  | nil => rfl
  | cons coefficient rest ih => exact ih _ _

theorem fold_equation (coefficients : List F) (accumulated power point : F)
    (small : coefficients.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper79Helper
        (.cons coefficients (.cons accumulated (.cons power (.cons point .nil)))) =
      .done (.cons (coefficients.foldl (powerTransition point) (accumulated, power)).1
        (.cons (coefficients.foldl (powerTransition point) (accumulated, power)).2 .nil)) := by
  rw [helper79_association.invoke unit.linked, helper79_body]
  have folded := Evaluation.denoteFold_reference (helpers (F := F) (G := G)) powerFold
    (.cons coefficients .nil) (.cons accumulated (.cons power .nil)) (.cons point .nil) coefficients
    (Evaluation.elements_admit _ _ _ _ _ small) (powerReference point) (fun _ => True) trivial
    (by
      intro state coefficient _ _
      refine ⟨?_, trivial⟩
      rw [Evaluation.foldTransition_unfiltered _ _ rfl]
      rcases state with _ | ⟨current, _ | ⟨currentPower, _ | _⟩⟩
      exact step_equation current currentPower coefficient coefficients point)
  change (Evaluation.denoteFold _ powerFold ((Values.cons coefficients .nil).append
    ((Values.cons accumulated (.cons power .nil)).append (.cons point .nil)))).bind _ = _
  rw [folded]
  exact congrArg (fun result : Values (assignment F G) powerFold.state =>
    (PIR.Process.done (Values.cons (result.get .here) (.cons (result.get (.there .here)) .nil)) :
      PIR.Process closedInterface (Values (assignment F G) [.field "bls12-381.fr", .field "bls12-381.fr"])))
    (powerReference_fold point coefficients accumulated power)

theorem evaluateCoefficients_equation (coefficients : List F) (point : F)
    (small : coefficients.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.evaluateCoefficientsHelper
        (.cons coefficients (.cons point .nil)) =
      .done (.cons (powerSum coefficients point) .nil) := by
  rw [evaluateCoefficients_association.invoke unit.linked, evaluateCoefficients_body,
    powerStart_equation]
  change (invoke (helpers (G := G)) GkrSourceBodies.helper80Helper
    (.cons 0 (.cons 1 (.cons point (.cons coefficients .nil))))).bind _ = _
  rw [helper80_association.invoke unit.linked, helper80_body, fold_equation coefficients 0 1 point small,
    powerTransition_fold]
  simp only [PIR.Process.bind, Values.get, zero_add, one_mul]

/-! ## Blocks of stacked tables -/

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- A counted loop whose state after each iteration is given. -/
theorem denoteLoop_states {I : PIR.Signature} (state captures : List Ty)
    (body : RegionFunction (assignment F G) I (.index :: (state ++ captures), state ++ captures))
    (count : Nat) (initial : Values (assignment F G) state)
    (captured : Values (assignment F G) captures) (states : Nat → Values (assignment F G) state)
    (start : states 0 = initial)
    (law : ∀ index, index < count →
      Evaluation.invokeCallback body (.cons index ((states index).append captured)) =
        .done ((states (index + 1)).append captured)) :
    Evaluation.denoteLoop state captures body 0 count initial captured = .done (states count) := by
  subst start
  simp only [Evaluation.denoteLoop, Finite.execute, Finite.Domain.admit, Finite.admitThen, Nat.sub_zero]
  have folded := Finite.fold_range_state
    (fun current index => (Evaluation.invokeCallback body (.cons index (current.append captured))).bind
      fun results => (.done (results.split state).1 : PIR.Process I _)) states 0 count (by
        intro index _ upper
        rw [law index (by omega)]
        simp only [PIR.Process.bind, Values.split_append])
  simpa using folded

set_option backward.isDefEq.respectTransparency false in
theorem powerOfTwo_body (table : Meanings F G) (exponent : Nat) (small : exponent < 64) :
    GkrSourceBodies.helper18Body.denote (meaning F G table) (Values.cons exponent .nil).get =
      .done (.cons (2 ^ exponent) .nil) := by
  have exponentBound : exponent < indexLimit := Nat.lt_trans small (by decide +kernel)
  simp only [GkrSourceBodies.helper18Body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Regions.denote, Values.get_cons, Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Process.bind, Primitive.evaluate, primitiveOutcome, show 1 < indexLimit by decide +kernel,
    show 0 < indexLimit by decide +kernel, ite_true, Values.split]
  rw [denoteLoop_states (F := F) (G := G) [.index] [] _ exponent _ .nil
    (fun index => .cons (2 ^ index) .nil) ?start ?law]
  · rfl
  case start => rfl
  case law =>
    intro index lower
    have current : 2 ^ index < indexLimit := by
      unfold indexLimit
      exact Nat.pow_lt_pow_right (by decide) (by omega)
    have product : 2 ^ index * 2 < indexLimit := by
      rw [← Nat.pow_succ]
      exact Nat.pow_lt_pow_right (by decide) (by omega : index + 1 < 64)
    simp only [Evaluation.invokeCallback, Values.get_cons, Environment.prepend, Environment.push, PIR.Process.bind, checkedIndices, current, product,
      show 2 < indexLimit by decide +kernel, and_self, ite_true, Values.append, Nat.pow_succ]

theorem powerOfTwo_equation (exponent : Nat) (small : exponent < 64) :
    invoke (helpers (F := F) (G := G)) GkrSourceBodies.helper18Helper (.cons exponent .nil) =
      .done (.cons (2 ^ exponent) .nil) :=
  (helper18_association.invoke unit.linked _).trans (powerOfTwo_body _ exponent small)

/-- The block of `size` values at `position`. -/
def block (xs : List F) (position size : Nat) : List F := (xs.drop (position * size)).take size

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem block_length (xs : List F) (position size : Nat) (inside : (position + 1) * size ≤ xs.length) :
    (block xs position size).length = size := by
  simp only [block, List.length_take, List.length_drop]
  rw [Nat.add_mul, Nat.one_mul] at inside
  omega

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The two halves of a block of even size are the blocks of half the size. -/
theorem block_halves (xs : List F) (position half : Nat) :
    (block xs position (2 * half)).take half = block xs (2 * position) half ∧
      (block xs position (2 * half)).drop half = block xs (2 * position + 1) half := by
  constructor
  · simp only [block, List.take_take]
    rw [Nat.min_eq_left (by omega : half ≤ 2 * half)]
    congr 2
    ring
  · simp only [block, List.drop_take, List.drop_drop]
    rw [show 2 * half - half = half by omega]
    congr 2
    ring

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem block_whole (xs : List F) (size : Nat) (whole : xs.length = size) : block xs 0 size = xs := by
  simp [block, ← whole]

/-- The position's leading bits above `r - 1`: twice those above `r`, plus the
bit at `r - 1`. -/
theorem position_split (position r : Nat) (positive : 1 ≤ r) :
    position / 2 ^ (r - 1) = 2 * (position / 2 ^ r) + position / 2 ^ (r - 1) % 2 := by
  have above : position / 2 ^ r = position / 2 ^ (r - 1) / 2 := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ, Nat.sub_add_cancel positive]
  rw [above]
  exact (Nat.div_add_mod _ 2).symm

omit [CommRing F] [DecidableEq F] in
/-- One iteration of the selection: the block at the leading bits above
`r - 1`, from the block at the leading bits above `r`. -/
theorem block_step (xs : List F) (position size r : Nat) (positive : 1 ≤ r) :
    (if position / 2 ^ (r - 1) % 2 = 1 then
        (block xs (position / 2 ^ r) (size * 2 ^ r)).drop (size * 2 ^ (r - 1))
      else (block xs (position / 2 ^ r) (size * 2 ^ r)).take (size * 2 ^ (r - 1))) =
      block xs (position / 2 ^ (r - 1)) (size * 2 ^ (r - 1)) := by
  have doubled : size * 2 ^ r = 2 * (size * 2 ^ (r - 1)) := by
    rw [show r = (r - 1) + 1 by omega, pow_succ]
    simp only [Nat.add_sub_cancel]
    ring
  rw [doubled]
  obtain ⟨low, high⟩ := block_halves xs (position / 2 ^ r) (size * 2 ^ (r - 1))
  have split := position_split position r positive
  split
  · rename_i bit
    rw [high, split, bit]
  · rename_i bit
    have zero : position / 2 ^ (r - 1) % 2 = 0 := by omega
    rw [low, split, zero, Nat.add_zero]

/-- The loop body of `select_block`: one MSB-first bit of the position
selects one half of the current block. -/
def selectLoopBody : Region dialect [.index, .vector "bls12-381.fr", .index, .index]
    [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.exec (.indexSub)) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.invoke ⟨"s3h676b7212h706f7765725f6f665f74776f", .local, [.index], [.index]⟩) (.cons .here .nil) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.exec (.indexDiv)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s10") .nil .nil <|
  .letOp (.exec (.indexConstant 2)) .nil .nil <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.exec (.indexMod)) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s13") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil) .nil <|
  .letOp (.mark "s15") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s16") .nil .nil <|
  .letOp (.exec (.indexEqual)) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s19") .nil .nil <|
  .letOp (.branch [.vector "bls12-381.fr", .vector "bls12-381.fr"] [.vector "bls12-381.fr"]) (.cons .here (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))) (.cons (
    .ret (.cons (.there .here) .nil)) (.cons (
    .ret (.cons .here .nil)) .nil)) <|
  .ret (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)))

theorem selectBlockBody_eq : GkrSourceBodies.selectBlockBody = (
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.loop [.vector "bls12-381.fr", .index] [.index]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there .here) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil))))) (.cons selectLoopBody .nil) <|
  .ret (.cons .here .nil)) := rfl

theorem selectLoop_body (table : Meanings F G) (index : Nat) (current : List F) (remaining position : Nat) :
    selectLoopBody.denote (meaning F G table)
      ((.cons index (.cons current (.cons remaining (.cons position .nil)))) :
        Values (assignment F G) [.index, .vector "bls12-381.fr", .index, .index]).get =
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexConstant 1) .nil) :
      Closed (Values (assignment F G) [.index])).bind fun result0 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexSub)
      (.cons remaining (.cons (result0.get .here) .nil))) :
      Closed (Values (assignment F G) [.index])).bind fun result1 =>
    (invoke table GkrSourceBodies.helper18Helper (.cons (result1.get .here) .nil) :
      Closed (Values (assignment F G) [.index])).bind fun result2 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexDiv)
      (.cons position (.cons (result2.get .here) .nil))) :
      Closed (Values (assignment F G) [.index])).bind fun result3 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexConstant 2) .nil) :
      Closed (Values (assignment F G) [.index])).bind fun result4 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexMod)
      (.cons (result3.get .here) (.cons (result4.get .here) .nil))) :
      Closed (Values (assignment F G) [.index])).bind fun result5 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorSplit "bls12-381.fr") (.cons current .nil)) :
      Closed (Values (assignment F G) [.vector "bls12-381.fr", .vector "bls12-381.fr"])).bind fun result6 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexConstant 1) .nil) :
      Closed (Values (assignment F G) [.index])).bind fun result7 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexEqual)
      (.cons (result5.get .here) (.cons (result7.get .here) .nil))) :
      Closed (Values (assignment F G) [.boolean])).bind fun result8 =>
    (if (result8.get .here) then
      .done (.cons (result6.get (.there .here)) .nil)
    else .done (.cons (result6.get .here) .nil) :
      Closed (Values (assignment F G) [.vector "bls12-381.fr"])).bind fun result9 =>
    .done (.cons (result9.get .here) (.cons (result1.get .here) (.cons position .nil))) := by
  derive_process using (exact branch_law _ _ _ _ _ _)

set_option backward.isDefEq.respectTransparency false in
theorem selectBlock_equation (xs : List F) (position bits size : Nat)
    (shape : xs.length = 2 ^ bits * size) (positive : 0 < size) (inside : position < 2 ^ bits)
    (vectorBound : xs.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.selectBlockHelper
        (.cons xs (.cons position (.cons bits .nil))) =
      .done (.cons (block xs position size) .nil) := by
  have powerBound : 2 ^ bits < indexLimit := by
    refine Nat.lt_of_le_of_lt ?_ vectorBound
    rw [shape]
    exact Nat.le_mul_of_pos_right _ positive
  have bitsSmall : bits < 64 := by
    by_contra large
    have : 2 ^ 64 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) (by omega)
    exact absurd powerBound (by unfold indexLimit; omega)
  have positionBound : position < indexLimit := Nat.lt_trans inside powerBound
  refine (selectBlock_association.invoke unit.linked _).trans ?_
  rw [selectBlockBody_eq]
  simp only [Region.denote, meaning, Evaluation.meaning, Evaluation.operation, Operands.eval,
    Regions.denote, Values.get_cons, Environment.prepend, Environment.push,
    SiteObservations.closed, SiteObservations.silent, PIR.Process.bind, Primitive.evaluate,
    primitiveOutcome, show 0 < indexLimit by decide +kernel, ite_true, Values.split]
  rw [denoteLoop_states (F := F) (G := G) [.vector "bls12-381.fr", .index] [.index] _ bits _
    (.cons position .nil)
    (fun index => .cons (block xs (position / 2 ^ (bits - index)) (size * 2 ^ (bits - index)))
      (.cons (bits - index) .nil)) ?start ?law]
  · simp only [Nat.sub_self, pow_zero, Nat.div_one, Nat.mul_one, PIR.Process.bind]
    rfl
  case start =>
    have zero : position / 2 ^ bits = 0 := Nat.div_eq_of_lt inside
    simp only [Nat.sub_zero, zero]
    rw [block, Nat.zero_mul, List.drop_zero, Nat.mul_comm, ← shape, List.take_length]
  case law =>
    intro index lower
    have remaining : 1 ≤ bits - index := by omega
    have remainingBound : bits - index < indexLimit :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_trans bitsSmall (by decide +kernel))
    have power := powerOfTwo_equation (F := F) (G := G) (bits - index - 1) (by omega)
    have powerSmall : 2 ^ (bits - index - 1) < indexLimit :=
      Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega)) powerBound
    have powerPositive : 2 ^ (bits - index - 1) ≠ 0 := by positivity
    have quotientBound : position / 2 ^ (bits - index - 1) < indexLimit :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) positionBound
    have bitBound : position / 2 ^ (bits - index - 1) % 2 < indexLimit :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide +kernel)
    have above : position / 2 ^ (bits - index) < 2 ^ index := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
      exact inside
    have blockLength :
        (block xs (position / 2 ^ (bits - index)) (size * 2 ^ (bits - index))).length =
          size * 2 ^ (bits - index) := by
      apply block_length
      rw [shape]
      calc (position / 2 ^ (bits - index) + 1) * (size * 2 ^ (bits - index))
          ≤ 2 ^ index * (size * 2 ^ (bits - index)) := Nat.mul_le_mul_right _ above
        _ = 2 ^ bits * size := by
          rw [Nat.mul_left_comm, ← Nat.pow_add, Nat.add_sub_cancel' (by omega), Nat.mul_comm]
    have blockPositive : 0 < size * 2 ^ (bits - index) := by positivity
    have doubled : size * 2 ^ (bits - index) = 2 * (size * 2 ^ (bits - index - 1)) := by
      rw [show bits - index = (bits - index - 1) + 1 by omega, pow_succ]
      simp only [Nat.add_sub_cancel]
      ring
    have blockEven : size * 2 ^ (bits - index) % 2 = 0 := by rw [doubled]; simp
    have half : size * 2 ^ (bits - index) / 2 = size * 2 ^ (bits - index - 1) := by
      rw [doubled]; simp
    have next : bits - (index + 1) = bits - index - 1 := by omega
    have step := block_step xs position size (bits - index) remaining
    simp only [Evaluation.invokeCallback, Values.append]
    show Region.denote (meaning F G (helpers (F := F) (G := G))) selectLoopBody _ = _
    rw [selectLoop_body]
    simp only [Primitive.evaluate, primitiveOutcome, checkedIndices, PIR.Process.bind, Values.get,
      show 1 < indexLimit by decide +kernel, show 2 < indexLimit by decide +kernel, remaining,
      remainingBound, power, powerSmall, powerPositive, positionBound, quotientBound, blockLength, blockPositive, blockEven, half, and_self, ite_true, ite_false, next,
      true_and, and_true]
    by_cases bit : position / 2 ^ (bits - index - 1) % 2 = 1
    · simp only [bit, ite_true] at step ⊢
      rw [← step]
      simp [PIR.Process.bind, Values.get, show (1 : Nat) < indexLimit by decide +kernel]
      rfl
    · simp only [bit, ite_false] at step ⊢
      rw [← step]
      simp [PIR.Process.bind, Values.get, bit, bitBound]

/-! ## Helper calls of exported programs -/

theorem helperTable_eq : Zkc.Construction.helperTable program F G = helpers (F := F) (G := G) := rfl

end ZkcExamples.Structured.GkrSourceLaws
