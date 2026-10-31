module

public import ZkcExamples.Structured.GkrSourceViews
public import Zkc.Protocols.Gkr.Source.VerifierHelperInstallation
public import Zkc.Protocols.Multilinear.Source.MapPrefixContracts
public import Zkc.Protocols.Sumcheck.Source.HelperLaws
public import Zkc.Protocols.Multilinear.Source.MapSourceExpansions
public import Zkc.Protocols.Gkr.Source.BlockLaws
public import Zkc.Source.Structured.MapLaws
public import Zkc.Construction.Structured
public import Zkc.Source.Structured.CollectLaws
public import Zkc.Source.Structured.BodyBindings
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

set_option backward.isDefEq.respectTransparency false

namespace ZkcExamples.Structured.GkrSourceLaws
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws MapPrefixLaws
open MapPrefixBodies GkrSourceViews
open Zkc.Polynomial Zkc.Polynomial.Multilinear


/-- Read an ordered collection from its actual typed body. The proof at each
use checks that this is the body's first operation, rather than guessing an
admission number or a declaration-list position. -/
abbrev collection? {inputs outputs : List Ty} : Region dialect inputs outputs → Option CollectSpec
  | .letOp (.collect spec) _ _ _ => some spec
  | _ => none

/-- The complete current finite fold, with its tuple-valued item ABI. -/
abbrev fold? {inputs outputs : List Ty} : Region dialect inputs outputs → Option FoldSpec
  | .letOp (.fold spec) _ _ _ => some spec
  | _ => none

abbrev firstCollection : CollectSpec :=
  (collection? GkrSourceBodies.helper8Body).get (by decide +kernel)

abbrev lineCollection : CollectSpec :=
  (collection? GkrSourceBodies.sourceHelper110Body).get (by decide +kernel)

abbrev collectBindings : MultilinearCollectBodies.Bindings :=
  ⟨GkrSourceBodies.helper8Helper.name, firstCollection.domain.name,
    firstCollection.body, GkrSourceBodies.interpolateRealizationHelper.name⟩

abbrev prefixBindings : MultilinearPrefixBodies.Bindings :=
  ⟨GkrSourceBodies.helper12Helper.name, GkrSourceBodies.helper16Helper.name⟩

abbrev lineBindings : MultilinearCollectBodies.Bindings :=
  ⟨GkrSourceBodies.sourceHelper110Helper.name, lineCollection.domain.name,
    lineCollection.body, GkrSourceBodies.lineInterpolationRealizationHelper.name⟩

set_option maxRecDepth 20000 in
structured_associations GkrSourceViews
  [empty := GkrSourceBodies.empty,
    append := GkrSourceBodies.append,
    helper2 := GkrSourceBodies.helper2,
    helper3 := GkrSourceBodies.helper3,
    helper4 := GkrSourceBodies.helper4,
    helper5 := GkrSourceBodies.helper5,
    helper6 := GkrSourceBodies.helper6,
    helper7 := GkrSourceBodies.helper7,
    helper8 := GkrSourceBodies.helper8,
    helper9 := GkrSourceBodies.helper9,
    helper10 := GkrSourceBodies.helper10,
    helper11 := GkrSourceBodies.helper11,
    helper12 := GkrSourceBodies.helper12,
    helper13 := GkrSourceBodies.helper13,
    helper14 := GkrSourceBodies.helper14,
    helper15 := GkrSourceBodies.helper15,
    helper16 := GkrSourceBodies.helper16,
    evaluate := GkrSourceBodies.evaluate,
    helper18 := GkrSourceBodies.helper18,
    selectBlock := GkrSourceBodies.selectBlock,
    helper42 := GkrSourceBodies.helper42,
    sourceHelper110 := GkrSourceBodies.sourceHelper110,
    sum := GkrSourceBodies.sum,
    evaluateWiring := GkrSourceBodies.evaluateWiring,
    helper73 := GkrSourceBodies.helper73,
    sourceHelper112 := GkrSourceBodies.sourceHelper112,
    helper75 := GkrSourceBodies.helper75,
    helper76 := GkrSourceBodies.helper76,
    helper74 := GkrSourceBodies.helper74,
    helper78 := GkrSourceBodies.helper78,
    helper43 := GkrSourceBodies.helper43,
    helper80 := GkrSourceBodies.helper80,
    evaluateCoefficients := GkrSourceBodies.evaluateCoefficients,
    linePoint := GkrSourceBodies.linePoint,
    interpolateRealization := GkrSourceBodies.interpolateRealization,
    interpolateCallback := GkrSourceBodies.interpolateCallback,
    lineInterpolationRealization := GkrSourceBodies.lineInterpolationRealization,
    lineCallback := GkrSourceBodies.lineCallback]

theorem first_bodies : MapFirstContracts.Bodies unit.definitions collectBindings := by
  bind_structured_bodies

theorem prefix_bodies : MapPrefixContracts.Bodies unit.definitions prefixBindings := by
  bind_structured_bodies

theorem bodies : Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.Bodies unit.definitions := by
  bind_structured_bodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The actual checked source table. -/
abbrev helpers : Meanings F G := closedMeanings unit.definitions

theorem prefix_laws : MapPrefixContracts.Laws (helpers (F := F) (G := G)) prefixBindings := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.prefix_laws unit.linked bodies

theorem empty_equation :
    invoke (helpers (F := F) (G := G)) SumcheckHelperBodies.emptyHelper .nil = .done (.cons [] .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.empty_equation unit.linked bodies

theorem append_equation (xs : List F) (x : F) :
    invoke (helpers (G := G)) SumcheckHelperBodies.appendHelper (.cons xs (.cons x .nil)) =
      .done (.cons (xs ++ [x]) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.append_equation unit.linked bodies xs x

theorem sum_body (table : Meanings F G) (xs : List F) :
    GkrSourceBodies.sumBody.denote (meaning F G table) (Values.cons xs .nil).get =
      .done (.cons (xs.foldl (· + ·) 0) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.sum_body table xs

theorem sum_equation (xs : List F) :
    invoke (helpers (G := G)) GkrSourceBodies.sumHelper (.cons xs .nil) = .done (.cons xs.sum .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.sum_equation unit.linked bodies xs

theorem evaluate_expansion (table : Meanings F G) (xs point : List F)
    (pointBound : point.length < indexLimit) :
    GkrSourceBodies.evaluateBody.denote (meaning F G table) (Values.cons xs (.cons point .nil)).get =
      (invoke table tableHelper (inputs xs point.length 1)).bind fun constructed =>
      (invoke table prefixHelper (constructed.append (.cons point .nil))).bind fun residual =>
      (invoke table (MultilinearPrefixBodies.valuesRealizationHelper prefixBindings.values) residual).bind fun values =>
      .done (.cons (values.get .here).sum .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.evaluate_expansion table xs point pointBound

theorem evaluate_generic_body (table : Meanings F G) (laws : MapPrefixContracts.Laws table prefixBindings)
    (xs point : List F) (vectorBound : xs.length < indexLimit) (pointBound : point.length < indexLimit) :
    GkrSourceBodies.evaluateBody.denote (meaning F G table) (Values.cons xs (.cons point .nil)).get =
      if HasShape xs point.length 1 then .done (.cons (restrictPrefixValues xs point).sum .nil)
      else .halt .reject := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.evaluate_generic_body table laws xs point vectorBound pointBound

theorem evaluate_equation (xs point : List F) (vectorBound : xs.length < indexLimit)
    (pointBound : point.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.evaluateHelper (.cons xs (.cons point .nil)) =
      if HasShape xs point.length 1 then .done (.cons (restrictPrefixValues xs point).sum .nil)
      else .halt .reject := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.evaluate_equation unit.linked bodies xs point vectorBound pointBound

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem prefix_sum_extension (n : Nat) (xs point : List F) (table : Table F n)
    (decoded : ofList? n xs = some table) (length : point.length = n) :
    (restrictPrefixValues xs point).sum = extension n table (coordinates n point) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.prefix_sum_extension n xs point table decoded length

theorem evaluate_extension (n : Nat) (xs point : List F) (table : Table F n)
    (decoded : ofList? n xs = some table) (length : point.length = n) (small : n < 64)
    (vectorBound : xs.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.evaluateHelper (.cons xs (.cons point .nil)) =
      .done (.cons (extension n table (coordinates n point)) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.evaluate_extension unit.linked bodies n xs point table decoded length small vectorBound

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
      (invoke table (MultilinearPrefixBodies.valuesRealizationHelper prefixBindings.values) third).bind fun values =>
      .done (.cons (values.get .here).sum .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.evaluateWiring_expansion table xs gate left right gateBound leftBound rightBound pairBound sumBound

theorem evaluateWiring_equation (xs gate left right : List F)
    (vectorBound : xs.length < indexLimit) (small : gate.length + left.length + right.length < 64)
    (shape : xs.length = 2 ^ (gate.length + left.length + right.length)) :
    invoke (helpers (G := G)) GkrSourceBodies.evaluateWiringHelper
        (.cons xs (.cons gate (.cons left (.cons right .nil)))) =
      .done (.cons (restrictPrefixValues xs (gate ++ left ++ right)).sum .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.evaluateWiring_equation unit.linked bodies xs gate left right vectorBound small shape

theorem evaluateWiring_extension (w : Nat) (xs gate left right : List F)
    (table : Table F (w + w + w)) (decoded : ofList? (w + w + w) xs = some table)
    (gateLength : gate.length = w) (leftLength : left.length = w) (rightLength : right.length = w)
    (small : w + w + w < 64) (vectorBound : xs.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.evaluateWiringHelper
        (.cons xs (.cons gate (.cons left (.cons right .nil)))) =
      .done (.cons (extension (w + w + w) table
        (coordinates (w + w + w) (gate ++ left ++ right))) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.evaluateWiring_extension unit.linked bodies w xs gate left right table decoded gateLength leftLength rightLength small vectorBound

theorem helper42_body_eq : GkrSourceBodies.helper42Body = MapFirstBodies.interpolateBody := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.interpolate_body_eq

theorem interpolate_equation (low high r : F) :
    invoke (helpers (G := G)) GkrSourceBodies.helper42Helper (.cons low (.cons high (.cons r .nil))) =
      .done (.cons (low + (high - low) * r) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.interpolate_equation unit.linked bodies low high r

theorem line_realization_body (table : Meanings F G) (low high r : F) :
    GkrSourceBodies.lineInterpolationRealizationBody.denote (meaning F G table)
      (Values.cons low (.cons high (.cons r .nil))).get =
      (invoke table GkrSourceBodies.helper42Helper (.cons low (.cons high (.cons r .nil)))).bind
        fun result => .done (.cons (result.get .here) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.line_realization_body table low high r

theorem line_callback_equation (low high : List F) (lo hi r : F) :
    invoke (helpers (G := G)) (MultilinearCollectBodies.mapCallbackHelper lineBindings)
      (.cons lo (.cons hi (.cons low (.cons high (.cons r .nil))))) =
      .done (.cons (lo + (hi - lo) * r) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.line_callback_equation unit.linked bodies low high lo hi r

theorem map_equation (start finish : List F) (t : F) (sameLength : finish.length = start.length)
    (small : start.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.sourceHelper110Helper (.cons start (.cons finish (.cons t .nil))) =
      .done (.cons (linePoints start finish t) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.map_equation unit.linked bodies start finish t sameLength small

theorem linePoint_body (table : Meanings F G) (start finish : List F) (t : F) :
    GkrSourceBodies.linePointBody.denote (meaning F G table)
        (Values.cons start (.cons finish (.cons t .nil))).get =
      (invoke table GkrSourceBodies.sourceHelper110Helper (.cons start (.cons finish (.cons t .nil)))).bind
        fun result => .done (.cons (result.get .here) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.linePoint_body table start finish t

theorem linePoint_equation (start finish : List F) (t : F) (sameLength : finish.length = start.length)
    (small : start.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.linePointHelper (.cons start (.cons finish (.cons t .nil))) =
      .done (.cons (linePoints start finish t) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.linePoint_equation unit.linked bodies start finish t sameLength small

abbrev powerFold : FoldSpec :=
  (fold? GkrSourceBodies.helper43Body).get (by decide +kernel)

theorem helper73_body (table : Meanings F G) (accumulated power coefficient point : F) :
    GkrSourceBodies.helper73Body.denote (meaning F G table)
        (Values.cons accumulated (.cons power (.cons coefficient (.cons point .nil)))).get =
      .done (.cons (accumulated + coefficient * power) (.cons (power * point) .nil)) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.powerStep_body table accumulated power coefficient point

theorem coefficientStepRealization_body (table : Meanings F G) (accumulated power coefficient point : F) :
    GkrSourceBodies.sourceHelper112Body.denote (meaning F G table)
        (Values.cons accumulated (.cons power (.cons coefficient (.cons point .nil)))).get =
      (invoke table GkrSourceBodies.helper73Helper
        (.cons accumulated (.cons power (.cons coefficient (.cons point .nil))))).bind fun result =>
      .done (.cons (result.get .here) (.cons (result.get (.there .here)) .nil)) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.coefficientStepRealization_body table accumulated power coefficient point

theorem helper75_body (table : Meanings F G) (accumulated power coefficient point : F) :
    GkrSourceBodies.helper75Body.denote (meaning F G table)
        (Values.cons accumulated (.cons power (.cons coefficient (.cons point .nil)))).get =
      (invoke table GkrSourceBodies.sourceHelper112Helper
        (.cons accumulated (.cons power (.cons coefficient (.cons point .nil))))).bind fun result =>
      .done (.cons (result.get .here) (.cons (result.get (.there .here)) .nil)) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.powerStepWrapper_body table accumulated power coefficient point

theorem helper78_body (table : Meanings F G) (accumulated power coefficient : F)
    (coefficients : List F) (point : F) :
    GkrSourceBodies.helper78Body.denote (meaning F G table)
        (Values.cons accumulated (.cons power (.cons coefficient (.cons coefficients
          (.cons point .nil))))).get =
      (invoke table GkrSourceBodies.helper75Helper
        (.cons accumulated (.cons power (.cons coefficient (.cons point .nil))))).bind fun result =>
      .done (.cons (result.get .here) (.cons (result.get (.there .here)) .nil)) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.powerFoldCallback_body table accumulated power coefficient coefficients point

theorem helper76_body (table : Meanings F G) :
    GkrSourceBodies.helper76Body.denote (meaning F G table) (Values.nil).get =
      .done (.cons ((0 : Nat) : F) (.cons ((1 : Nat) : F) .nil)) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.powerInitialState_body table

theorem coefficientStartRealization_body (table : Meanings F G) :
    GkrSourceBodies.helper74Body.denote (meaning F G table) (Values.nil).get =
      (invoke table GkrSourceBodies.helper76Helper .nil).bind fun result =>
      .done (.cons (result.get .here) (.cons (result.get (.there .here)) .nil)) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.coefficientStartRealization_body table

theorem coefficientFold_body (table : Meanings F G) (coefficients : List F) (accumulated power point : F) :
    GkrSourceBodies.helper43Body.denote (meaning F G table)
        (Values.cons coefficients (.cons accumulated (.cons power (.cons point .nil)))).get =
      (Evaluation.denoteFold table powerFold
        (.cons coefficients (.cons accumulated (.cons power (.cons point .nil))))).bind fun result =>
      .done (.cons (result.get .here) (.cons (result.get (.there .here)) .nil)) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.coefficientFold_body table coefficients accumulated power point

theorem helper80_body (table : Meanings F G) (accumulated power point : F) (coefficients : List F) :
    GkrSourceBodies.helper80Body.denote (meaning F G table)
        (Values.cons accumulated (.cons power (.cons point (.cons coefficients .nil)))).get =
      (invoke table GkrSourceBodies.helper43Helper
        (.cons coefficients (.cons accumulated (.cons power (.cons point .nil))))).bind fun result =>
      .done (.cons (result.get .here) (.cons (result.get (.there .here)) .nil)) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.powerFoldWrapper_body table accumulated power point coefficients

theorem evaluateCoefficients_body (table : Meanings F G) (coefficients : List F) (point : F) :
    GkrSourceBodies.evaluateCoefficientsBody.denote (meaning F G table)
        (Values.cons coefficients (.cons point .nil)).get =
      (invoke table GkrSourceBodies.helper74Helper .nil).bind fun start =>
      (invoke table GkrSourceBodies.helper80Helper (.cons (start.get .here)
        (.cons (start.get (.there .here)) (.cons point (.cons coefficients .nil))))).bind fun result =>
      .done (.cons (result.get .here) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.evaluateCoefficients_body table coefficients point

theorem powerStep_equation (accumulated power coefficient point : F) :
    invoke (helpers (G := G)) GkrSourceBodies.helper75Helper
        (.cons accumulated (.cons power (.cons coefficient (.cons point .nil)))) =
      .done (.cons (accumulated + coefficient * power) (.cons (power * point) .nil)) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.powerStep_equation unit.linked bodies accumulated power coefficient point

theorem step_equation (accumulated power coefficient : F) (coefficients : List F) (point : F) :
    invoke (helpers (G := G)) GkrSourceBodies.helper78Helper
        (.cons accumulated (.cons power (.cons coefficient (.cons coefficients (.cons point .nil))))) =
      .done (.cons (accumulated + coefficient * power) (.cons (power * point) .nil)) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.step_equation unit.linked bodies accumulated power coefficient coefficients point

theorem powerStart_equation :
    invoke (helpers (F := F) (G := G)) GkrSourceBodies.helper74Helper .nil =
      .done (.cons 0 (.cons 1 .nil)) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.powerStart_equation unit.linked bodies

def powerTransition (point : F) (state : F × F) (coefficient : F) : F × F :=
  (state.1 + coefficient * state.2, state.2 * point)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem powerTransition_fold (point : F) (coefficients : List F) (accumulated power : F) :
    coefficients.foldl (powerTransition point) (accumulated, power) =
      (accumulated + power * powerSum coefficients point, power * point ^ coefficients.length) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.powerTransition_fold point coefficients accumulated power

def powerReference (point : F) (state : Values (assignment F G) powerFold.state) (coefficient : F) :
    Values (assignment F G) powerFold.state :=
  .cons (state.get .here + coefficient * state.get (.there .here))
    (.cons (state.get (.there .here) * point) .nil)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem powerReference_fold (point : F) (coefficients : List F) (accumulated power : F) :
    coefficients.foldl (powerReference (G := G) point) (.cons accumulated (.cons power .nil)) =
      .cons (coefficients.foldl (powerTransition point) (accumulated, power)).1
        (.cons (coefficients.foldl (powerTransition point) (accumulated, power)).2 .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.powerReference_fold point coefficients accumulated power

theorem fold_equation (coefficients : List F) (accumulated power point : F)
    (small : coefficients.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper43Helper
        (.cons coefficients (.cons accumulated (.cons power (.cons point .nil)))) =
      .done (.cons (coefficients.foldl (powerTransition point) (accumulated, power)).1
        (.cons (coefficients.foldl (powerTransition point) (accumulated, power)).2 .nil)) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.fold_equation unit.linked bodies coefficients accumulated power point small

theorem evaluateCoefficients_equation (coefficients : List F) (point : F)
    (small : coefficients.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.evaluateCoefficientsHelper
        (.cons coefficients (.cons point .nil)) =
      .done (.cons (powerSum coefficients point) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.evaluateCoefficients_equation unit.linked bodies coefficients point small

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem denoteLoop_states {I : PIR.Signature} (state captures : List Ty)
    (body : RegionFunction (assignment F G) I (.index :: (state ++ captures), state ++ captures))
    (count : Nat) (initial : Values (assignment F G) state)
    (captured : Values (assignment F G) captures) (states : Nat → Values (assignment F G) state)
    (start : states 0 = initial)
    (law : ∀ index, index < count →
      Evaluation.invokeCallback body (.cons index ((states index).append captured)) =
        .done ((states (index + 1)).append captured)) :
    Evaluation.denoteLoop state captures body 0 count initial captured = .done (states count) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.denoteLoop_states state captures body count initial captured states start law

theorem powerOfTwo_body (table : Meanings F G) (exponent : Nat) (small : exponent < 64) :
    GkrSourceBodies.helper18Body.denote (meaning F G table) (Values.cons exponent .nil).get =
      .done (.cons (2 ^ exponent) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.powerOfTwo_body table exponent small

theorem powerOfTwo_equation (exponent : Nat) (small : exponent < 64) :
    invoke (helpers (F := F) (G := G)) GkrSourceBodies.helper18Helper (.cons exponent .nil) =
      .done (.cons (2 ^ exponent) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.powerOfTwo_equation unit.linked bodies exponent small

def selectLoopBody : Region dialect [.index, .vector "bls12-381.fr", .index, .index]
    [.vector "bls12-381.fr", .index, .index] :=
  Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.selectLoopBody

theorem selectBlockBody_eq : GkrSourceBodies.selectBlockBody = (
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.loop [.vector "bls12-381.fr", .index] [.index]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there .here) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil))))) (.cons selectLoopBody .nil) <|
  .ret (.cons .here .nil)) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.selectBlockBody_eq

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
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.selectLoop_body table index current remaining position

theorem selectBlock_equation (xs : List F) (position bits size : Nat)
    (shape : xs.length = 2 ^ bits * size) (positive : 0 < size) (inside : position < 2 ^ bits)
    (vectorBound : xs.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.selectBlockHelper
        (.cons xs (.cons position (.cons bits .nil))) =
      .done (.cons (block xs position size) .nil) := by
  exact Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.selectBlock_equation unit.linked bodies xs position bits size shape positive inside vectorBound

/-! ## Helper calls of exported programs -/

theorem helperTable_eq : Zkc.Construction.helperTable program F G = helpers (F := F) (G := G) := rfl

end ZkcExamples.Structured.GkrSourceLaws
