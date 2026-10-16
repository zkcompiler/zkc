module

public import ZkcExamples.Structured.SumcheckSourceAssociations
public import ZkcExamples.Structured.SumcheckHelperBridge

@[expose] public section
namespace ZkcExamples.Structured.SumcheckSourceContracts
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws MapPrefixBodies
open SumcheckHelperBodies SumcheckHelperLaws SumcheckSourceAssociations
open SumcheckSourceViews (unit)
open Zkc.Polynomial Zkc.Polynomial.Multilinear

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The closed-site fold of this complete original unit's own helper list. -/
abbrev helperMeanings : Meanings F G := closedMeanings unit.definitions

theorem first_laws : MapFirstContracts.Laws (helperMeanings (F := F) (G := G)) :=
  MapFirstContracts.laws_of_bodies unit.linked first_bodies

theorem halves_body : HalvesBodyLaw (helperMeanings (F := F) (G := G)) :=
  fun xs dimension columns => halves_association.invoke unit.linked (inputs xs dimension columns)

theorem shape_body : ShapeBodyLaw (helperMeanings (F := F) (G := G)) :=
  fun xs dimension columns => shape_association.invoke unit.linked (inputs xs dimension columns)

/-- Full raw-input contract, with no width or vector-length admission invented. -/
theorem sums_all (xs : List F) (dimension columns : Nat) :
    invoke (helperMeanings (G := G)) sumsHelper (inputs xs dimension columns) =
      if dimension < indexLimit then
        if 0 < dimension then
          if 0 < xs.length ∧ xs.length % 2 = 0 then
            .done (messageResult (xs.take (xs.length / 2)).sum (xs.drop (xs.length / 2)).sum)
          else .halt .refused
        else .halt .reject
      else .halt .refused :=
  (sums_association.invoke unit.linked (inputs xs dimension columns)).trans
    (sums_generic_body_all _ first_laws.less halves_body xs dimension columns)

theorem sums_honestMessage {n : Nat} (xs : List F) (table : Table F (n + 1))
    (columns : Nat) (decoded : ofList? (n + 1) xs = some table)
    (dimensionBound : n + 1 < indexLimit) :
    invoke (helperMeanings (G := G)) sumsHelper (inputs xs (n + 1) columns) =
      .done (messageResult (Zkc.Protocols.Sumcheck.Multilinear.honestMessage table).1
        (Zkc.Protocols.Sumcheck.Multilinear.honestMessage table).2) :=
  (sums_association.invoke unit.linked (inputs xs (n + 1) columns)).trans
    (sums_honestMessage_generic_body _ first_laws.halves xs table columns decoded dimensionBound)

theorem empty_equation :
    invoke (helperMeanings (F := F) (G := G)) emptyHelper .nil = .done (.cons [] .nil) :=
  (empty_association.invoke unit.linked .nil).trans (empty_body _)

theorem append_equation (xs : List F) (x : F) :
    invoke (helperMeanings (G := G)) appendHelper (.cons xs (.cons x .nil)) =
      .done (.cons (xs ++ [x]) .nil) :=
  (append_association.invoke unit.linked (.cons xs (.cons x .nil))).trans (append_body _ xs x)

theorem values_equation (xs : List F) (dimension columns : Nat) :
    invoke (helperMeanings (G := G)) valuesHelper (inputs xs dimension columns) = .done (.cons xs .nil) :=
  (values_association.invoke unit.linked (inputs xs dimension columns)).trans
    (MapSourceExpansions.first_values _ xs dimension columns)

/-- Projection of actual observed lookup; arbitrary mark handlers are not erased. -/
theorem helper_plain (helper : Helper) (args : Values (assignment F G) helper.inputs) :
    (invoke (unit.tables F G).closed helper args).interpret forgetSites =
      (invoke (helperMeanings (G := G)) helper args).interpret
        (closedLift (I := participantInterface F G)) :=
  unit.closed_invoke_forgetSites helper args

theorem prefix_laws : MapPrefixContracts.Laws (helperMeanings (F := F) (G := G)) :=
  MapPrefixContracts.laws_of_bodies unit.linked prefix_bodies first_bodies

theorem prefix_equation (xs : List F) (dimension columns : Nat) (point : List F)
    (shape : HasShape xs dimension columns) (vectorBound : xs.length < indexLimit) :
    invoke (helperMeanings (G := G)) prefixHelper (MapPrefixLaws.prefixInputs xs dimension columns point) =
      if point.length < indexLimit then
        if point.length ≤ dimension then
          .done (inputs (restrictPrefixValues xs point) (dimension - point.length) columns)
        else .halt .reject
      else .halt .exhausted :=
  MapPrefixContracts.prefix_equation unit.linked prefix_bodies first_laws.first
    xs dimension columns point shape vectorBound

/-- The callback is an actual member of the same original table, not an appended fixture. -/
theorem checkTable_body (xs point : List F) (claim : F) :
    invoke (helperMeanings (G := G)) checkTableHelper (checkInputs xs point claim) =
      checkTableBody.denote (meaning F G (helperMeanings (G := G))) (checkInputs xs point claim).get :=
  checkTable_association.invoke unit.linked (checkInputs xs point claim)

theorem checkTable_equation (xs point : List F) (claim : F)
    (vectorBound : xs.length < indexLimit) (pointBound : point.length < indexLimit) :
    invoke (helperMeanings (G := G)) checkTableHelper (checkInputs xs point claim) =
      if HasShape xs point.length 1 then
        .done (boolResult (decide ((restrictPrefixValues xs point).sum = claim)))
      else .halt .reject :=
  (checkTable_body xs point claim).trans
    (checkTable_generic_body _ prefix_laws xs point claim vectorBound pointBound)

theorem check_equation (xs point : List F) (claim : F)
    (vectorBound : xs.length < indexLimit) (pointBound : point.length < indexLimit) :
    invoke (helperMeanings (G := G)) checkHelper (checkInputs xs point claim) =
      .done (boolResult (decide (HasShape xs point.length 1 ∧
        (restrictPrefixValues xs point).sum = claim))) :=
  (check_association.invoke unit.linked (checkInputs xs point claim)).trans
    (check_generic_body _ prefix_laws checkTable_body xs point claim vectorBound pointBound)

/-- The existing mathematical checker, including malformed vectors, for the actual public helper. -/
theorem check_mathematical (xs point : List F) (claim : F)
    (vectorBound : xs.length < indexLimit) (pointBound : point.length < indexLimit) :
    invoke (helperMeanings (G := G)) checkHelper (checkInputs xs point claim) =
      .done (boolResult (Zkc.Protocols.Sumcheck.Multilinear.check
        (n := 0 + point.length) xs
        (Quadratic.point point.length (coordinates point.length point) Fin.elim0) claim)) :=
  (check_association.invoke unit.linked (checkInputs xs point claim)).trans
    (SumcheckHelperLaws.check_mathematical _ prefix_laws checkTable_body
      xs point claim vectorBound pointBound)

theorem check_mle (xs point : List F) (claim : F) (table : Table F (0 + point.length))
    (decoded : ofList? (0 + point.length) xs = some table) (vectorBound : xs.length < indexLimit) :
    invoke (helperMeanings (G := G)) checkHelper (checkInputs xs point claim) =
      .done (boolResult (decide (extension (0 + point.length) table
        (coordinates (0 + point.length) point) = claim))) :=
  (check_association.invoke unit.linked (checkInputs xs point claim)).trans
    (check_mle_generic_body _ prefix_laws checkTable_body xs point claim table decoded vectorBound)

theorem check_large_dimension (xs point : List F) (claim : F)
    (pointBound : point.length < indexLimit) (large : ¬ point.length < 64) :
    invoke (helperMeanings (G := G)) checkHelper (checkInputs xs point claim) = .done (boolResult false) :=
  (check_association.invoke unit.linked (checkInputs xs point claim)).trans
    (check_large_dimension_generic_body _ (lessAll_bounded _ first_laws.less) shape_body
      xs point claim pointBound large)

theorem check_vector_exhausted (xs point : List F) (claim : F)
    (small : point.length < 64) (overflow : ¬ xs.length < indexLimit) :
    invoke (helperMeanings (G := G)) checkHelper (checkInputs xs point claim) = .halt .exhausted :=
  (check_association.invoke unit.linked (checkInputs xs point claim)).trans
    (check_vector_exhausted_generic_body _ (lessAll_bounded _ first_laws.less) shape_body
      xs point claim small overflow)

theorem check_point_exhausted (xs point : List F) (claim : F)
    (overflow : ¬ point.length < indexLimit) :
    invoke (helperMeanings (G := G)) checkHelper (checkInputs xs point claim) = .halt .exhausted :=
  (check_association.invoke unit.linked (checkInputs xs point claim)).trans
    (SumcheckHelperLaws.check_point_exhausted _ xs point claim overflow).1

/-- Total actual lookup, preserving the source's ordered admission and short-circuit cases. -/
theorem check_all (xs point : List F) (claim : F) :
    invoke (helperMeanings (G := G)) checkHelper (checkInputs xs point claim) =
      if point.length < indexLimit then
        if point.length < 64 then
          if xs.length < indexLimit then
            .done (boolResult (Zkc.Protocols.Sumcheck.Multilinear.check
              (n := 0 + point.length) xs
              (Quadratic.point point.length (coordinates point.length point) Fin.elim0) claim))
          else .halt .exhausted
        else .done (boolResult false)
      else .halt .exhausted := by
  by_cases pointBound : point.length < indexLimit
  · rw [ite_eq_left pointBound]
    by_cases small : point.length < 64
    · rw [ite_eq_left small]
      by_cases vectorBound : xs.length < indexLimit
      · rw [ite_eq_left vectorBound]
        exact check_mathematical xs point claim vectorBound pointBound
      · rw [ite_eq_right vectorBound]
        exact check_vector_exhausted xs point claim small vectorBound
    · rw [ite_eq_right small]
      exact check_large_dimension xs point claim pointBound small
  · rw [ite_eq_right pointBound]
    exact check_point_exhausted xs point claim pointBound

set_option backward.isDefEq.respectTransparency false in
/-- Actual helper lookup after forgetting sites returns the proved mathematical Boolean. -/
theorem check_plain (xs point : List F) (claim : F)
    (vectorBound : xs.length < indexLimit) (pointBound : point.length < indexLimit) :
    (invoke (unit.tables F G).closed checkHelper (checkInputs xs point claim)).interpret forgetSites =
      .done (boolResult (Zkc.Protocols.Sumcheck.Multilinear.check
        (n := 0 + point.length) xs
        (Quadratic.point point.length (coordinates point.length point) Fin.elim0) claim)) := by
  rw [helper_plain, check_mathematical xs point claim vectorBound pointBound]
  rfl

theorem width_equation (xs : List F) (dimension columns : Nat) :
    invoke (helperMeanings (G := G)) MapFirstBodies.widthHelper (inputs xs dimension columns) =
      .done (.cons columns .nil) :=
  (width_association.invoke unit.linked (inputs xs dimension columns)).trans
    (MapSourceExpansions.first_width _ xs dimension columns)

theorem variables_equation (xs : List F) (dimension columns : Nat) :
    invoke (helperMeanings (G := G)) MapFirstBodies.variablesHelper (inputs xs dimension columns) =
      .done (.cons dimension .nil) :=
  (variables_association.invoke unit.linked (inputs xs dimension columns)).trans
    (MapSourceExpansions.first_variables _ xs dimension columns)

set_option backward.isDefEq.respectTransparency false in
/-- The projection preserves its selected optional component without demanding other operands. -/
theorem width_components (xs : Option (List F)) (dimension : Option Nat) (columns : Option Nat) :
    invoke (unit.tables F G).components MapFirstBodies.widthHelper
      (.cons xs (.cons dimension (.cons columns .nil))) = .done (.cons columns .nil) :=
  (unit.component_body_view_as SumcheckSourceViews.widthDefinition width_member
    MapFirstBodies.widthHelper width_signature MapFirstBodies.widthBody width_shared_raw
      (.cons xs (.cons dimension (.cons columns .nil)))).trans (by rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The projection preserves its selected optional component without demanding other operands. -/
theorem variables_components (xs : Option (List F)) (dimension : Option Nat) (columns : Option Nat) :
    invoke (unit.tables F G).components MapFirstBodies.variablesHelper
      (.cons xs (.cons dimension (.cons columns .nil))) = .done (.cons dimension .nil) :=
  (unit.component_body_view_as SumcheckSourceViews.variablesDefinition variables_member
    MapFirstBodies.variablesHelper variables_signature MapFirstBodies.variablesBody variables_shared_raw
      (.cons xs (.cons dimension (.cons columns .nil)))).trans (by rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The projection preserves its selected optional component without demanding other operands. -/
theorem values_components (xs : Option (List F)) (dimension : Option Nat) (columns : Option Nat) :
    invoke (unit.tables F G).components MapFirstBodies.valuesHelper
      (.cons xs (.cons dimension (.cons columns .nil))) = .done (.cons xs .nil) :=
  (unit.component_body_view_as SumcheckSourceViews.valuesDefinition values_member
    MapFirstBodies.valuesHelper values_signature MapFirstBodies.valuesBody values_shared_raw
      (.cons xs (.cons dimension (.cons columns .nil)))).trans (by rfl)

set_option backward.isDefEq.respectTransparency false in
theorem empty_plain :
    (invoke (unit.tables F G).closed emptyHelper .nil).interpret forgetSites = .done (.cons [] .nil) := by
  rw [helper_plain, empty_equation]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem append_plain (xs : List F) (x : F) :
    (invoke (unit.tables F G).closed appendHelper (.cons xs (.cons x .nil))).interpret forgetSites =
      .done (.cons (xs ++ [x]) .nil) := by
  rw [helper_plain, append_equation]
  rfl

end ZkcExamples.Structured.SumcheckSourceContracts
