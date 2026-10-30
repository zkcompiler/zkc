module

public import ZkcExamples.Structured.SumcheckSourceAssociations
public import Zkc.Protocols.Sumcheck.Source.HelperBridge
public import Zkc.Protocols.Sumcheck.Source.UnitContracts

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

theorem bodies : SumcheckUnitContracts.Bodies unit.definitions :=
  ⟨⟨_, first_bodies⟩, sums_association, empty_association, append_association, values_association,
    width_association, variables_association⟩

theorem first_laws : MapFirstContracts.Laws (helperMeanings (F := F) (G := G)) :=
  SumcheckUnitContracts.first_laws unit.linked bodies

theorem shape_body : ShapeBodyLaw (helperMeanings (F := F) (G := G)) :=
  SumcheckUnitContracts.shape_body unit.linked bodies

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
  SumcheckUnitContracts.sums_all unit.linked bodies xs dimension columns

/-- Projection of actual observed lookup; arbitrary mark handlers are not erased. -/
theorem helper_plain (helper : Helper) (args : Values (assignment F G) helper.inputs) :
    (invoke (unit.tables F G).closed helper args).interpret forgetSites =
      (invoke (helperMeanings (G := G)) helper args).interpret
        (closedLift (I := participantInterface F G)) :=
  unit.closed_invoke_forgetSites helper args

theorem prefix_laws : MapPrefixContracts.Laws (helperMeanings (F := F) (G := G))
    SumcheckMathBindings.prefixBindings :=
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
      SumcheckSourceBodies.checkTableBody.denote (meaning F G (helperMeanings (G := G))) (checkInputs xs point claim).get :=
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
    (SumcheckHelperLaws.check_point_exhausted (bindings := SumcheckMathBindings.prefixBindings)
      _ xs point claim overflow).1

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

/-- Actual helper lookup after forgetting sites returns the proved mathematical Boolean. -/
theorem check_plain (xs point : List F) (claim : F)
    (vectorBound : xs.length < indexLimit) (pointBound : point.length < indexLimit) :
    (invoke (unit.tables F G).closed checkHelper (checkInputs xs point claim)).interpret forgetSites =
      .done (boolResult (Zkc.Protocols.Sumcheck.Multilinear.check
        (n := 0 + point.length) xs
        (Quadratic.point point.length (coordinates point.length point) Fin.elim0) claim)) := by
  rw [helper_plain, check_mathematical xs point claim vectorBound pointBound]
  rfl

/-- The projection preserves its selected optional component without demanding other operands. -/
theorem width_components (xs : Option (List F)) (dimension : Option Nat) (columns : Option Nat) :
    invoke (unit.tables F G).components MapFirstBodies.widthHelper
      (.cons xs (.cons dimension (.cons columns .nil))) = .done (.cons columns .nil) :=
  SumcheckUnitContracts.width_components bodies xs dimension columns

end ZkcExamples.Structured.SumcheckSourceContracts
