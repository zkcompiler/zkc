module

public import ZkcExamples.Structured.SumcheckReduceAssociations
public import ZkcExamples.Structured.SumcheckHelperBridge

@[expose] public section
namespace ZkcExamples.Structured.SumcheckReduceContracts
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws MapPrefixBodies
open SumcheckHelperBodies SumcheckHelperLaws SumcheckReduceAssociations
open SumcheckReduceViews (unit)
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
  (unit.component_body_view_as SumcheckReduceViews.widthDefinition width_member
    MapFirstBodies.widthHelper width_signature MapFirstBodies.widthBody width_shared_raw
      (.cons xs (.cons dimension (.cons columns .nil)))).trans (by rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The projection preserves its selected optional component without demanding other operands. -/
theorem variables_components (xs : Option (List F)) (dimension : Option Nat) (columns : Option Nat) :
    invoke (unit.tables F G).components MapFirstBodies.variablesHelper
      (.cons xs (.cons dimension (.cons columns .nil))) = .done (.cons dimension .nil) :=
  (unit.component_body_view_as SumcheckReduceViews.variablesDefinition variables_member
    MapFirstBodies.variablesHelper variables_signature MapFirstBodies.variablesBody variables_shared_raw
      (.cons xs (.cons dimension (.cons columns .nil)))).trans (by rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The projection preserves its selected optional component without demanding other operands. -/
theorem values_components (xs : Option (List F)) (dimension : Option Nat) (columns : Option Nat) :
    invoke (unit.tables F G).components MapFirstBodies.valuesHelper
      (.cons xs (.cons dimension (.cons columns .nil))) = .done (.cons xs .nil) :=
  (unit.component_body_view_as SumcheckReduceViews.valuesDefinition values_member
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

end ZkcExamples.Structured.SumcheckReduceContracts
