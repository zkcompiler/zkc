module

public import Zkc.Protocols.Multilinear.Source.MapFirstLaws
public import Zkc.Protocols.Multilinear.Source.PrefixBodies
public import Zkc.Source.Structured.Linking

@[expose] public section

/-! Projection and realization equations shared by the retained First and Prefix
sources. Each premise identifies an exact body in the caller's own linked table. -/
namespace ZkcExamples.Structured.MapProjectionContracts
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws MapFirstBodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]
variable {definitions : List CheckedDefinition}
  (linked : DeclarationsLinked [] definitions)
include linked

theorem values_equation (body : BodyIn definitions valuesHelper valuesBody)
    (xs : List F) (dimension columns : Nat) :
    invoke (closedMeanings (F := F) (G := G) definitions) valuesHelper (inputs xs dimension columns) =
      .done (.cons xs .nil) :=
  (body.invoke linked (inputs xs dimension columns)).trans
    (MapSourceExpansions.first_values _ xs dimension columns)

theorem valuesRealization_equation {computation : String} (projection : BodyIn definitions valuesHelper valuesBody)
    (body : BodyIn definitions (MultilinearPrefixBodies.valuesRealizationHelper computation) valuesRealizationBody)
    (xs : List F) (dimension columns : Nat) :
    invoke (closedMeanings (F := F) (G := G) definitions) (MultilinearPrefixBodies.valuesRealizationHelper computation)
      (inputs xs dimension columns) = .done (.cons xs .nil) := by
  rw [body.invoke linked]
  dsimp only [inputs, vector]
  rw [MapSourceExpansions.first_valuesRealization]
  change (invoke (closedMeanings (F := F) (G := G) definitions) valuesHelper
    (inputs xs dimension columns)).bind _ = _
  rw [values_equation linked projection]
  rfl

theorem variables_equation (body : BodyIn definitions variablesHelper variablesBody)
    (xs : List F) (dimension columns : Nat) :
    invoke (closedMeanings (F := F) (G := G) definitions) variablesHelper (inputs xs dimension columns) =
      .done (.cons dimension .nil) :=
  (body.invoke linked (inputs xs dimension columns)).trans
    (MapSourceExpansions.first_variables _ xs dimension columns)

theorem variablesRealization_equation (projection : BodyIn definitions variablesHelper variablesBody)
    (body : BodyIn definitions variablesRealizationHelper variablesRealizationBody)
    (xs : List F) (dimension columns : Nat) :
    invoke (closedMeanings (F := F) (G := G) definitions) variablesRealizationHelper
      (inputs xs dimension columns) = .done (.cons dimension .nil) := by
  rw [body.invoke linked]
  dsimp only [inputs, vector]
  rw [MapSourceExpansions.first_variablesRealization]
  change (invoke (closedMeanings (F := F) (G := G) definitions) variablesHelper
    (inputs xs dimension columns)).bind _ = _
  rw [variables_equation linked projection]
  rfl

theorem width_equation (body : BodyIn definitions widthHelper widthBody)
    (xs : List F) (dimension columns : Nat) :
    invoke (closedMeanings (F := F) (G := G) definitions) widthHelper (inputs xs dimension columns) =
      .done (.cons columns .nil) :=
  (body.invoke linked (inputs xs dimension columns)).trans
    (MapSourceExpansions.first_width _ xs dimension columns)

theorem widthRealization_equation (projection : BodyIn definitions widthHelper widthBody)
    (body : BodyIn definitions widthRealizationHelper widthRealizationBody)
    (xs : List F) (dimension columns : Nat) :
    invoke (closedMeanings (F := F) (G := G) definitions) widthRealizationHelper
      (inputs xs dimension columns) = .done (.cons columns .nil) := by
  rw [body.invoke linked]
  dsimp only [inputs, vector]
  rw [MapSourceExpansions.first_widthRealization]
  change (invoke (closedMeanings (F := F) (G := G) definitions) widthHelper
    (inputs xs dimension columns)).bind _ = _
  rw [width_equation linked projection]
  rfl

end ZkcExamples.Structured.MapProjectionContracts
