module

public import Zkc.Protocols.Sumcheck.Source.HelperLaws
public import Zkc.Protocols.Multilinear.Source.MapFirstContracts
public import Zkc.Source.Structured.PlainHelpers

@[expose] public section

/-! Exact helper-body transport into a complete unit's plain participant tables.
The optional Math projections preserve absent, unused inputs. -/
namespace ZkcExamples.Structured.SumcheckVerifierHelpers
open Zkc.Source Zkc.Source.Structured
open SumcheckHelperBodies MapFirstBodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Only exact helper membership, complete signatures and full raw trees. -/
structure Bodies (definitions : List CheckedDefinition) : Prop where
  empty : BodyIn definitions emptyHelper emptyBody
  append : BodyIn definitions appendHelper appendBody
  width : BodyIn definitions widthHelper widthBody
  «variables» : BodyIn definitions variablesHelper variablesBody
  values : BodyIn definitions valuesHelper valuesBody

variable (U : UnitPayload) (bodies : Bodies U.definitions)
include bodies

theorem empty_plain :
    invoke (plainHelpers (F := F) (G := G) U).closed emptyHelper .nil =
      .done (.cons [] .nil) := by
  rw [closed_invoke_plain, bodies.empty.invoke U.linked, SumcheckHelperLaws.empty_body]
  rfl

/-- Append is total in this logical helper and consumes the actual supplied value. -/
theorem append_plain (point : List F) (value : F) :
    invoke (plainHelpers (F := F) (G := G) U).closed appendHelper
      (.cons point (.cons value .nil)) = .done (.cons (point ++ [value]) .nil) := by
  rw [closed_invoke_plain, bodies.append.invoke U.linked, SumcheckHelperLaws.append_body]
  rfl

theorem width_optional (xs : Option (List F)) (dimension width : Option Nat) :
    invoke (plainHelpers (F := F) (G := G) U).components widthHelper
      (.cons xs (.cons dimension (.cons width .nil))) = .done (.cons width .nil) := by
  rw [component_body_plain U widthHelper widthBody bodies.width]
  rfl

theorem variables_optional (xs : Option (List F)) (dimension width : Option Nat) :
    invoke (plainHelpers (F := F) (G := G) U).components variablesHelper
      (.cons xs (.cons dimension (.cons width .nil))) = .done (.cons dimension .nil) := by
  rw [component_body_plain U variablesHelper variablesBody bodies.variables]
  rfl

theorem values_optional (xs : Option (List F)) (dimension width : Option Nat) :
    invoke (plainHelpers (F := F) (G := G) U).components valuesHelper
      (.cons xs (.cons dimension (.cons width .nil))) = .done (.cons xs .nil) := by
  rw [component_body_plain U valuesHelper valuesBody bodies.values]
  rfl

end ZkcExamples.Structured.SumcheckVerifierHelpers
