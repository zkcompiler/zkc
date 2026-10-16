module

public import ZkcExamples.Structured.SumcheckHelperLaws
public import ZkcExamples.Structured.MapFirstContracts
public import Zkc.Source.Structured.OpenLaws

@[expose] public section

/-! Exact helper-body transport into a complete unit's plain participant tables.
The optional Math projections preserve absent, unused inputs. -/
namespace ZkcExamples.Structured.SumcheckVerifierHelpers
open Zkc.Source Zkc.Source.Structured
open SumcheckHelperBodies MapFirstBodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The actual silent fold used by the complete unit's participant semantics. -/
abbrev plainHelpers (U : UnitPayload) :
    Evaluation.ComponentTables F G (participantInterface F G) :=
  U.definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩

/-- Only exact helper membership, complete signatures and full raw trees. -/
structure Bodies (definitions : List CheckedDefinition) : Prop where
  empty : BodyIn definitions emptyHelper emptyBody
  append : BodyIn definitions appendHelper appendBody
  width : BodyIn definitions widthHelper widthBody
  «variables» : BodyIn definitions variablesHelper variablesBody
  values : BodyIn definitions valuesHelper valuesBody

/-- Closed interpretation retains each helper's actual captured definition prefix. -/
theorem closed_invoke_plain (U : UnitPayload) (helper : Helper)
    (arguments : Values (assignment F G) helper.inputs) :
    invoke (plainHelpers (F := F) (G := G) U).closed helper arguments =
      (invoke (closedMeanings (F := F) (G := G) U.definitions) helper arguments).interpret
        (closedLift (I := participantInterface F G)) := by
  simpa only [plainHelpers, Evaluation.ComponentTables.closed_fold] using
    (Evaluation.foldMeanings_closedLift (F := F) (G := G)
      (I := participantInterface F G) U.definitions helper arguments).symm

/-- Full-body association transports optional component evaluation as well. -/
theorem component_body_plain (U : UnitPayload) (helper : Helper)
    (body : Region dialect helper.inputs helper.outputs)
    (association : BodyIn U.definitions helper body)
    (arguments : Values (Component (assignment F G)) helper.inputs) :
    invoke (plainHelpers (F := F) (G := G) U).components helper arguments =
      body.component (Evaluation.meaning (.silent _) (plainHelpers U).closed)
        (Evaluation.componentOperation (.silent _) (plainHelpers U)) arguments.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := association
  calc
    _ = (invoke (U.tables F G).components helper arguments).interpret forgetSites :=
      ((Evaluation.ComponentTables.fold_forgetSites U.definitions).components helper arguments).symm
    _ = _ := by
      rw [U.component_body_view_as definition member helper signature body exactRaw arguments]
      exact Evaluation.component_interpret forgetSites observedSites_forgetSites
        (Evaluation.ComponentTables.fold_forgetSites U.definitions) body arguments.get

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
