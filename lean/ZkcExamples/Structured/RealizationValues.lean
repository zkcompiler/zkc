module

public import ZkcExamples.Structured.RealizationValuesViews
public import ZkcExamples.Structured.PrimitiveLibrary
public import Zkc.Source.Structured.RealizationTotality

@[expose] public section

/-! Complete-table equations for the actual retained table/realization caller.
Pure projection has no shape or representation premises. The owning source
wrapper validates the table first and preserves every failure of that constructor.
Math projection and strict owned invocation retain different absence behavior. -/
namespace ZkcExamples.Structured.RealizationValues
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary RealizationValuesViews

set_option smartUnfolding false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Full-table lookup of the actual Math helper projects the original vector. -/
theorem projection_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) projectionHelper (inputs xs dimension columns) =
      .done (.cons xs .nil) := by
  refine (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload projectionDefinition projection_member
    projectionBody projection_exact (inputs xs dimension columns)).trans ?_
  rfl

/-- The retained realization invokes the exact full Math ABI in the same table. -/
theorem realization_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) realizationHelper (inputs xs dimension columns) =
      .done (.cons xs .nil) := by
  refine (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload realizationDefinition realization_member
    realizationBody realization_exact (inputs xs dimension columns)).trans ?_
  change (invoke (program.payload.meanings F G) projectionHelper
    (inputs xs dimension columns)).bind _ = _
  rw [projection_equation]
  rfl

/-- The unchanged Local values wrapper adds no validation after realization. -/
theorem values_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) valuesHelper (inputs xs dimension columns) =
      .done (.cons xs .nil) := by
  refine (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload valuesDefinition values_member
    valuesBody values_exact (inputs xs dimension columns)).trans ?_
  change (invoke (program.payload.meanings F G) realizationHelper
    (inputs xs dimension columns)).bind _ = _
  rw [realization_equation]
  rfl

/-- Totality of the pure realization includes empty vectors and arbitrary indices. -/
theorem realization_returns (xs : List F) (dimension columns : Nat) :
    Returns (invoke (program.payload.meanings F G) realizationHelper
      (inputs xs dimension columns)) :=
  ⟨_, realization_equation xs dimension columns⟩

private theorem less_law : LessLaw (program.payload.meanings F G) := by
  intro a b aBound bBound
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload lessDefinition less_member
    PrimitiveTableViews.lessBody less_exact (.cons a (.cons b .nil))).trans
      (less_body _ a b aBound bBound)

private theorem rows_law : RowsLaw (program.payload.meanings F G) := by
  intro dimension bound
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload rowsDefinition rows_member
    PrimitiveTableViews.rowsBody rows_exact (indexResult dimension)).trans
      (rows_body _ less_law dimension bound)

private theorem shape_equation (xs : List F) (dimension columns : Nat)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    invoke (program.payload.meanings F G) PrimitiveTableViews.shapeHelper
      (inputs xs dimension columns) =
      .done (boolResult (decide (HasShape xs dimension columns))) :=
  (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload shapeDefinition shape_member
    PrimitiveTableViews.shapeBody shape_exact (inputs xs dimension columns)).trans
      (shape_body _ less_law rows_law xs dimension columns lengthBound dimensionBound columnsBound)

/-- Validation is supplied by this payload, including its complete helper closure. -/
theorem table_equation (xs : List F) (dimension columns : Nat)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    invoke (program.payload.meanings F G) PrimitiveTableViews.tableHelper
      (inputs xs dimension columns) =
      if HasShape xs dimension columns then .done (inputs xs dimension columns)
      else .halt .reject := by
  have actual := Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload tableDefinition table_member
    PrimitiveTableViews.tableBody table_exact (inputs xs dimension columns)
  have equation := table_body (program.payload.meanings F G) xs dimension columns
    (decide (HasShape xs dimension columns))
    (shape_equation (G := G) xs dimension columns lengthBound dimensionBound columnsBound)
  simp only [decide_eq_true_eq] at equation
  exact actual.trans equation

set_option maxHeartbeats 400000 in
/-- Exact source composition, before imposing any representation or shape premise. -/
theorem process_expansion (xs : List F) (dimension columns : Nat) :
    program.denote F G (inputs xs dimension columns) =
      (invoke (program.payload.meanings F G) PrimitiveTableViews.tableHelper
        (inputs xs dimension columns)).bind (fun table =>
        invoke (program.payload.meanings F G) valuesHelper table) := by
  refine (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    program.payload entryBody entry_exact (inputs xs dimension columns)).trans ?_
  change (invoke (program.payload.meanings F G) PrimitiveTableViews.tableHelper
    (inputs xs dimension columns)).bind _ = _
  apply congrArg
  funext table
  cases table with
  | cons entries rest => cases rest with
    | cons dimension rest => cases rest with
      | cons columns rest =>
        cases rest
        change (invoke (program.payload.meanings F G) valuesHelper
          (inputs entries dimension columns)).bind _ = _
        rw [values_equation]
        rfl

/-- The actual source validates table shape before returning its entries. -/
theorem process_equation (xs : List F) (dimension columns : Nat)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    program.denote F G (inputs xs dimension columns) =
      if HasShape xs dimension columns then .done (.cons xs .nil) else .halt .reject := by
  rw [process_expansion, table_equation xs dimension columns lengthBound dimensionBound columnsBound]
  split
  · exact values_equation xs dimension columns
  · rfl

/-- Every constructor stop is preserved before the realization is reached. -/
theorem process_stops_of_table (xs : List F) (dimension columns : Nat) (reason : PIR.Stop)
    (stops : invoke (program.payload.meanings F G) PrimitiveTableViews.tableHelper
      (inputs xs dimension columns) = .halt reason) :
    program.denote F G (inputs xs dimension columns) = .halt reason := by
  rw [process_expansion, stops]
  rfl

/-- Per-result Math dependencies ignore both unused optional dimensions. -/
theorem projection_optional (xs : Option (List F)) (dimension columns : Option Nat) :
    invoke (program.payload.componentTables F G).components projectionHelper
      (.cons xs (.cons dimension (.cons columns .nil))) = .done (.cons xs .nil) := by
  refine (Evaluation.payload_component_body_view (F := F) (G := G) SiteObservations.closed
    program.payload projectionDefinition projection_member
    projectionBody projection_exact (.cons xs (.cons dimension (.cons columns .nil)))).trans ?_
  rfl

/-- An optional Local operation sequences the entire retained input tuple. -/
theorem realization_optional_missing
    (args : Values (Component (assignment F G)) tableTypes)
    (missing : RoleFamily.sequence args = none) :
    Evaluation.componentOperation SiteObservations.closed
      (program.payload.componentTables F G) (.invoke realizationHelper) args .nil =
        .done (.cons none .nil) := by
  rw [Evaluation.componentOperation_local SiteObservations.closed _ _ rfl]
  change (match RoleFamily.sequence
      (Value := assignment F G) args with
    | none => .done (.cons none .nil)
    | some values => (invoke (program.payload.componentTables F G).closed
        realizationHelper values).bind (fun result => .done result.present)) =
      (PIR.Process.done (.cons none .nil) :
        Closed (Values (Component (assignment F G)) valueTypes))
  rw [missing]

/-- At the owning boundary, any absent input stops before work, even if unused. -/
theorem realization_owned_missing (self : Nat)
    (args : Values (Component (assignment F G)) tableTypes)
    (missing : RoleFamily.sequence args = none) :
    Participant.owned self self
      (invoke (program.payload.meanings F G) realizationHelper) args = .halt .incomplete := by
  simp only [Participant.owned, ↓reduceIte, missing]

/-- Both unused index operands are required by the owner of this actual source helper. -/
theorem values_owned_missing (self : Nat) (xs : Option (List F))
    (dimension columns : Option Nat) (missing : dimension = none ∨ columns = none) :
    Participant.owned self self (invoke (program.payload.meanings F G) valuesHelper)
      (.cons xs (.cons dimension (.cons columns .nil))) = .halt .incomplete := by
  have absent : RoleFamily.sequence (Value := assignment F G)
      (.cons xs (.cons dimension (.cons columns .nil)) :
        Values (Component (assignment F G)) tableTypes) = none := by
    rcases missing with missing | missing
    · subst dimension
      cases xs <;> rfl
    · subst columns
      cases xs <;> cases dimension <;> rfl
  simp only [Participant.owned, ↓reduceIte, absent]

/-- A nonowner skips the actual Local values helper. -/
theorem values_nonowner (self owner : Nat) (different : owner ≠ self)
    (args : Values (Component (assignment F G)) tableTypes) :
    Participant.owned self owner (invoke (program.payload.meanings F G) valuesHelper) args =
      .done (.cons none .nil) :=
  Participant.owned_other self owner different _ args

/-- The actual selected Math closure satisfies the generic admission-totality law. -/
theorem projection_admitted_returns (args : Values (assignment F G) tableTypes) :
    Returns (invoke (program.payload.meanings F G) projectionHelper args) :=
  Evaluation.admitted_realization_helper_returns SiteObservations.closed
    program.subject.payload projectionHelper
    (subjectImported.realizationRootSelected realization_retained) args

/-- Imported retained-root evidence proves actual realization invocation total. -/
theorem realization_admitted_returns (args : Values (assignment F G) tableTypes) :
    Returns (invoke (program.payload.meanings F G) realizationHelper args) :=
  Evaluation.imported_realization_returns SiteObservations.closed subjectImported
    realizationDeclaration realization_retained realizationDefinition
    realization_member realization_derived args

set_option backward.isDefEq.respectTransparency false in
/-- The complete owning protocol fails before table validation when any input is absent. -/
theorem participant_missing (args : Values (Component (assignment F G)) tableTypes)
    (missing : RoleFamily.sequence args = none) :
    program.subject.participant F G 0 args = .halt .incomplete := by
  have stopped (table : Evaluation.Meanings F G (participantInterface F G)) :
      Participant.owned 0 0 (invoke table PrimitiveTableViews.tableHelper) args =
        .halt .incomplete := by
    simp only [Participant.owned, ↓reduceIte, missing]
  rw [Program.participant_direct]
  cases args with
  | cons xs rest => cases rest with
    | cons dimension rest => cases rest with
      | cons columns rest =>
        cases rest
        change ((Participant.owned 0 0 (invoke _ PrimitiveTableViews.tableHelper)
          (.cons xs (.cons dimension (.cons columns .nil)))).bind _).bind _ = _
        rw [stopped]
        rfl

set_option backward.isDefEq.respectTransparency false in
/-- The checked singleton projection transfers the exact validated source result. -/
theorem participant_equation (xs : List F) (dimension columns : Nat)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    program.subject.participant F G 0 (inputs xs dimension columns).present =
      if HasShape xs dimension columns then .done (.cons (some xs) .nil)
      else .halt .reject := by
  rw [program.participant_eq_denote]
  change ((program.denote F G (inputs xs dimension columns)).interpret closedLift).bind _ = _
  rw [process_equation xs dimension columns lengthBound dimensionBound columnsBound]
  split <;> rfl

end ZkcExamples.Structured.RealizationValues
