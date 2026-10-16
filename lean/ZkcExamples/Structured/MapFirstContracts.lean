module

public import ZkcExamples.Structured.MapFirstLaws
public import Zkc.Source.Structured.Linking
public import Zkc.Source.Structured.MapLaws

@[expose] public section

namespace ZkcExamples.Structured
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws MapFirstBodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

namespace MapFirstContracts

/-- Only dependencies shared by the actual First clients are required. -/
structure Bodies (definitions : List CheckedDefinition) : Prop where
  less : BodyIn definitions lessHelper lessBody
  rows : BodyIn definitions rowsHelper rowsBody
  shape : BodyIn definitions shapeHelper shapeBody
  table : BodyIn definitions tableHelper tableBody
  halves : BodyIn definitions halvesHelper halvesBody
  interpolate : BodyIn definitions interpolateHelper interpolateBody
  map : BodyIn definitions mapHelper mapBody
  first : BodyIn definitions firstHelper firstBody

variable {definitions : List CheckedDefinition}
    (linked : DeclarationsLinked [] definitions) (bodies : Bodies definitions)
include linked bodies

set_option backward.isDefEq.respectTransparency false in
/-- Actual membership plus raw-body equality discharges the comparison premise. -/
theorem less_law : LessLaw (closedMeanings (F := F) (G := G) definitions) := by
  intro a b aBound bBound
  exact (bodies.less.invoke linked (.cons a (.cons b .nil))).trans
      (less_body _ a b aBound bBound)

set_option backward.isDefEq.respectTransparency false in
/-- The full table supplies the loop equation, including every checked step. -/
theorem rows_law : RowsLaw (closedMeanings (F := F) (G := G) definitions) := by
  intro dimension bound
  exact (bodies.rows.invoke linked (indexResult dimension)).trans
      (rows_body _ (less_law linked bodies) dimension bound)

set_option backward.isDefEq.respectTransparency false in
/-- The actual retained has_shape helper has this universal conditional equation. -/
theorem shape_equation (xs : List F) (dimension columns : Nat)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    invoke (closedMeanings (F := F) (G := G) definitions) shapeHelper (inputs xs dimension columns) =
      .done (boolResult (decide (HasShape xs dimension columns))) :=
  (bodies.shape.invoke linked (inputs xs dimension columns)).trans
      (shape_body _ (less_law linked bodies) (rows_law linked bodies) xs dimension columns lengthBound dimensionBound columnsBound)

set_option backward.isDefEq.respectTransparency false in
/-- The checked constructor preserves all three original outputs in order. -/
theorem table_equation (xs : List F) (dimension columns : Nat)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    invoke (closedMeanings (F := F) (G := G) definitions) tableHelper (inputs xs dimension columns) =
      if HasShape xs dimension columns then .done (inputs xs dimension columns) else .halt .reject := by
  have actual := bodies.table.invoke (F := F) (G := G) linked (inputs xs dimension columns)
  have equation := table_body (closedMeanings (F := F) (G := G) definitions) xs dimension columns
    (decide (HasShape xs dimension columns))
    (shape_equation linked bodies (G := G) xs dimension columns lengthBound dimensionBound columnsBound)
  simp only [decide_eq_true_eq] at equation
  exact actual.trans equation

set_option backward.isDefEq.respectTransparency false in
/-- The source helper itself checks dimension and split shape, not columns. -/
theorem halves_equation (xs : List F) (dimension columns : Nat)
    (dimensionBound : dimension < indexLimit) :
    invoke (closedMeanings (F := F) (G := G) definitions) halvesHelper (inputs xs dimension columns) =
      if 0 < dimension then
        if 0 < xs.length ∧ xs.length % 2 = 0 then
          .done (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) .nil))
        else .halt .refused
      else .halt .reject :=
  (bodies.halves.invoke linked (inputs xs dimension columns)).trans
      (halves_body _ (less_law linked bodies) xs dimension columns dimensionBound)

set_option backward.isDefEq.respectTransparency false in
/-- Arithmetic is established from the retained Math body, not its symbol name. -/
theorem interpolate_equation (low high r : F) :
    invoke (closedMeanings (F := F) (G := G) definitions) interpolateHelper
      (.cons low (.cons high (.cons r .nil))) =
      .done (.cons (low + (high - low) * r) .nil) := by
  refine (bodies.interpolate.invoke linked (.cons low (.cons high (.cons r .nil)))).trans ?_
  rw [MapSourceExpansions.first_interpolate]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Complete actual table discharges the generic map helper premise. -/
theorem map_law : MapLaw (closedMeanings (F := F) (G := G) definitions) := by
  intro low high r sameLength small
  refine (bodies.map.invoke linked (.cons low (.cons high (.cons r .nil)))).trans ?_
  rw [MapSourceExpansions.first_map]
  have mapped := Evaluation.denoteMap_twoRows_broadcast (closedMeanings (F := F) (G := G) definitions)
    MapFirstBodies.mapSpec.helperName MapFirstBodies.mapSpec.field low high r small sameLength.symm
    (fun lo hi => lo + (hi - lo) * r) (fun lo hi => interpolate_equation linked bodies lo hi r)
  exact (congrArg (fun process : Closed (Values (assignment F G) [vector]) =>
    process.bind fun result =>
      (.done (.cons (result.get .here) .nil) : Closed (Values (assignment F G) [vector])))
    mapped).trans (by rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Checked body lookup is repeated for this complete Payload. -/
theorem first_equation (xs : List F) (dimension columns : Nat) (r : F)
    (shape : HasShape xs dimension columns) (lengthBound : xs.length < indexLimit) :
    invoke (closedMeanings (F := F) (G := G) definitions) firstHelper (firstInputs xs dimension columns r) =
      if 0 < dimension then
        .done (inputs (Zkc.Polynomial.Multilinear.restrictValues xs r) (dimension - 1) columns)
      else .halt .reject :=
  (bodies.first.invoke linked (firstInputs xs dimension columns r)).trans
      (MapFirstLaws.first_body _ (halves_equation linked bodies) (map_law linked bodies) xs dimension columns r shape lengthBound)


/-- Total comparison and the bounded library laws derived in this table. -/
structure Laws (table : Meanings F G) : Prop where
  less : LessAllLaw table
  halves : HalvesLaw table
  shape : ∀ (xs : List F) (dimension columns : Nat),
    xs.length < indexLimit → dimension < indexLimit → columns < indexLimit →
    invoke table shapeHelper (inputs xs dimension columns) =
      .done (boolResult (decide (HasShape xs dimension columns)))
  tableLaw : ∀ (xs : List F) (dimension columns : Nat),
    xs.length < indexLimit → dimension < indexLimit → columns < indexLimit →
    invoke table tableHelper (inputs xs dimension columns) =
      if HasShape xs dimension columns then .done (inputs xs dimension columns) else .halt .reject
  first : ∀ (xs : List F) (dimension columns : Nat) (r : F),
    HasShape xs dimension columns → xs.length < indexLimit →
    invoke table firstHelper (firstInputs xs dimension columns r) =
      if 0 < dimension then
        .done (inputs (Zkc.Polynomial.Multilinear.restrictValues xs r) (dimension - 1) columns)
      else .halt .reject

set_option backward.isDefEq.respectTransparency false in
theorem less_all : LessAllLaw (closedMeanings (F := F) (G := G) definitions) := by
  intro a b
  exact (bodies.less.invoke linked (.cons a (.cons b .nil))).trans
    (less_generic_body_all _ a b)

/-- A fixed dependency chain, proved once and instantiated separately per source. -/
theorem laws_of_bodies : Laws (closedMeanings (F := F) (G := G) definitions) :=
  ⟨less_all linked bodies, halves_equation linked bodies, shape_equation linked bodies,
    table_equation linked bodies, first_equation linked bodies⟩

end MapFirstContracts
end ZkcExamples.Structured
