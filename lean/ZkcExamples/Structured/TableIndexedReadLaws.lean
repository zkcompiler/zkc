module

public import ZkcExamples.Structured.TableIndexedReadViews
public import Zkc.Semantics.TableRelation

@[expose] public section

/-! The retained indexed-read source scans a finite index domain. Every reached
read is in range; the requested coordinate may be arbitrary. -/
namespace ZkcExamples.Structured.TableIndexedReadLaws
open Zkc.Source Zkc.Source.Structured TableIndexedReadBodies TableIndexedReadViews
open TableIndexedReadViews.Associations

set_option backward.isDefEq.respectTransparency false

abbrev vector : Ty := .vector "koala-bear"
abbrev scalar : Ty := .field "koala-bear"
abbrev readFold : FoldSpec :=
  ⟨⟨"finite_" ++ indexedReadHelper.name ++ "_s4_domain", [vector], .vector "koala-bear", .here, true⟩,
    [.boolean], [.index, scalar], readStepHelper.name, "", .math⟩

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev meanings : Meanings F G := closedMeanings unit.definitions

theorem readDecision_equation (table : List F) (found : Bool) (coordinate position : Nat)
    (value : F) (bounded : coordinate < table.length) :
    invoke (meanings (F := F) (G := G)) readDecisionHelper
      (.cons found (.cons coordinate (.cons position (.cons table (.cons value .nil))))) =
      .done (.cons (found || (decide (coordinate = position) &&
        decide (table[coordinate]? = some value))) .nil) := by
  rw [readDecision_association.invoke unit.linked]
  change ((match table[coordinate]? with
    | some row => (PIR.Process.done (Values.cons row Values.nil) :
        Closed (Values (assignment F G) [scalar]))
    | none => .halt .refused).bind _) = _
  rw [List.getElem?_eq_getElem bounded]
  simp only [Option.some.injEq]
  rfl

theorem readStep_equation (table : List F) (found : Bool) (coordinate position : Nat)
    (value : F) (bounded : coordinate < table.length) :
    invoke (meanings (F := F) (G := G)) readStepHelper
      (.cons found (.cons coordinate (.cons table (.cons position (.cons value .nil))))) =
      .done (.cons (found || (decide (coordinate = position) &&
        decide (table[coordinate]? = some value))) .nil) := by
  rw [readStep_association.invoke unit.linked]
  change (invoke (meanings (F := F) (G := G)) readDecisionHelper
    (.cons found (.cons coordinate (.cons position (.cons table (.cons value .nil)))))).bind _ = _
  rw [readDecision_equation table found coordinate position value bounded]
  rfl

private def step (table : List F) (position : Nat) (value : F) (found : Bool) (coordinate : Nat) : Bool :=
  found || (decide (coordinate = position) && decide (table[coordinate]? = some value))

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem read_fold_values (table : List F) (position : Nat) (value : F)
    (coordinates : List Nat) (found : Bool) :
    coordinates.foldl (fun (state : Values (assignment F G) [.boolean]) coordinate =>
      Values.cons (step table position value (state.get .here) coordinate) .nil) (.cons found .nil) =
      .cons (coordinates.foldl (step table position value) found) .nil := by
  induction coordinates generalizing found with
  | nil => rfl
  | cons coordinate rest ih => exact ih _

omit [CommRing F] in
private theorem read_fold_true (table : List F) (position : Nat) (value : F)
    (coordinates : List Nat) (found : Bool) :
    coordinates.foldl (step table position value) found = true ↔
      found = true ∨ ∃ coordinate ∈ coordinates,
        coordinate = position ∧ table[coordinate]? = some value := by
  induction coordinates generalizing found with
  | nil => simp
  | cons coordinate rest ih =>
    simp only [List.foldl_cons, ih, step, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.mem_cons, exists_eq_or_imp]
    exact or_assoc

omit [CommRing F] in
private theorem read_fold_exact (table : List F) (position : Nat) (value : F) :
    (List.range table.length).foldl (step table position value) false =
      PIR.Relation.Table.indexedRead table position value := by
  apply Bool.eq_iff_iff.mpr
  rw [read_fold_true, PIR.Relation.Table.indexedRead_exact]
  simp only [Bool.false_eq_true, false_or, List.mem_range, PIR.Relation.Table.IndexedRead]
  constructor
  · rintro ⟨coordinate, _, rfl, selected⟩
    exact selected
  · intro selected
    exact ⟨position, (List.getElem?_eq_some_iff.mp selected).1, rfl, selected⟩

theorem indexedRead_bounded (table : List F) (position : Nat) (value : F)
    (bounded : table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) indexedReadHelper
      (.cons table (.cons position (.cons value .nil))) =
      .done (.cons (PIR.Relation.Table.indexedRead table position value) .nil) := by
  rw [indexedRead_association.invoke unit.linked]
  simp only [indexedReadBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Values.get, Regions.denote,
    PIR.Process.bind, Environment.prepend, Environment.push]
  have admitted : (readFold.domain.denote (Values.cons table
      (Values.nil : Values (assignment F G) []))).admit = .returned (List.range table.length) := by
    change (Finite.Domain.check (table.length < indexLimit) .exhausted
      (.elements (List.range table.length))).admit = _
    simp [Finite.Domain.admit, bounded]
  have folded := Evaluation.denoteFold_reference meanings readFold
    (.cons table .nil) (.cons false .nil) (.cons position (.cons value .nil))
    (List.range table.length) admitted
    (fun (state : Values (assignment F G) [.boolean]) coordinate =>
      Values.cons (step table position value (state.get .here) coordinate) .nil)
    (fun _ => True) trivial (by
      intro state coordinate reached _
      cases state with | cons found rest => ?_
      cases rest
      constructor
      · exact (Evaluation.foldTransition_unfiltered _ readFold rfl _ _ _ _).trans
          (readStep_equation table found coordinate position value (List.mem_range.mp reached))
      · trivial)
  change (Evaluation.denoteFold _ readFold
    ((Values.cons table Values.nil).append ((Values.cons false Values.nil).append
      (Values.cons position (Values.cons value Values.nil))))).bind _ = _
  erw [folded, read_fold_values (G := G) table position value (List.range table.length) false,
    read_fold_exact]
  rfl

theorem indexedRead_exhausted (table : List F) (position : Nat) (value : F)
    (unbounded : ¬table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) indexedReadHelper
      (.cons table (.cons position (.cons value .nil))) = .halt .exhausted := by
  rw [indexedRead_association.invoke unit.linked]
  simp only [indexedReadBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Values.get, Regions.denote,
    PIR.Process.bind, Environment.prepend, Environment.push]
  change (Finite.execute (Finite.Domain.check (decide (table.length < indexLimit))
    .exhausted (.elements (List.range table.length))) _ _).bind _ = _
  simp [Finite.execute, Finite.Domain.admit, unbounded, Finite.admitThen, PIR.Process.bind]

theorem indexedRead_equation (table : List F) (position : Nat) (value : F) :
    invoke (meanings (F := F) (G := G)) indexedReadHelper
      (.cons table (.cons position (.cons value .nil))) =
      if table.length < indexLimit then
        .done (.cons (PIR.Relation.Table.indexedRead table position value) .nil)
      else .halt .exhausted := by
  split
  · exact indexedRead_bounded table position value ‹_›
  · exact indexedRead_exhausted table position value ‹_›

set_option maxRecDepth 4000 in
theorem formula_equation (table : List F) (position : Nat) (value : F) :
    invoke (meanings (F := F) (G := G)) formulaHelper
      (.cons table (.cons position (.cons value .nil))) =
      if table.length < indexLimit then
        .done (.cons (PIR.Relation.Table.indexedRead table position value) .nil)
      else .halt .exhausted := by
  rw [formula_association.invoke unit.linked]
  change (invoke (meanings (F := F) (G := G)) indexedReadHelper
    (.cons table (.cons position (.cons value .nil)))).bind _ = _
  rw [indexedRead_equation]
  split <;> rfl

end ZkcExamples.Structured.TableIndexedReadLaws
