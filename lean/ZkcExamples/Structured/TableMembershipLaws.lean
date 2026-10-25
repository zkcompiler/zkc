module

public import ZkcExamples.Structured.TableMembershipViews
public import Zkc.Semantics.TableRelation

@[expose] public section

/-! Equations for the actual retained table-membership helper closure.
Finite-domain exhaustion is preserved; no native execution correspondence is
inferred from these source-model laws. -/
namespace ZkcExamples.Structured.TableMembershipLaws
open Zkc.Source Zkc.Source.Structured TableMembershipBodies TableMembershipViews
open TableMembershipViews.Associations

set_option backward.isDefEq.respectTransparency false

abbrev scalar : Ty := .field "koala-bear"
abbrev vector : Ty := .vector "koala-bear"
abbrev query : Ty := queryStepHelper.inputs[1]

abbrev containsFold : FoldSpec :=
  ⟨⟨"finite_" ++ containsHelper.name ++ "_s2_domain", [vector], .vector "koala-bear", .here, false⟩,
    [.boolean], [scalar], containsStepHelper.name, "", .math⟩

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev meanings : Meanings F G := closedMeanings unit.definitions

theorem containsDecision_equation (found : Bool) (row value : F) :
    invoke (meanings (F := F) (G := G)) containsDecisionHelper
      (.cons found (.cons row (.cons value .nil))) =
      .done (.cons (found || decide (row = value)) .nil) := by
  rw [containsDecision_association.invoke unit.linked]
  rfl

theorem containsStep_equation (table : List F) (found : Bool) (row value : F) :
    invoke (meanings (F := F) (G := G)) containsStepHelper
      (.cons found (.cons row (.cons table (.cons value .nil)))) =
      .done (.cons (found || decide (row = value)) .nil) := by
  rw [containsStep_association.invoke unit.linked]
  change (invoke (meanings (F := F) (G := G)) containsDecisionHelper (.cons found (.cons row (.cons value .nil)))).bind _ = _
  rw [containsDecision_equation]
  rfl

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem contains_fold (table : List F) (value : F) (found : Bool) :
    table.foldl (fun (state : Values (assignment F G) [.boolean]) row =>
      Values.cons (state.get .here || decide (row = value)) .nil) (.cons found .nil) =
      .cons (table.foldl (fun state row => state || decide (row = value)) found) .nil := by
  induction table generalizing found with
  | nil => rfl
  | cons row rest ih => exact ih _

theorem contains_bounded (table : List F) (value : F) (bounded : table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) containsHelper (.cons table (.cons value .nil)) =
      .done (.cons (PIR.Relation.Table.contains table value) .nil) := by
  rw [contains_association.invoke unit.linked]
  simp only [containsBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Values.get, Regions.denote,
    PIR.Process.bind, Environment.prepend, Environment.push]
  have admitted : (containsFold.domain.denote (Values.cons table
      (Values.nil : Values (assignment F G) []))).admit = .returned table := by
    change (Finite.Domain.check (table.length < indexLimit) .exhausted (.elements table)).admit = _
    simp [Finite.Domain.admit, bounded]
  have folded := Evaluation.denoteFold_reference meanings containsFold
    (.cons table .nil) (.cons false .nil) (.cons value .nil) table admitted
    (fun (state : Values (assignment F G) [.boolean]) row =>
      Values.cons (state.get .here || decide (row = value)) .nil) (fun _ => True) trivial (by
      intro state row _ _
      cases state with | cons found rest => ?_
      cases rest
      constructor
      · exact (Evaluation.foldTransition_unfiltered _ containsFold rfl _ _ _ _).trans
          (containsStep_equation table found row value)
      · trivial)
  change (Evaluation.denoteFold _ containsFold
    ((Values.cons table Values.nil).append
      ((Values.cons false Values.nil).append (Values.cons value Values.nil)))).bind _ = _
  erw [folded, contains_fold (G := G) table value false]
  rfl

theorem contains_exhausted (table : List F) (value : F) (unbounded : ¬table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) containsHelper (.cons table (.cons value .nil)) =
      .halt .exhausted := by
  rw [contains_association.invoke unit.linked]
  simp only [containsBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Values.get, Regions.denote,
    PIR.Process.bind, Environment.prepend, Environment.push]
  change (Finite.execute (Finite.Domain.check (decide (table.length < indexLimit))
    .exhausted (.elements table)) _ _).bind _ = _
  simp [Finite.execute, Finite.Domain.admit, unbounded, Finite.admitThen, PIR.Process.bind]

/-- The nominal query carrier retains both ordered fields, including an inactive
value. This view only names the existing product interpretation. -/
abbrev QueryValue (F : Type) := Bool × (F × Unit)

def decodeQuery {F : Type} (value : QueryValue F) : PIR.Relation.Table.Query F :=
  ⟨value.1, value.2.1⟩

abbrev membershipFold : FoldSpec :=
  ⟨⟨"finite_" ++ membershipHelper.name ++ "_s2_domain", [.sequence query],
      .sequence query, .here, false⟩,
    [.boolean], [vector], queryStepHelper.name, "", .math⟩

theorem queryDecision_bounded (table : List F) (valid active : Bool) (value : F)
    (bounded : table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) queryDecisionHelper
      (.cons valid (.cons active (.cons value (.cons table .nil)))) =
      .done (.cons (valid && (!active || PIR.Relation.Table.contains table value)) .nil) := by
  rw [queryDecision_association.invoke unit.linked]
  change (invoke (meanings (F := F) (G := G)) containsHelper
    (.cons table (.cons value .nil))).bind _ = _
  rw [contains_bounded table value bounded]
  cases active <;> rfl

theorem queryDecision_exhausted (table : List F) (valid active : Bool) (value : F)
    (unbounded : ¬table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) queryDecisionHelper
      (.cons valid (.cons active (.cons value (.cons table .nil)))) = .halt .exhausted := by
  rw [queryDecision_association.invoke unit.linked]
  change (invoke (meanings (F := F) (G := G)) containsHelper
    (.cons table (.cons value .nil))).bind _ = _
  rw [contains_exhausted table value unbounded]
  rfl

theorem queryStep_bounded (table : List F) (queries : List (QueryValue F))
    (valid : Bool) (item : QueryValue F) (bounded : table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) queryStepHelper
      (.cons valid (.cons item (.cons queries (.cons table .nil)))) =
      .done (.cons (valid && (!item.1 || PIR.Relation.Table.contains table item.2.1)) .nil) := by
  rw [queryStep_association.invoke unit.linked]
  change (invoke (meanings (F := F) (G := G)) queryDecisionHelper
    (.cons valid (.cons item.1 (.cons item.2.1 (.cons table .nil))))).bind _ = _
  rw [queryDecision_bounded table valid item.1 item.2.1 bounded]
  rfl

theorem queryStep_exhausted (table : List F) (queries : List (QueryValue F))
    (valid : Bool) (item : QueryValue F) (unbounded : ¬table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) queryStepHelper
      (.cons valid (.cons item (.cons queries (.cons table .nil)))) = .halt .exhausted := by
  rw [queryStep_association.invoke unit.linked]
  change (invoke (meanings (F := F) (G := G)) queryDecisionHelper
    (.cons valid (.cons item.1 (.cons item.2.1 (.cons table .nil))))).bind _ = _
  rw [queryDecision_exhausted table valid item.1 item.2.1 unbounded]
  rfl

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem membership_fold (table : List F) (queries : List (QueryValue F)) (valid : Bool) :
    queries.foldl (fun (state : Values (assignment F G) [.boolean]) item =>
      Values.cons (state.get .here && (!item.1 || PIR.Relation.Table.contains table item.2.1)) .nil)
      (.cons valid .nil) =
      .cons ((queries.map decodeQuery).foldl (fun state item =>
        state && (!item.active || PIR.Relation.Table.contains table item.value)) valid) .nil := by
  induction queries generalizing valid with
  | nil => rfl
  | cons item rest ih => exact ih _

theorem membership_bounded (table : List F) (queries : List (QueryValue F))
    (tableBounded : table.length < indexLimit) (queriesBounded : queries.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) membershipHelper (.cons table (.cons queries .nil)) =
      .done (.cons (PIR.Relation.Table.membership table (queries.map decodeQuery)) .nil) := by
  rw [membership_association.invoke unit.linked]
  change (Evaluation.denoteFold (meanings (F := F) (G := G)) membershipFold
    ((Values.cons queries Values.nil).append
      ((Values.cons true Values.nil).append (Values.cons table Values.nil)))).bind _ = _
  have admitted : (membershipFold.domain.denote (Values.cons queries
      (Values.nil : Values (assignment F G) []))).admit = .returned queries := by
    change (Finite.Domain.check (queries.length < indexLimit) .exhausted (.elements queries)).admit = _
    simp [Finite.Domain.admit, queriesBounded]
  have folded := Evaluation.denoteFold_reference meanings membershipFold
    (.cons queries .nil) (.cons true .nil) (.cons table .nil) queries admitted
    (fun (state : Values (assignment F G) [.boolean]) item =>
      Values.cons (state.get .here && (!item.1 || PIR.Relation.Table.contains table item.2.1)) .nil)
    (fun _ => True) trivial (by
      intro state item _ _
      cases state with | cons valid rest => ?_
      cases rest
      constructor
      · exact (Evaluation.foldTransition_unfiltered _ membershipFold rfl _ _ _ _).trans
          (queryStep_bounded table queries valid item tableBounded)
      · trivial)
  erw [folded, membership_fold (G := G) table queries true]
  rfl

/-- No callback is reached, so no bound on the table is required. -/
theorem membership_empty (table : List F) :
    invoke (meanings (F := F) (G := G)) membershipHelper (.cons table (.cons [] .nil)) =
      .done (.cons true .nil) := by
  rw [membership_association.invoke unit.linked]
  change (Evaluation.denoteFold (meanings (F := F) (G := G)) membershipFold
    ((Values.cons [] Values.nil).append
      ((Values.cons true Values.nil).append (Values.cons table Values.nil)))).bind _ = _
  rw [Evaluation.denoteFold_empty _ membershipFold _ _ _ (by
    change (Finite.Domain.check (0 < indexLimit) .exhausted (.elements [])).admit = _
    rfl)]
  rfl

theorem membership_queries_exhausted (table : List F) (queries : List (QueryValue F))
    (unbounded : ¬queries.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) membershipHelper (.cons table (.cons queries .nil)) =
      .halt .exhausted := by
  rw [membership_association.invoke unit.linked]
  change (Finite.execute (Finite.Domain.check (decide (queries.length < indexLimit))
    .exhausted (.elements queries)) _ _).bind _ = _
  simp [Finite.execute, Finite.Domain.admit, unbounded, Finite.admitThen, PIR.Process.bind]

/-- Inactive rows and an already false accumulator still reach the table scan. -/
theorem membership_table_exhausted (table : List F) (item : QueryValue F)
    (queries : List (QueryValue F)) (bounded : (item :: queries).length < indexLimit)
    (unbounded : ¬table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) membershipHelper
      (.cons table (.cons (item :: queries) .nil)) = .halt .exhausted := by
  rw [membership_association.invoke unit.linked]
  change (Evaluation.denoteFold (meanings (F := F) (G := G)) membershipFold
    ((Values.cons (item :: queries) Values.nil).append
      ((Values.cons true Values.nil).append (Values.cons table Values.nil)))).bind _ = _
  rw [Evaluation.denoteFold_pack]
  have admitted : (membershipFold.domain.denote (Values.cons (item :: queries)
      (Values.nil : Values (assignment F G) []))).admit = .returned (item :: queries) := by
    change (Finite.Domain.check ((item :: queries).length < indexLimit)
      .exhausted (.elements (item :: queries))).admit = _
    simp only [Finite.Domain.admit, decide_eq_true_eq, ite_eq_left bounded]
  simp only [Finite.execute, admitted, Finite.admitThen, Finite.fold]
  rw [Evaluation.foldTransition_unfiltered _ membershipFold rfl]
  change ((invoke (meanings (F := F) (G := G)) queryStepHelper
    (.cons true (.cons item (.cons (item :: queries) (.cons table .nil))))).bind _).bind _ = _
  rw [queryStep_exhausted table (item :: queries) true item unbounded]
  rfl

/-- The return domain describes reached finite admission, not a native ABI. -/
abbrev Admissible (table : List F) (queries : List (QueryValue F)) : Prop :=
  queries.length < indexLimit ∧ (queries = [] ∨ table.length < indexLimit)

theorem membership_equation (table : List F) (queries : List (QueryValue F)) :
    invoke (meanings (F := F) (G := G)) membershipHelper (.cons table (.cons queries .nil)) =
      if Admissible table queries then
        .done (.cons (PIR.Relation.Table.membership table (queries.map decodeQuery)) .nil)
      else .halt .exhausted := by
  by_cases admitted : Admissible table queries
  · rw [ite_eq_left admitted]
    obtain ⟨queriesBounded, empty | tableBounded⟩ := admitted
    · subst queries
      exact membership_empty table
    · exact membership_bounded table queries tableBounded queriesBounded
  · rw [ite_eq_right admitted]
    by_cases queriesBounded : queries.length < indexLimit
    · cases queries with
      | nil => exact False.elim (admitted ⟨queriesBounded, Or.inl rfl⟩)
      | cons item rest =>
        exact membership_table_exhausted table item rest queriesBounded
          (fun tableBounded => admitted ⟨queriesBounded, Or.inr tableBounded⟩)
    · exact membership_queries_exhausted table queries queriesBounded

set_option maxRecDepth 4000 in

theorem formula_equation (table : List F) (queries : List (QueryValue F)) :
    invoke (meanings (F := F) (G := G)) formulaHelper (.cons table (.cons queries .nil)) =
      if Admissible table queries then
        .done (.cons (PIR.Relation.Table.membership table (queries.map decodeQuery)) .nil)
      else .halt .exhausted := by
  rw [formula_association.invoke unit.linked]
  change (invoke (meanings (F := F) (G := G)) membershipHelper
    (.cons table (.cons queries .nil))).bind _ = _
  rw [membership_equation]
  split <;> rfl

end ZkcExamples.Structured.TableMembershipLaws
