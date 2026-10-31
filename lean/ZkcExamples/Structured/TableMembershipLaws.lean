module

public import ZkcExamples.Structured.TableMembershipViews
public import Zkc.Semantics.TableRelation

@[expose] public section

/-! Concrete applications of the reusable eager table-membership helper laws.
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
  ⟨DomainSpec.elements ("finite_" ++ containsHelper.name ++ "_s2_domain") [vector] (.vector "koala-bear") .here,
    [.boolean], [scalar], containsStepHelper.name, "", .math⟩

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev meanings : Meanings F G := closedMeanings unit.definitions

theorem containsDecision_equation (found : Bool) (row value : F) :
    invoke (meanings (F := F) (G := G)) containsDecisionHelper
      (.cons found (.cons row (.cons value .nil))) =
      .done (.cons (found || decide (row = value)) .nil) := by
  exact Zkc.Protocols.TableMembership.Source.containsDecision_equation unit.linked installedBodies found row value

theorem containsStep_equation (table : List F) (found : Bool) (row value : F) :
    invoke (meanings (F := F) (G := G)) containsStepHelper
      (.cons found (.cons row (.cons table (.cons value .nil)))) =
      .done (.cons (found || decide (row = value)) .nil) := by
  exact Zkc.Protocols.TableMembership.Source.containsStep_equation unit.linked installedBodies table found row value

theorem contains_bounded (table : List F) (value : F) (bounded : table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) containsHelper (.cons table (.cons value .nil)) =
      .done (.cons (PIR.Relation.Table.contains table value) .nil) := by
  exact Zkc.Protocols.TableMembership.Source.contains_bounded unit.linked installedBodies table value bounded

theorem contains_exhausted (table : List F) (value : F) (unbounded : ¬table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) containsHelper (.cons table (.cons value .nil)) =
      .halt .exhausted := by
  exact Zkc.Protocols.TableMembership.Source.contains_exhausted unit.linked installedBodies table value unbounded

/-- The nominal query carrier retains both ordered fields, including an inactive
value. This view only names the existing product interpretation. -/
abbrev QueryValue (F : Type) := Bool × (F × Unit)

def decodeQuery {F : Type} (value : QueryValue F) : PIR.Relation.Table.Query F :=
  ⟨value.1, value.2.1⟩

abbrev membershipFold : FoldSpec :=
  ⟨DomainSpec.elements ("finite_" ++ membershipHelper.name ++ "_s2_domain") [.sequence query]
      (.sequence query) .here,
    [.boolean], [vector], queryStepHelper.name, "", .math⟩

theorem queryDecision_bounded (table : List F) (valid active : Bool) (value : F)
    (bounded : table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) queryDecisionHelper
      (.cons valid (.cons active (.cons value (.cons table .nil)))) =
      .done (.cons (valid && (!active || PIR.Relation.Table.contains table value)) .nil) := by
  exact Zkc.Protocols.TableMembership.Source.queryDecision_bounded unit.linked installedBodies table valid active value bounded

theorem queryDecision_exhausted (table : List F) (valid active : Bool) (value : F)
    (unbounded : ¬table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) queryDecisionHelper
      (.cons valid (.cons active (.cons value (.cons table .nil)))) = .halt .exhausted := by
  exact Zkc.Protocols.TableMembership.Source.queryDecision_exhausted unit.linked installedBodies table valid active value unbounded

theorem queryStep_bounded (table : List F) (queries : List (QueryValue F))
    (valid : Bool) (item : QueryValue F) (bounded : table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) queryStepHelper
      (.cons valid (.cons item (.cons queries (.cons table .nil)))) =
      .done (.cons (valid && (!item.1 || PIR.Relation.Table.contains table item.2.1)) .nil) := by
  exact Zkc.Protocols.TableMembership.Source.queryStep_bounded unit.linked installedBodies table queries valid item bounded

theorem queryStep_exhausted (table : List F) (queries : List (QueryValue F))
    (valid : Bool) (item : QueryValue F) (unbounded : ¬table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) queryStepHelper
      (.cons valid (.cons item (.cons queries (.cons table .nil)))) = .halt .exhausted := by
  exact Zkc.Protocols.TableMembership.Source.queryStep_exhausted unit.linked installedBodies table queries valid item unbounded

theorem membership_bounded (table : List F) (queries : List (QueryValue F))
    (tableBounded : table.length < indexLimit) (queriesBounded : queries.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) membershipHelper (.cons table (.cons queries .nil)) =
      .done (.cons (PIR.Relation.Table.membership table (queries.map decodeQuery)) .nil) := by
  exact Zkc.Protocols.TableMembership.Source.membership_bounded unit.linked installedBodies table queries tableBounded queriesBounded

/-- No callback is reached, so no bound on the table is required. -/
theorem membership_empty (table : List F) :
    invoke (meanings (F := F) (G := G)) membershipHelper (.cons table (.cons [] .nil)) =
      .done (.cons true .nil) := by
  exact Zkc.Protocols.TableMembership.Source.membership_empty unit.linked installedBodies table

theorem membership_queries_exhausted (table : List F) (queries : List (QueryValue F))
    (unbounded : ¬queries.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) membershipHelper (.cons table (.cons queries .nil)) =
      .halt .exhausted := by
  exact Zkc.Protocols.TableMembership.Source.membership_queries_exhausted unit.linked installedBodies table queries unbounded

/-- Inactive rows and an already false accumulator still reach the table scan. -/
theorem membership_table_exhausted (table : List F) (item : QueryValue F)
    (queries : List (QueryValue F)) (bounded : (item :: queries).length < indexLimit)
    (unbounded : ¬table.length < indexLimit) :
    invoke (meanings (F := F) (G := G)) membershipHelper
      (.cons table (.cons (item :: queries) .nil)) = .halt .exhausted := by
  exact Zkc.Protocols.TableMembership.Source.membership_table_exhausted unit.linked installedBodies table item queries bounded unbounded

/-- The return domain describes reached finite admission, not a native ABI. -/
abbrev Admissible (table : List F) (queries : List (QueryValue F)) : Prop :=
  queries.length < indexLimit ∧ (queries = [] ∨ table.length < indexLimit)

theorem membership_equation (table : List F) (queries : List (QueryValue F)) :
    invoke (meanings (F := F) (G := G)) membershipHelper (.cons table (.cons queries .nil)) =
      if Admissible table queries then
        .done (.cons (PIR.Relation.Table.membership table (queries.map decodeQuery)) .nil)
      else .halt .exhausted := by
  exact Zkc.Protocols.TableMembership.Source.membership_equation unit.linked installedBodies table queries

set_option maxRecDepth 4000 in

theorem formula_equation (table : List F) (queries : List (QueryValue F)) :
    invoke (meanings (F := F) (G := G)) formulaHelper (.cons table (.cons queries .nil)) =
      if Admissible table queries then
        .done (.cons (PIR.Relation.Table.membership table (queries.map decodeQuery)) .nil)
      else .halt .exhausted := by
  exact Zkc.Protocols.TableMembership.Source.formula_equation unit.linked installedBodies table queries

end ZkcExamples.Structured.TableMembershipLaws
