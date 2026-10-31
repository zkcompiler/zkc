module

public import Zkc.Protocols.TableMembership.ReferenceBodies
public import Zkc.Source.Structured.ReferenceLaws
public import Zkc.Semantics.TableRelation

@[expose] public section

/-! Equations for any linked eager table-membership helper closure.
Exact associated bodies carry source authority. Empty domains, inactive queries
and exhausted scans retain their source outcomes. -/
namespace Zkc.Protocols.TableMembership.Source
open Zkc.Source Zkc.Source.Structured

set_option backward.isDefEq.respectTransparency false

/-- Each premise selects an exact typed body in the actual linked closure. -/
structure Bodies (definitions : List CheckedDefinition) (field : String) (bindings : Names) : Prop where
  containsDecision : BodyIn definitions (containsDecisionHelper field bindings) (containsDecisionBody field bindings)
  containsStep : BodyIn definitions (containsStepHelper field bindings) (containsStepBody field bindings)
  contains : BodyIn definitions (containsHelper field bindings) (containsBody field bindings)
  queryDecision : BodyIn definitions (queryDecisionHelper field bindings) (queryDecisionBody field bindings)
  queryStep : BodyIn definitions (queryStepHelper field bindings) (queryStepBody field bindings)
  membership : BodyIn definitions (membershipHelper field bindings) (membershipBody field bindings)
  formula : BodyIn definitions (formulaHelper field bindings) (formulaBody field bindings)

variable {field : String} {bindings : Names} {definitions : List CheckedDefinition}

abbrev scalar (field : String) : Ty := .field field
abbrev vector (field : String) : Ty := .vector field
abbrev query (field : String) (bindings : Names) : Ty := (queryStepHelper field bindings).inputs[1]

abbrev containsFold (field : String) (bindings : Names) : FoldSpec :=
  ⟨DomainSpec.elements bindings.containsDomain [(vector field)] (.vector field) .here,
    [.boolean], [(scalar field)], (containsStepHelper field bindings).name, "", .math⟩

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev meanings (definitions : List CheckedDefinition) : Meanings F G := closedMeanings definitions


theorem containsDecision_equation (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (found : Bool) (row value : F) :
    invoke (meanings (F := F) (G := G) definitions) (containsDecisionHelper field bindings)
      (.cons found (.cons row (.cons value .nil))) =
      .done (.cons (found || decide (row = value)) .nil) := by
  rw [bodies.containsDecision.invoke linked, Evaluation.denote_meaning_eq_meaningOn]
  exact (containsDecisionLaw (ringModel F G) field bindings).valid _ _ trivial

theorem containsStep_equation (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (table : List F) (found : Bool) (row value : F) :
    invoke (meanings (F := F) (G := G) definitions) (containsStepHelper field bindings)
      (.cons found (.cons row (.cons table (.cons value .nil)))) =
      .done (.cons (found || decide (row = value)) .nil) := by
  rw [bodies.containsStep.invoke linked]
  change (invoke (meanings (F := F) (G := G) definitions) (containsDecisionHelper field bindings) (.cons found (.cons row (.cons value .nil)))).bind _ = _
  rw [(containsDecision_equation linked bodies)]
  rfl

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem contains_fold (table : List F) (value : F) (found : Bool) :
    table.foldl (fun (state : Values (assignment F G) [.boolean]) row =>
      Values.cons (state.get .here || decide (row = value)) .nil) (.cons found .nil) =
      .cons (table.foldl (fun state row => state || decide (row = value)) found) .nil := by
  induction table generalizing found with
  | nil => rfl
  | cons row rest ih => exact ih _

theorem contains_bounded (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (table : List F) (value : F) (bounded : table.length < indexLimit) :
    invoke (meanings (F := F) (G := G) definitions) (containsHelper field bindings) (.cons table (.cons value .nil)) =
      .done (.cons (PIR.Relation.Table.contains table value) .nil) := by
  rw [bodies.contains.invoke linked]
  simp only [containsBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Values.get, Regions.denote,
    PIR.Process.bind, Environment.prepend, Environment.push]
  have admitted : (containsFold field bindings).domain.admit (Values.cons table
      (Values.nil : Values (assignment F G) [])) =
      .returned (table.map fun item => .cons item .nil) := by
    simp [containsFold, DomainSpec.admit_elements, Collection.values, Values.get, bounded]
  have folded := Evaluation.denoteFold_reference_map (meanings definitions) (containsFold field bindings)
    (.cons table .nil) (.cons false .nil) (.cons value .nil) table (fun item => .cons item .nil) admitted
    (fun (state : Values (assignment F G) [.boolean]) row =>
      Values.cons (state.get .here || decide (row = value)) .nil) (fun _ => True) trivial (by
      intro state row _ _
      cases state with | cons found rest => ?_
      cases rest
      constructor
      · exact (Evaluation.foldTransition_unfiltered _ (containsFold field bindings) rfl _ _ _ _).trans
          ((containsStep_equation linked bodies) table found row value)
      · trivial)
  change (Evaluation.denoteFold _ (containsFold field bindings)
    ((Values.cons table Values.nil).append
      ((Values.cons false Values.nil).append (Values.cons value Values.nil)))).bind _ = _
  erw [folded, contains_fold (G := G) table value false]
  rfl

theorem contains_exhausted (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (table : List F) (value : F) (unbounded : ¬table.length < indexLimit) :
    invoke (meanings (F := F) (G := G) definitions) (containsHelper field bindings) (.cons table (.cons value .nil)) =
      .halt .exhausted := by
  rw [bodies.contains.invoke linked]
  simp only [containsBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Values.get, Regions.denote,
    PIR.Process.bind, Environment.prepend, Environment.push]
  change (Finite.admitThen ((containsFold field bindings).domain.admit
    (Values.cons table (.nil : Values (assignment F G) []))) _).bind _ = _
  simp [containsFold, DomainSpec.admit_elements, Collection.values, Values.get,
    unbounded, Finite.admitThen, PIR.Process.bind]

/-- The nominal (query field bindings) carrier retains both ordered fields, including an inactive
value. This view only names the existing product interpretation. -/
abbrev QueryValue (F : Type) := Bool × (F × Unit)

def decodeQuery {F : Type} (value : QueryValue F) : PIR.Relation.Table.Query F :=
  ⟨value.1, value.2.1⟩

abbrev membershipFold (field : String) (bindings : Names) : FoldSpec :=
  ⟨DomainSpec.elements bindings.membershipDomain [.sequence (query field bindings)]
      (.sequence (query field bindings)) .here,
    [.boolean], [(vector field)], (queryStepHelper field bindings).name, "", .math⟩

theorem queryDecision_bounded (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (table : List F) (valid active : Bool) (value : F)
    (bounded : table.length < indexLimit) :
    invoke (meanings (F := F) (G := G) definitions) (queryDecisionHelper field bindings)
      (.cons valid (.cons active (.cons value (.cons table .nil)))) =
      .done (.cons (valid && (!active || PIR.Relation.Table.contains table value)) .nil) := by
  rw [bodies.queryDecision.invoke linked]
  change (invoke (meanings (F := F) (G := G) definitions) (containsHelper field bindings)
    (.cons table (.cons value .nil))).bind _ = _
  rw [(contains_bounded linked bodies) table value bounded]
  cases active <;> rfl

theorem queryDecision_exhausted (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (table : List F) (valid active : Bool) (value : F)
    (unbounded : ¬table.length < indexLimit) :
    invoke (meanings (F := F) (G := G) definitions) (queryDecisionHelper field bindings)
      (.cons valid (.cons active (.cons value (.cons table .nil)))) = .halt .exhausted := by
  rw [bodies.queryDecision.invoke linked]
  change (invoke (meanings (F := F) (G := G) definitions) (containsHelper field bindings)
    (.cons table (.cons value .nil))).bind _ = _
  rw [(contains_exhausted linked bodies) table value unbounded]
  rfl

theorem queryStep_bounded (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (table : List F) (queries : List (QueryValue F))
    (valid : Bool) (item : QueryValue F) (bounded : table.length < indexLimit) :
    invoke (meanings (F := F) (G := G) definitions) (queryStepHelper field bindings)
      (.cons valid (.cons item (.cons queries (.cons table .nil)))) =
      .done (.cons (valid && (!item.1 || PIR.Relation.Table.contains table item.2.1)) .nil) := by
  rw [bodies.queryStep.invoke linked]
  change (invoke (meanings (F := F) (G := G) definitions) (queryDecisionHelper field bindings)
    (.cons valid (.cons item.1 (.cons item.2.1 (.cons table .nil))))).bind _ = _
  rw [(queryDecision_bounded linked bodies) table valid item.1 item.2.1 bounded]
  rfl

theorem queryStep_exhausted (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (table : List F) (queries : List (QueryValue F))
    (valid : Bool) (item : QueryValue F) (unbounded : ¬table.length < indexLimit) :
    invoke (meanings (F := F) (G := G) definitions) (queryStepHelper field bindings)
      (.cons valid (.cons item (.cons queries (.cons table .nil)))) = .halt .exhausted := by
  rw [bodies.queryStep.invoke linked]
  change (invoke (meanings (F := F) (G := G) definitions) (queryDecisionHelper field bindings)
    (.cons valid (.cons item.1 (.cons item.2.1 (.cons table .nil))))).bind _ = _
  rw [(queryDecision_exhausted linked bodies) table valid item.1 item.2.1 unbounded]
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

theorem membership_bounded (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (table : List F) (queries : List (QueryValue F))
    (tableBounded : table.length < indexLimit) (queriesBounded : queries.length < indexLimit) :
    invoke (meanings (F := F) (G := G) definitions) (membershipHelper field bindings) (.cons table (.cons queries .nil)) =
      .done (.cons (PIR.Relation.Table.membership table (queries.map decodeQuery)) .nil) := by
  rw [bodies.membership.invoke linked]
  change (Evaluation.denoteFold (meanings (F := F) (G := G) definitions) (membershipFold field bindings)
    ((Values.cons queries Values.nil).append
      ((Values.cons true Values.nil).append (Values.cons table Values.nil)))).bind _ = _
  have admitted : (membershipFold field bindings).domain.admit (carriers := uniformCarriers F G) (Values.cons queries
      (Values.nil : Values (assignment F G) [])) =
      .returned (queries.map fun item => .cons item .nil) := by
    simp [membershipFold, DomainSpec.admit_elements, Collection.values, Values.get, queriesBounded]
  have folded := Evaluation.denoteFold_reference_map (meanings definitions) (membershipFold field bindings)
    (.cons queries .nil) (.cons true .nil) (.cons table .nil) queries (fun item => .cons item .nil) admitted
    (fun (state : Values (assignment F G) [.boolean]) item =>
      Values.cons (state.get .here && (!item.1 || PIR.Relation.Table.contains table item.2.1)) .nil)
    (fun _ => True) trivial (by
      intro state item _ _
      cases state with | cons valid rest => ?_
      cases rest
      constructor
      · exact (Evaluation.foldTransition_unfiltered _ (membershipFold field bindings) rfl _ _ _ _).trans
          ((queryStep_bounded linked bodies) table queries valid item tableBounded)
      · trivial)
  erw [folded, membership_fold (G := G) table queries true]
  rfl

/-- No callback is reached, so no bound on the table is required. -/
theorem membership_empty (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (table : List F) :
    invoke (meanings (F := F) (G := G) definitions) (membershipHelper field bindings) (.cons table (.cons [] .nil)) =
      .done (.cons true .nil) := by
  rw [bodies.membership.invoke linked]
  change (Evaluation.denoteFold (meanings (F := F) (G := G) definitions) (membershipFold field bindings)
    ((Values.cons [] Values.nil).append
      ((Values.cons true Values.nil).append (Values.cons table Values.nil)))).bind _ = _
  rw [Evaluation.denoteFold_empty _ (membershipFold field bindings) _ _ _ (by
    rfl)]
  rfl

theorem membership_queries_exhausted (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (table : List F) (queries : List (QueryValue F))
    (unbounded : ¬queries.length < indexLimit) :
    invoke (meanings (F := F) (G := G) definitions) (membershipHelper field bindings) (.cons table (.cons queries .nil)) =
      .halt .exhausted := by
  rw [bodies.membership.invoke linked]
  change (Finite.admitThen ((membershipFold field bindings).domain.admit (carriers := uniformCarriers F G)
    (Values.cons queries (.nil : Values (assignment F G) []))) _).bind _ = _
  simp [membershipFold, DomainSpec.admit_elements, Collection.values, Values.get,
    unbounded, Finite.admitThen, PIR.Process.bind]

/-- Inactive rows and an already false accumulator still reach the table scan. -/
theorem membership_table_exhausted (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (table : List F) (item : QueryValue F)
    (queries : List (QueryValue F)) (bounded : (item :: queries).length < indexLimit)
    (unbounded : ¬table.length < indexLimit) :
    invoke (meanings (F := F) (G := G) definitions) (membershipHelper field bindings)
      (.cons table (.cons (item :: queries) .nil)) = .halt .exhausted := by
  rw [bodies.membership.invoke linked]
  change (Evaluation.denoteFold (meanings (F := F) (G := G) definitions) (membershipFold field bindings)
    ((Values.cons (item :: queries) Values.nil).append
      ((Values.cons true Values.nil).append (Values.cons table Values.nil)))).bind _ = _
  rw [Evaluation.denoteFold_pack]
  have admitted : (membershipFold field bindings).domain.admit (carriers := uniformCarriers F G) (Values.cons (item :: queries)
      (Values.nil : Values (assignment F G) [])) =
      .returned ((item :: queries).map fun value => .cons value .nil) := by
    simp only [membershipFold, DomainSpec.admit_elements, Collection.values, Values.get,
      ite_eq_left bounded]
  simp only [admitted, Finite.admitThen, List.map_cons, Finite.fold]
  rw [Evaluation.foldTransition_unfiltered _ (membershipFold field bindings) rfl]
  change ((invoke (meanings (F := F) (G := G) definitions) (queryStepHelper field bindings)
    (.cons true (.cons item (.cons (item :: queries) (.cons table .nil))))).bind _).bind _ = _
  rw [(queryStep_exhausted linked bodies) table (item :: queries) true item unbounded]
  rfl

/-- The return domain describes reached finite admission, not a native ABI. -/
abbrev Admissible (table : List F) (queries : List (QueryValue F)) : Prop :=
  queries.length < indexLimit ∧ (queries = [] ∨ table.length < indexLimit)

theorem membership_equation (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (table : List F) (queries : List (QueryValue F)) :
    invoke (meanings (F := F) (G := G) definitions) (membershipHelper field bindings) (.cons table (.cons queries .nil)) =
      if Admissible table queries then
        .done (.cons (PIR.Relation.Table.membership table (queries.map decodeQuery)) .nil)
      else .halt .exhausted := by
  by_cases admitted : Admissible table queries
  · rw [ite_eq_left admitted]
    obtain ⟨queriesBounded, empty | tableBounded⟩ := admitted
    · subst queries
      exact (membership_empty linked bodies) table
    · exact (membership_bounded linked bodies) table queries tableBounded queriesBounded
  · rw [ite_eq_right admitted]
    by_cases queriesBounded : queries.length < indexLimit
    · cases queries with
      | nil => exact False.elim (admitted ⟨queriesBounded, Or.inl rfl⟩)
      | cons item rest =>
        exact (membership_table_exhausted linked bodies) table item rest queriesBounded
          (fun tableBounded => admitted ⟨queriesBounded, Or.inr tableBounded⟩)
    · exact (membership_queries_exhausted linked bodies) table queries queriesBounded

set_option maxRecDepth 4000

theorem formula_equation (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings) (table : List F) (queries : List (QueryValue F)) :
    invoke (meanings (F := F) (G := G) definitions) (formulaHelper field bindings) (.cons table (.cons queries .nil)) =
      if Admissible table queries then
        .done (.cons (PIR.Relation.Table.membership table (queries.map decodeQuery)) .nil)
      else .halt .exhausted := by
  rw [bodies.formula.invoke linked]
  change (invoke (meanings (F := F) (G := G) definitions) (membershipHelper field bindings)
    (.cons table (.cons queries .nil))).bind _ = _
  rw [(membership_equation linked bodies)]
  split <;> rfl

end Zkc.Protocols.TableMembership.Source
