module

/-!
# Problems, witnesses, and admission diagnostics

A promise problem may leave a gap between positive and negative instances. Witnesses are
an additional relation, not a required field of every problem. Admission diagnostics are
logical facts separate from the validity of a requested theorem.
-/

public section

namespace ProtocolProof

universe u v

/-- Positive and negative instances need not exhaust the statement type. -/
structure PromiseProblem (Statement : Type u) where
  yes : Statement → Prop
  no : Statement → Prop
  disjoint : ∀ statement, yes statement → no statement → False

/-- Ordinary truth is the special case without a promise gap. -/
@[expose] def PromiseProblem.ofPredicate {X : Type u} (truth : X → Prop) : PromiseProblem X where
  yes := truth
  no statement := ¬truth statement
  disjoint _ positive negative := negative positive

@[simp] theorem PromiseProblem.ofPredicate_yes {X : Type u} (truth : X → Prop) (x : X) :
    (ofPredicate truth).yes x ↔ truth x := Iff.rfl

@[simp] theorem PromiseProblem.ofPredicate_no {X : Type u} (truth : X → Prop) (x : X) :
    (ofPredicate truth).no x ↔ ¬truth x := Iff.rfl

/-- A witness establishes a positive instance. Coverage, if required, is a separate theorem. -/
structure WitnessRelation {X : Type u} (problem : PromiseProblem X) (Witness : Type v) where
  relates : X → Witness → Prop
  implies_yes : ∀ statement witness, relates statement witness → problem.yes statement

/-- Whether a selected admission predicate has at least one input. Not a proof-route audit. -/
@[expose] def AdmitsInput {E : Type u} (admissible : E → Prop) : Prop := ∃ e, admissible e

/-- Explicitly empty admission makes a universally conditioned claim vacuous. -/
theorem no_admitted_input_vacuous {E : Type u} {admissible : E → Prop}
    (empty : ¬AdmitsInput admissible) (claim : E → Prop) :
    ∀ e, admissible e → claim e := by
  intro e he
  exact (empty ⟨e, he⟩).elim

end ProtocolProof
