module

public import TestsSecurity.ABIInstallations.Constrained
public import ZkcSecurity.Claims.Completeness

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.ABIInstallations.ConstrainedLaws
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair TestsSecurity.ABIInstallations.Fixtures
open TestsSecurity.ABIInstallations.Constrained

/-- Presentation of the admitted source clause, independently of the printer. -/
def condition (values : subject.Inputs) : Prop := values.get .here = some 1

theorem one_clause_iff (values : subject.Inputs) :
    subject.inputClause values ⟨1, by decide⟩ rfl ↔ condition values := by
  cases values with | cons actual rest => ?_
  cases rest with | cons service rest => ?_
  cases rest
  cases actual with
  | none =>
    change (∃ arguments : Values model.Value [.index],
      (none : Option (Values model.Value [.index])) = some arguments ∧ _) ↔
        (none : Option Nat) = some 1
    simp
  | some actual =>
    change (∃ arguments : Values model.Value [.index],
      some (Values.cons actual .nil) = some arguments ∧ _) ↔ some actual = some (1 : Nat)
    constructor
    · rintro ⟨arguments, read, truth⟩
      cases Option.some.inj read
      have accepted := congrArg (fun row => row.get .here) (PIR.Process.done.inj truth)
      change decide (actual = 1) = true at accepted
      simpa using accepted
    · intro same
      cases Option.some.inj same
      exact ⟨.cons 1 .nil, rfl, rfl⟩

theorem condition_iff (values : subject.Inputs) :
    (∀ index isInput, subject.inputClause values index isInput) ↔ condition values := by
  constructor
  · intro clauses
    exact (one_clause_iff values).mp (clauses ⟨1, by decide⟩ rfl)
  · intro holds index isInput
    rcases index with ⟨index, bound⟩
    match index with
    | 0 => cases isInput
    | 1 => exact (one_clause_iff values).mpr holds
    | n + 2 => change n + 2 < 2 at bound; omega

/-- A nondefault witness satisfies the source input clause and ABI range. -/
theorem nonvacuous : Nonvacuous subject := by
  let values : subject.Inputs := .cons (some 1) (.cons none .nil)
  refine ⟨values, ⟨.cons (1 : Nat) .nil, rfl, rfl⟩, ?_⟩
  refine ⟨?_, (condition_iff values).mpr rfl, _, _, rfl, rfl, rfl⟩
  change (1 : Nat) < indexLimit ∧ True ∧ True
  decide +kernel

#print axioms condition_iff
#print axioms nonvacuous
end TestsSecurity.ABIInstallations.ConstrainedLaws
