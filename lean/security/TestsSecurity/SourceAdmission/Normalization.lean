module

public import TestsSecurity.ABIInstallations.ConstrainedLaws
public import TestsSecurity.SourceAdmission.ShapeFixture

@[expose] public section
noncomputable section

/-! Automatic presentations are checked on every optional typed input. The
heterogeneous fixture retains both table clauses and ignores neither one. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.SourceAdmission.Normalization
open Zkc.Source Zkc.Source.Structured

namespace Constrained
open TestsSecurity.ABIInstallations.Constrained

def condition (values : subject.Inputs) : Prop := source_input_condition subject on values

theorem condition_iff (values : subject.Inputs) :
    (∀ index isInput, subject.inputClause values index isInput) ↔ condition values := by
  source_input_clauses

theorem expected (values : subject.Inputs) :
    (∀ index isInput, subject.inputClause values index isInput) ↔
      TestsSecurity.ABIInstallations.ConstrainedLaws.condition values := by
  source_input_clauses

end Constrained

/-- Presence and mathematics of one retained shape application. -/
def tableShape {α : Type} (table : Option (List α)) (rounds : Option Nat)
    (maximum : Nat) : Prop :=
  table.elim False fun table =>
    rounds.elim False fun rounds => table.length = 2 ^ rounds ∧ rounds ≤ maximum

namespace Heterogeneous
open ShapeFixture

def condition (values : subject.Inputs) : Prop := source_input_condition subject on values

theorem condition_iff (values : subject.Inputs) :
    (∀ index isInput, subject.inputClause values index isInput) ↔ condition values := by
  source_input_clauses

theorem expected (values : subject.Inputs) :
    (∀ index isInput, subject.inputClause values index isInput) ↔
      tableShape (values.get .here) (values.get (.there (.there (.there .here)))) 4 ∧
      tableShape (values.get (.there (.there .here)))
        (values.get (.there (.there (.there .here)))) 4 := by
  source_input_clauses

end Heterogeneous

#print axioms Constrained.condition_iff
#print axioms Constrained.expected
#print axioms Heterogeneous.condition_iff
#print axioms Heterogeneous.expected
end TestsSecurity.SourceAdmission.Normalization
