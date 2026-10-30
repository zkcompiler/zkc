module

public import ZkcSecurityExamples.Generated.SmallSumcheck
public import ZkcSecurityExamples.Generated.TwoSums
public import TestsSecurity.SourceAdmission.Normalization

@[expose] public section
noncomputable section

/-! These controls use actual current exported subjects, independently of root
ABI generation. Every optional source coordinate is universally quantified. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.SourceAdmission.CurrentSubjects
open Zkc.Source Zkc.Source.Structured
open Normalization (tableShape)

namespace SmallSumcheck
open ZkcSecurity.Examples.Generated.SmallSumcheck

def condition (values : subject.Inputs) : Prop := source_input_condition subject on values

theorem condition_iff (values : subject.Inputs) :
    (∀ index isInput, subject.inputClause values index isInput) ↔ condition values := by
  source_input_clauses

theorem expected (values : subject.Inputs) :
    (∀ index isInput, subject.inputClause values index isInput) ↔
      tableShape (values.get .here) (values.get (.there (.there .here))) 2 := by
  source_input_clauses

end SmallSumcheck

namespace TwoSums
open ZkcSecurity.Examples.Generated.TwoSums

def condition (values : subject.Inputs) : Prop := source_input_condition subject on values

theorem condition_iff (values : subject.Inputs) :
    (∀ index isInput, subject.inputClause values index isInput) ↔ condition values := by
  source_input_clauses

theorem expected (values : subject.Inputs) :
    (∀ index isInput, subject.inputClause values index isInput) ↔
      tableShape (values.get .here) (values.get (.there (.there (.there (.there .here))))) 4 ∧
      tableShape (values.get (.there .here))
        (values.get (.there (.there (.there (.there .here))))) 4 := by
  source_input_clauses

end TwoSums

#print axioms SmallSumcheck.condition_iff
#print axioms SmallSumcheck.expected
#print axioms TwoSums.condition_iff
#print axioms TwoSums.expected
end TestsSecurity.SourceAdmission.CurrentSubjects
