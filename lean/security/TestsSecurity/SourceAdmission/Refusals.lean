module

public import TestsSecurity.SourceAdmission.Normalization

@[expose] public section
noncomputable section

/-! A checked presentation cannot drop a clause or replace source truth with
True. Automatic interpretation requires a concrete retained source. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.SourceAdmission.Refusals
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Claims.HonestPair

example (_values : TestsSecurity.ABIInstallations.Constrained.subject.Inputs) : True := by
  fail_if_success
    have : (∀ index isInput,
        TestsSecurity.ABIInstallations.Constrained.subject.inputClause _values index isInput) ↔ True := by
      source_input_clauses
  trivial

example (_values : ShapeFixture.subject.Inputs) : True := by
  fail_if_success
    have : (∀ index isInput, ShapeFixture.subject.inputClause _values index isInput) ↔
        Normalization.tableShape (_values.get .here)
          (_values.get (.there (.there (.there .here)))) 4 := by
      source_input_clauses
  trivial

example (candidate : Subject TestsSecurity.ABIInstallations.Fixtures.model
    ShapeFixture.original ShapeFixture.imported ShapeFixture.selected)
    (_values : candidate.Inputs) : True := by
  fail_if_success
    let attempted : Prop := source_input_condition candidate on _values
  trivial

end TestsSecurity.SourceAdmission.Refusals
