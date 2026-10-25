module

public import TestsSecurity.ABIInstallations.Constrained
public import TestsSecurity.ABIInstallations.Heterogeneous
public import ZkcSecurity.Tools.SourceInputClauses

@[expose] public section
noncomputable section

/-! Constructor rows must discard constant presence branches just as abstract
typed rows do. An unused service stays arbitrary, including absence. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.SourceAdmission.Presence
open Zkc.Source Zkc.Source.Structured

namespace Constrained
open TestsSecurity.ABIInstallations.Constrained

theorem present_condition (n : Nat) (service : Option Nat) :
    (source_input_condition subject on
      (show subject.Inputs from .cons (some n) (.cons service .nil))) ↔ n = 1 := Iff.rfl

theorem absent_condition (service : Option Nat) :
    (source_input_condition subject on
      (show subject.Inputs from .cons none (.cons service .nil))) ↔ False := Iff.rfl

end Constrained

namespace NoClauses
open TestsSecurity.ABIInstallations.Heterogeneous

theorem condition_true (values : subject.Inputs) :
    (source_input_condition subject on values) ↔ True := by subject_abi_options

theorem retained_clauses (values : subject.Inputs) :
    (∀ index isInput, subject.inputClause values index isInput) ↔ True := by
  source_input_clauses

end NoClauses
end TestsSecurity.SourceAdmission.Presence
