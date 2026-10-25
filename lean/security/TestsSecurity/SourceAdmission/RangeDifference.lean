module

public import TestsSecurity.SourceAdmission.Migration
public import TestsSecurity.ABIInstallations.Heterogeneous

@[expose] public section
noncomputable section

/-! Empty historical policies did not impose executable index bounds.
This is an admitted ABI fixture, not an equivalence claim about other roots. -/
set_option autoImplicit false
namespace TestsSecurity.SourceAdmission.RangeDifference
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Claims.HonestPair
open TestsSecurity.ABIInstallations.Heterogeneous

def outside : subject.Inputs :=
  .cons (some indexLimit) (.cons (some true) (.cons none .nil))

theorem previously_admitted :
    HistoricalPolicy.HonestInput subject ⟨[]⟩ outside := by
  refine ⟨?_, _, _, rfl, rfl, rfl⟩
  intro rule member
  cases member

theorem not_source_admitted : ¬ subject.HonestInput outside := by
  intro honest
  have bound := honest.1.1
  change indexLimit < indexLimit at bound
  exact Nat.lt_irrefl _ bound

end TestsSecurity.SourceAdmission.RangeDifference
