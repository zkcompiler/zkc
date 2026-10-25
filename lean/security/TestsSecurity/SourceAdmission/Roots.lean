module

public import TestsSecurity.SourceAdmission.Migration
public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
public import ZkcSecurity.Examples.Generated.Components.TwoSumsABI
public import ZkcSecurity.Examples.Components.SmallSumcheckFormula
public import ZkcSecurity.Examples.Components.TwoSumsFormula

@[expose] public section
noncomputable section

/-! All-input migration against the historical registered policies of the two
actual roots. These controls intentionally require regenerated source clauses
and generated ABIs; old exports cannot satisfy the clause inventory checks. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace TestsSecurity.SourceAdmission.Roots
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair
open HistoricalPolicy (InputPolicy InputRule)

private theorem one_representable : (1 : Nat) < indexLimit := by decide +kernel

namespace SmallSumcheck
open ZkcSecurity.Examples.Generated.SmallSumcheck
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI

/-- Exactly the former registered rule order, selectors, width and maximum. -/
def historicalPolicy : InputPolicy subject.target.owner.protocol.inputs :=
  ⟨[.cubeTable .here (.there (.there .here)) 1,
    .boundedIndex (.there (.there .here)) 2]⟩

example : (subject.target.owner.contract.clauses.filter (·.kind == .input)).map (·.name) =
    ["shape"] := by decide +kernel

theorem all_inputs (values : subject.Inputs) :
    HistoricalPolicy.HonestInput subject historicalPolicy values ↔ subject.HonestInput values := by
  apply HistoricalPolicy.honestInput_iff subject historicalPolicy abi
  intro packed
  apply Iff.trans ?_ (abi.honest_pack_iff packed)
  obtain ⟨raw, claim, rounds, service, rfl⟩ := data_surjective packed
  change historicalPolicy.Holds (inputs raw claim rounds service) ↔
    subject.HonestInput (inputs raw claim rounds service)
  rw [honestInput_iff]
  change historicalPolicy.Holds (sourceInputs (some raw) (some claim) (some rounds) service) ↔ _
  simp [historicalPolicy, HistoricalPolicy.InputPolicy.Holds, HistoricalPolicy.InputRule.Holds,
    sourceInputs, one_representable, and_assoc]
  tauto

theorem nonvacuous : Nonvacuous subject :=
  ZkcSecurity.Examples.Components.SmallSumcheck.Formula.nonvacuous

example : subject.target.clauseIndex.val = 1 := by decide +kernel

/-- Input admission does not assume the retained target is true. -/
example : subject.HonestInput (inputs [0] 1 0 none) := by
  rw [honestInput_iff]
  decide +kernel

example : ¬ subject.HonestInput (inputs [] 0 0 none) := by
  rw [honestInput_iff]
  decide +kernel
end SmallSumcheck

namespace TwoSums
open ZkcSecurity.Examples.Generated.TwoSums
open ZkcSecurity.Examples.Generated.Components.TwoSumsABI

def historicalPolicy : InputPolicy subject.target.owner.protocol.inputs :=
  ⟨[.cubeTable .here (.there (.there (.there (.there .here)))) 1,
    .cubeTable (.there .here) (.there (.there (.there (.there .here)))) 1,
    .boundedIndex (.there (.there (.there (.there .here)))) 4]⟩

example : (subject.target.owner.contract.clauses.filter (·.kind == .input)).map (·.name) =
    ["left_shape", "right_shape"] := by decide +kernel

theorem all_inputs (values : subject.Inputs) :
    HistoricalPolicy.HonestInput subject historicalPolicy values ↔ subject.HonestInput values := by
  apply HistoricalPolicy.honestInput_iff subject historicalPolicy abi
  intro packed
  apply Iff.trans ?_ (abi.honest_pack_iff packed)
  obtain ⟨left, right, leftClaim, rightClaim, rounds, service, rfl⟩ := data_surjective packed
  change historicalPolicy.Holds (inputs left right leftClaim rightClaim rounds service) ↔
    subject.HonestInput (inputs left right leftClaim rightClaim rounds service)
  rw [honestInput_iff]
  change historicalPolicy.Holds
    (sourceInputs (some left) (some right) (some leftClaim) (some rightClaim) (some rounds) service) ↔ _
  simp [historicalPolicy, HistoricalPolicy.InputPolicy.Holds, HistoricalPolicy.InputRule.Holds,
    sourceInputs, one_representable, and_assoc]
  tauto

theorem nonvacuous : Nonvacuous subject :=
  ZkcSecurity.Examples.Components.TwoSums.Formula.nonvacuous

example : subject.target.clauseIndex.val = 2 := by decide +kernel

example : subject.HonestInput (inputs [0] [0] 0 1 0 none) := by
  rw [honestInput_iff]
  decide +kernel

example : ¬ subject.HonestInput (inputs [0] [] 0 0 0 none) := by
  rw [honestInput_iff]
  decide +kernel
end TwoSums

#print axioms SmallSumcheck.all_inputs
#print axioms TwoSums.all_inputs
#print axioms SmallSumcheck.nonvacuous
#print axioms TwoSums.nonvacuous
end TestsSecurity.SourceAdmission.Roots
