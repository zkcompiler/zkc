module

public import ZkcExamples.Structured.SumcheckContractBindings
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Fixed-table and omitted-terminal counterexamples. These are mathematical
controls for the contract connection, not native execution or provider tests. -/
namespace ZkcExamples.Structured.SumcheckContractControls
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open Zkc.Protocols.Sumcheck.Multilinear SumcheckContractBindings

abbrev F := ZMod 5

def originalTable : Table F 1 := fun _ => 0
def substitutedTable : Table F 1 := fun bits => if bits 0 then 0 else 1
def receivedResidual (challenge : F) : F := (1 - challenge) * 1 + challenge * 0

theorem wrong_fixed_table_changes_target :
    ¬ PublicTruth (G := F) ([0, 0] : List F) 1 ∧
      PublicTruth (G := F) ([1, 0] : List F) 1 := by
  rw [public_truth_iff _ _ (by decide), public_truth_iff _ _ (by decide)]
  decide

/-- The wrong table agrees with every forged residual, so it cannot stand in
for the original all-zero table in a terminal obligation. -/
theorem wrong_table_accepts_every_challenge (r : F) :
    extension 1 substitutedTable (fun _ => r) = receivedResidual r := by
  simp [extension, substitutedTable, receivedResidual]

theorem fixed_table_accepts_iff (r : F) :
    extension 1 originalTable (fun _ => r) = receivedResidual r ↔ r = 1 := by
  simp [extension, originalTable, receivedResidual]
  rw [eq_comm, sub_eq_zero, eq_comm]

/-- On five uniform challenges the right table accepts once; replacing it or
omitting the residual checks accepts all five. This is exact finite counting. -/
theorem fixed_table_acceptance_count :
    ((List.finRange 5).filter fun r =>
      decide (extension 1 originalTable (fun _ => (r.val : F)) = receivedResidual r.val)).length = 1 := by
  decide +kernel

theorem residual_omitted_cannot_close :
    ¬ TerminalObligation (fun _ : F => True) 0 1 originalTable
      (fun r => [r]) receivedResidual := by
  intro terminal
  obtain ⟨point, _, truth⟩ := terminal 0 trivial
  rw [residualClaim_complete_iff] at truth
  have impossible : (0 : F) = 1 := by
    simpa [extension, originalTable, receivedResidual] using truth
  exact (by decide : (0 : F) ≠ 1) impossible

/-- Independent existential table closure would make every scalar claim true.
The maintained source interpretation instead fixes the table parameter once. -/
theorem independent_table_is_vacuous (claim : F) : ∃ raw : List F, claim = raw.sum :=
  ⟨[claim], by simp⟩

end ZkcExamples.Structured.SumcheckContractControls
