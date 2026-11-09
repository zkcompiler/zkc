import Zkc.Protocol.Library.Transformations.Commitment.BatchCompleteness
import Zkc.Tests.Verification.BatchVerification
import Zkc.Tools.Program.DeclarationAudit

/-! The witness is built from the tree's actual node answers, not obtained
from verifier acceptance. Duplicate and unordered requests share this witness. -/
set_option autoImplicit false
namespace TestsSecurity.BatchCompleteness
open OracleComp OracleSpec ZkcSecurity.Commitment
open ZkcSecurity.Commitment.BatchOpening ZkcSecurity.Commitment.BatchVerification
open TestsSecurity.BatchVerification

def table : ℕ → List ℕ
  | 0 => row0
  | 1 => row1
  | _ => row2

def nodes : HashLog Query ℕ :=
  [⟨.inr (10, 20), 40⟩, ⟨.inr (30, 0), 50⟩, ⟨.inr (40, 50), 60⟩]

private theorem consistent : ∀ entry ∈ nodes, answer entry.1 = entry.2 := by
  decide

private theorem tree : Reduction model nodes 2 [(0, 10), (1, 20), (2, 30)] [0] 60 := by
  refine .step (.shared (p := 0) (up := 40) ?_ ?_
    (.left (p := 1) (right := 0) (up := 50) ?_ ?_ (.nil []))) ?_
  · decide
  · decide
  · simp
  · decide
  · exact .step (.shared (p := 0) (up := 60) (by simp) (by decide) (.nil [])) (.root 60)

theorem unordered_duplicates_complete :
    evalWithAnswerFn (QueryImpl.ofFn answer)
      (verify model validRow (2 ^ 64 - 1) 128 2 3 requests (requests.map table)
        (.decoded 60 [0])) = .returned true := by
  apply verify_table_complete model validRow answer (2 ^ 64 - 1) 128 2 3 requests table
    60 [0] nodes (by decide) (by decide) (by decide) (by decide) (by decide) consistent
  exact tree

theorem distinct_queries_reuse_tree :
    evalWithAnswerFn (QueryImpl.ofFn answer)
      (verify model validRow (2 ^ 64 - 1) 128 2 3 [0, 1, 2] ([0, 1, 2].map table)
        (.decoded 60 [0])) = .returned true := by
  apply verify_table_complete model validRow answer (2 ^ 64 - 1) 128 2 3 [0, 1, 2] table
    60 [0] nodes (by decide) (by decide) (by decide) (by decide) (by decide) consistent
  exact tree

theorem repeated_requests_preserve_representatives :
    select (requests.map fun index ↦ (index, table index)) (unique requests) =
      some [(0, row0), (1, row1), (2, row2)] :=
  select_table table requests (unique requests) (fun _ member ↦ unique_mem.mp member)

/-- This tests a theorem premise, not a verifier outcome. -/
theorem inconsistent_log_fails_consistency :
    ¬ (∀ entry ∈ ((⟨.inr (40, 50), 61⟩ : (_ : Query) × ℕ) :: nodes),
      answer entry.1 = entry.2) := by decide

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Protocol.Library.Transformations.Commitment.BatchCompleteness]
    "BATCH-COMPLETENESS-AXIOMS-PASS"
  ZkcTools.DeclarationAudit.checkCurrent "BATCH-COMPLETENESS-CONTROLS-AXIOMS-PASS"
end TestsSecurity.BatchCompleteness
