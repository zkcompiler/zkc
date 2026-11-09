import Zkc.Protocol.Library.Transformations.Commitment.BatchCheckpoint
import Zkc.Tests.Verification.BatchVerification
import Zkc.Tools.Program.DeclarationAudit

/-! Reuse the operational fixture, including duplicate and unordered requests.
The negative case exposes the same valid batch before its table is fixed. -/

set_option autoImplicit false
namespace TestsSecurity.BatchCheckpoint
open OracleComp OracleSpec ZkcSecurity.Commitment
open ZkcSecurity.Commitment.BatchVerification
open TestsSecurity.BatchVerification

def table : JointTable (fun _ : Unit ↦ Bool) ℕ ℕ Query
  | .inl _ => false
  | .inr query => answer query

def key : TranscriptKey Unit ℕ ℕ := ([.root 2 60], ())
def calls : List (JointKey Unit ℕ ℕ Query) :=
  [.inr (.inl row0), .inr (.inl row1), .inr (.inl row2),
    .inr (.inr (10, 20)), .inr (.inr (30, 0)), .inr (.inr (40, 50))]
def keys := calls ++ [.inl key] ++ calls

private theorem local_record_included :
    ∀ entry ∈ history 3 requests replies (.decoded 60 [0]), entry ∈ hashLog table keys := by
  rw [exact_history]
  simp [keys, calls, hashLog, table, answer, row0, row1, row2]

private theorem good : GoodFrom model.scheme 1 table [] keys := by
  simp [GoodFrom, keys, calls, table, targets, keyTargets, keyRoots, key,
    LeafHashing.scheme, LeafHashing.inputs, model, answer, row0, row1, row2]
  decide

theorem operational_batch_at_checkpoint :
    requests.map (model.extract (hashLog table (beforeFirstKey (.inl key) keys)) 2 60) =
      replies.map some := by
  exact verify_agrees_at_checkpoint model validRow (2 ^ 64 - 1) 128 2 3 1
    requests replies 60 [0] table keys key (by simp [keys])
    (by decide) good local_record_included unsorted_duplicates_accept

theorem repeated_challenge_keeps_checkpoint :
    beforeFirstKey (.inl key) (keys ++ [.inl key]) = beforeFirstKey (.inl key) keys := by
  decide

theorem early_challenge_has_no_extracted_rows :
    requests.map (model.extract
      (hashLog table (beforeFirstKey (.inl key) (.inl key :: calls))) 2 60) =
        [none, none, none, none] := by decide

theorem acceptance_alone_does_not_fix_checkpoint :
    requests.map (model.extract
      (hashLog table (beforeFirstKey (.inl key) (.inl key :: calls))) 2 60) ≠
        replies.map some := by decide

theorem early_challenge_is_not_good : ¬ GoodFrom model.scheme 1 table [] (.inl key :: calls) := by
  simp [GoodFrom, calls, table, targets, keyTargets, keyRoots, key,
    LeafHashing.scheme, LeafHashing.inputs, Absorbed.committed, model, answer, row0, row1, row2]
  decide

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Protocol.Library.Transformations.Commitment.BatchCheckpoint]
    "BATCH-CHECKPOINT-AXIOMS-PASS"
  ZkcTools.DeclarationAudit.checkCurrent "BATCH-CHECKPOINT-CONTROLS-AXIOMS-PASS"

end TestsSecurity.BatchCheckpoint
