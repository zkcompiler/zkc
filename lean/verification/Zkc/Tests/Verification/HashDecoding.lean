import Zkc.Protocol.Library.Transformations.Commitment.BatchOpening
import Zkc.Tests.Verification.BatchVerification
import Zkc.Tools.Program.DeclarationAudit

/-! A cross-role alias is harmless for role-specific extraction. These finite
controls concern record decoding, not the security of any hash provider. -/
set_option autoImplicit false
namespace TestsSecurity.HashDecoding
open OracleComp OracleSpec ZkcSecurity.Commitment
open ZkcSecurity.Commitment.BatchOpening TestsSecurity.BatchVerification

def log : HashLog Query ℕ :=
  [⟨.inl row0, 10⟩, ⟨.inl row1, 20⟩, ⟨.inr (10, 20), 40⟩, ⟨.inr (99, 0), 10⟩]

theorem node_role_consistent : DecoderConsistent model.children log := by
  simp [DecoderConsistent, log, model]

theorem leaf_role_consistent : DecoderConsistent model.leafRow log := by
  simp [DecoderConsistent, log, model]

theorem cross_role_alias_is_not_global_injectivity :
    ¬ MerkleTreeExtractor.ResponseInjectiveOn log := by
  intro injective
  have same := injective ⟨.inl row0, 10⟩ (by simp [log])
    ⟨.inr (99, 0), 10⟩ (by simp [log]) rfl
  cases same

private theorem tree : Reduction model log 1 [(0, 10), (1, 20)] [] 40 :=
  .step (.shared (p := 0) (up := 40) (by simp) (by simp [log, model]) (.nil [])) (.root 40)

private theorem rows : RowsRecorded model log [(0, 10), (1, 20)] [1, 0, 1]
    [row1, row0, row1] := by
  simp [RowsRecorded, log, model]

theorem exact_ordered_batch_despite_alias :
    [1, 0, 1].map (model.extract log 1 40) = [some row1, some row0, some row1] :=
  batch_agrees_of_decoderConsistent tree rows node_role_consistent leaf_role_consistent

theorem conflicting_nodes_fail_consistency :
    ¬ DecoderConsistent model.children ((⟨.inr (0, 1), 40⟩ : (_ : Query) × ℕ) :: log) := by
  simp [DecoderConsistent, log, model]

theorem conflicting_leaves_fail_consistency :
    ¬ DecoderConsistent model.leafRow ((⟨.inl row1, 10⟩ : (_ : Query) × ℕ) :: log) := by
  simp [DecoderConsistent, log, model, row0, row1]

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Protocol.Library.Transformations.Commitment.HashDecoding, `Zkc.Protocol.Library.Transformations.Commitment.HashedLeaves, `Zkc.Protocol.Library.Transformations.Commitment.BatchOpening]
    "HASH-DECODING-AXIOMS-PASS"
  ZkcTools.DeclarationAudit.checkCurrent "HASH-DECODING-CONTROLS-AXIOMS-PASS"
end TestsSecurity.HashDecoding
