// Logical contracts and curated exports owned by this domain.
def OpPcsCommitC : ZKC_Root<"C", CommitmentDomain>;
def OpPcsCommitValueField : ZKC_Project<OpPcsCommitC, CommitmentValueField>;
def OpPcsCommitEvaluationField : ZKC_Project<OpPcsCommitC, CommitmentEvaluationField>;
def OpPcsCommitPointField : ZKC_Project<OpPcsCommitC, CommitmentPointField>;
def OpPcsCommit : ZKC_Operation<"pcs.commit", [OpPcsCommitC, OpPcsCommitValueField, OpPcsCommitEvaluationField, OpPcsCommitPointField],
    [ZKC_Apply<TypeProverKey, [OpPcsCommitC]>, ZKC_Apply<TypeTable, [OpPcsCommitValueField]>],
    [ZKC_Apply<TypeCommitment, [OpPcsCommitC]>, ZKC_Apply<TypeOpeningState, [OpPcsCommitC]>], [ZKC_Holds<CapabilityMultilinearOpening, [OpPcsCommitC]>]> {
  int ordinal = 120;
}
def ExportPcsCommit : ZKC_OperationExport<"zkc::pcs", "commit",
    OpPcsCommit, ["prover_key", "table"]>;

def OpPcsOpenC : ZKC_Root<"C", CommitmentDomain>;
def OpPcsOpenValueField : ZKC_Project<OpPcsOpenC, CommitmentValueField>;
def OpPcsOpenEvaluationField : ZKC_Project<OpPcsOpenC, CommitmentEvaluationField>;
def OpPcsOpenPointField : ZKC_Project<OpPcsOpenC, CommitmentPointField>;
def OpPcsOpen : ZKC_Operation<"pcs.open", [OpPcsOpenC, OpPcsOpenValueField, OpPcsOpenEvaluationField, OpPcsOpenPointField],
    [ZKC_Apply<TypeOpeningState, [OpPcsOpenC]>, ZKC_Apply<TypePoint, [OpPcsOpenPointField]>],
    [ZKC_Apply<TypeField, [OpPcsOpenEvaluationField]>, ZKC_Apply<TypeProof, [OpPcsOpenC]>], [ZKC_Holds<CapabilityMultilinearOpening, [OpPcsOpenC]>]> {
  int ordinal = 121;
}
def ExportPcsOpen : ZKC_OperationExport<"zkc::pcs", "open",
    OpPcsOpen, ["opening_state", "point"]>;

def OpPcsCheckC : ZKC_Root<"C", CommitmentDomain>;
def OpPcsCheckValueField : ZKC_Project<OpPcsCheckC, CommitmentValueField>;
def OpPcsCheckEvaluationField : ZKC_Project<OpPcsCheckC, CommitmentEvaluationField>;
def OpPcsCheckPointField : ZKC_Project<OpPcsCheckC, CommitmentPointField>;
def OpPcsCheck : ZKC_Operation<"pcs.check", [OpPcsCheckC, OpPcsCheckValueField, OpPcsCheckEvaluationField, OpPcsCheckPointField],
    [ZKC_Apply<TypeVerifierKey, [OpPcsCheckC]>, ZKC_Apply<TypeCommitment, [OpPcsCheckC]>, ZKC_Apply<TypePoint, [OpPcsCheckPointField]>, ZKC_Apply<TypeField, [OpPcsCheckEvaluationField]>, ZKC_Apply<TypeProof, [OpPcsCheckC]>],
    [ZKC_Apply<TypeBool, []>], [ZKC_Holds<CapabilityMultilinearOpening, [OpPcsCheckC]>]> {
  int ordinal = 122;
}
def ExportPcsCheck : ZKC_OperationExport<"zkc::pcs", "check",
    OpPcsCheck, ["verifier_key", "commitment", "point", "field", "proof"]>;

def OpPcsEqualC : ZKC_Root<"C", CommitmentDomain>;
def OpPcsEqualValueField : ZKC_Project<OpPcsEqualC, CommitmentValueField>;
def OpPcsEqualEvaluationField : ZKC_Project<OpPcsEqualC, CommitmentEvaluationField>;
def OpPcsEqualPointField : ZKC_Project<OpPcsEqualC, CommitmentPointField>;
def OpPcsEqual : ZKC_Operation<"pcs.equal", [OpPcsEqualC, OpPcsEqualValueField, OpPcsEqualEvaluationField, OpPcsEqualPointField],
    [ZKC_Apply<TypeCommitment, [OpPcsEqualC]>, ZKC_Apply<TypeCommitment, [OpPcsEqualC]>],
    [ZKC_Apply<TypeBool, []>], [ZKC_Holds<CapabilityMultilinearOpening, [OpPcsEqualC]>]> {
  int ordinal = 126;
  let facets = [PublicReplay];
}
def ExportPcsEqual : ZKC_OperationExport<"zkc::pcs", "equal",
    OpPcsEqual, ["commitment0", "commitment1"]>;
