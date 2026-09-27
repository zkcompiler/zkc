// Logical contracts and curated exports owned by this domain.
def OpTranscriptDrawIndexT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptDrawIndexChallengeField : ZKC_Project<OpTranscriptDrawIndexT, TranscriptChallengeField>;
def OpTranscriptDrawIndex : ZKC_Operation<"transcript.draw_index", [OpTranscriptDrawIndexT, OpTranscriptDrawIndexChallengeField],
    [ZKC_Apply<TypeTranscript, [OpTranscriptDrawIndexT]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeTranscript, [OpTranscriptDrawIndexT]>], [ZKC_Holds<CapabilityIndexTranscript, [OpTranscriptDrawIndexT]>]> {
  int ordinal = 124;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Sampling<TranscriptProvider, IndexSample, 1>, ZKC_History<0, 1>];
}

def OpTranscriptChallengeT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptChallengeChallengeField : ZKC_Project<OpTranscriptChallengeT, TranscriptChallengeField>;
def OpTranscriptChallenge : ZKC_Operation<"transcript.challenge", [OpTranscriptChallengeT, OpTranscriptChallengeChallengeField],
    [ZKC_Apply<TypeTranscript, [OpTranscriptChallengeT]>],
    [ZKC_Apply<TypeField, [OpTranscriptChallengeChallengeField]>, ZKC_Apply<TypeTranscript, [OpTranscriptChallengeT]>], [ZKC_Holds<CapabilityFieldTranscript, [OpTranscriptChallengeT]>]> {
  int ordinal = 138;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Sampling<TranscriptProvider, FieldSample, -1>, ZKC_History<0, 1>];
}

def OpTranscriptObserveBoolT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObserveBoolE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObserveBool : ZKC_Operation<"transcript.observe.bool", [OpTranscriptObserveBoolT, OpTranscriptObserveBoolE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveBoolT]>, ZKC_Apply<TypeBool, []>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveBoolT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObserveBoolT]>, ZKC_Holds<CapabilityEncodesBool, [OpTranscriptObserveBoolE]>]> {
  int ordinal = 139;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

def OpTranscriptObserveFieldT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObserveFieldF : ZKC_Root<"F", FieldDomain>;
def OpTranscriptObserveFieldE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObserveField : ZKC_Operation<"transcript.observe.field", [OpTranscriptObserveFieldT, OpTranscriptObserveFieldF, OpTranscriptObserveFieldE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveFieldT]>, ZKC_Apply<TypeField, [OpTranscriptObserveFieldF]>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveFieldT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObserveFieldT]>, ZKC_Holds<CapabilityEncodesField, [OpTranscriptObserveFieldE, OpTranscriptObserveFieldF]>]> {
  int ordinal = 140;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

def OpTranscriptObserveTableT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObserveTableF : ZKC_Root<"F", FieldDomain>;
def OpTranscriptObserveTableE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObserveTable : ZKC_Operation<"transcript.observe.table", [OpTranscriptObserveTableT, OpTranscriptObserveTableF, OpTranscriptObserveTableE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveTableT]>, ZKC_Apply<TypeTable, [OpTranscriptObserveTableF]>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveTableT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObserveTableT]>, ZKC_Holds<CapabilityEncodesTable, [OpTranscriptObserveTableE, OpTranscriptObserveTableF]>]> {
  int ordinal = 141;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

def OpTranscriptObservePointT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObservePointF : ZKC_Root<"F", FieldDomain>;
def OpTranscriptObservePointE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObservePoint : ZKC_Operation<"transcript.observe.point", [OpTranscriptObservePointT, OpTranscriptObservePointF, OpTranscriptObservePointE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObservePointT]>, ZKC_Apply<TypePoint, [OpTranscriptObservePointF]>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObservePointT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObservePointT]>, ZKC_Holds<CapabilityEncodesPoint, [OpTranscriptObservePointE, OpTranscriptObservePointF]>]> {
  int ordinal = 142;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

def OpTranscriptObserveRoundT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObserveRoundF : ZKC_Root<"F", FieldDomain>;
def OpTranscriptObserveRoundE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObserveRound : ZKC_Operation<"transcript.observe.round", [OpTranscriptObserveRoundT, OpTranscriptObserveRoundF, OpTranscriptObserveRoundE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveRoundT]>, ZKC_Apply<TypeRound, [OpTranscriptObserveRoundF]>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveRoundT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObserveRoundT]>, ZKC_Holds<CapabilityEncodesRound, [OpTranscriptObserveRoundE, OpTranscriptObserveRoundF]>]> {
  int ordinal = 143;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

def OpTranscriptObserveCommitmentT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObserveCommitmentC : ZKC_Root<"C", CommitmentDomain>;
def OpTranscriptObserveCommitmentE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObserveCommitment : ZKC_Operation<"transcript.observe.commitment", [OpTranscriptObserveCommitmentT, OpTranscriptObserveCommitmentC, OpTranscriptObserveCommitmentE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveCommitmentT]>, ZKC_Apply<TypeCommitment, [OpTranscriptObserveCommitmentC]>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveCommitmentT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObserveCommitmentT]>, ZKC_Holds<CapabilityEncodesCommitment, [OpTranscriptObserveCommitmentE, OpTranscriptObserveCommitmentC]>]> {
  int ordinal = 144;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

def OpTranscriptObserveProofT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObserveProofC : ZKC_Root<"C", CommitmentDomain>;
def OpTranscriptObserveProofE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObserveProof : ZKC_Operation<"transcript.observe.proof", [OpTranscriptObserveProofT, OpTranscriptObserveProofC, OpTranscriptObserveProofE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveProofT]>, ZKC_Apply<TypeProof, [OpTranscriptObserveProofC]>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveProofT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObserveProofT]>, ZKC_Holds<CapabilityEncodesProof, [OpTranscriptObserveProofE, OpTranscriptObserveProofC]>]> {
  int ordinal = 145;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

def OpTranscriptObserveGroupT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObserveGroupG : ZKC_Root<"G", GroupDomain>;
def OpTranscriptObserveGroupE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObserveGroup : ZKC_Operation<"transcript.observe.group", [OpTranscriptObserveGroupT, OpTranscriptObserveGroupG, OpTranscriptObserveGroupE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveGroupT]>, ZKC_Apply<TypeGroup, [OpTranscriptObserveGroupG]>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveGroupT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObserveGroupT]>, ZKC_Holds<CapabilityEncodesGroup, [OpTranscriptObserveGroupE, OpTranscriptObserveGroupG]>]> {
  int ordinal = 146;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

def OpTranscriptObserveGroupsT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObserveGroupsG : ZKC_Root<"G", GroupDomain>;
def OpTranscriptObserveGroupsE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObserveGroups : ZKC_Operation<"transcript.observe.groups", [OpTranscriptObserveGroupsT, OpTranscriptObserveGroupsG, OpTranscriptObserveGroupsE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveGroupsT]>, ZKC_Apply<TypeGroups, [OpTranscriptObserveGroupsG]>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveGroupsT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObserveGroupsT]>, ZKC_Holds<CapabilityEncodesGroups, [OpTranscriptObserveGroupsE, OpTranscriptObserveGroupsG]>]> {
  int ordinal = 147;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

def OpTranscriptObserveMatrixT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObserveMatrixF : ZKC_Root<"F", FieldDomain>;
def OpTranscriptObserveMatrixE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObserveMatrix : ZKC_Operation<"transcript.observe.matrix", [OpTranscriptObserveMatrixT, OpTranscriptObserveMatrixF, OpTranscriptObserveMatrixE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveMatrixT]>, ZKC_Apply<TypeMatrix, [OpTranscriptObserveMatrixF]>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveMatrixT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObserveMatrixT]>, ZKC_Holds<CapabilityEncodesMatrix, [OpTranscriptObserveMatrixE, OpTranscriptObserveMatrixF]>]> {
  int ordinal = 148;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

def OpTranscriptObserveVectorT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObserveVectorF : ZKC_Root<"F", FieldDomain>;
def OpTranscriptObserveVectorE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObserveVector : ZKC_Operation<"transcript.observe.vector", [OpTranscriptObserveVectorT, OpTranscriptObserveVectorF, OpTranscriptObserveVectorE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveVectorT]>, ZKC_Apply<TypeVector, [OpTranscriptObserveVectorF]>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveVectorT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObserveVectorT]>, ZKC_Holds<CapabilityEncodesVector, [OpTranscriptObserveVectorE, OpTranscriptObserveVectorF]>]> {
  int ordinal = 149;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

def OpTranscriptObservePolynomialT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObservePolynomialF : ZKC_Root<"F", FieldDomain>;
def OpTranscriptObservePolynomialE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObservePolynomial : ZKC_Operation<"transcript.observe.polynomial", [OpTranscriptObservePolynomialT, OpTranscriptObservePolynomialF, OpTranscriptObservePolynomialE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObservePolynomialT]>, ZKC_Apply<TypePolynomial, [OpTranscriptObservePolynomialF]>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObservePolynomialT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObservePolynomialT]>, ZKC_Holds<CapabilityEncodesPolynomial, [OpTranscriptObservePolynomialE, OpTranscriptObservePolynomialF]>]> {
  int ordinal = 150;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

def OpTranscriptObserveIndexT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObserveIndexE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObserveIndex : ZKC_Operation<"transcript.observe.index", [OpTranscriptObserveIndexT, OpTranscriptObserveIndexE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveIndexT]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveIndexT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObserveIndexT]>, ZKC_Holds<CapabilityEncodesIndex, [OpTranscriptObserveIndexE]>]> {
  int ordinal = 151;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

def OpTranscriptObserveIndicesT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObserveIndicesE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObserveIndices : ZKC_Operation<"transcript.observe.indices", [OpTranscriptObserveIndicesT, OpTranscriptObserveIndicesE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveIndicesT]>, ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveIndicesT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObserveIndicesT]>, ZKC_Holds<CapabilityEncodesIndices, [OpTranscriptObserveIndicesE]>]> {
  int ordinal = 152;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

def OpTranscriptObserveCommitmentsT : ZKC_Root<"T", TranscriptDomain>;
def OpTranscriptObserveCommitmentsC : ZKC_Root<"C", CommitmentDomain>;
def OpTranscriptObserveCommitmentsE : ZKC_Root<"E", CodecDomain>;
def OpTranscriptObserveCommitments : ZKC_Operation<"transcript.observe.commitments", [OpTranscriptObserveCommitmentsT, OpTranscriptObserveCommitmentsC, OpTranscriptObserveCommitmentsE],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveCommitmentsT]>, ZKC_Apply<TypeCommitments, [OpTranscriptObserveCommitmentsC]>],
    [ZKC_Apply<TypeTranscript, [OpTranscriptObserveCommitmentsT]>], [ZKC_Holds<CapabilityTranscript, [OpTranscriptObserveCommitmentsT]>, ZKC_Holds<CapabilityEncodesCommitments, [OpTranscriptObserveCommitmentsE, OpTranscriptObserveCommitmentsC]>]> {
  int ordinal = 153;
  let stage = Construction;
  let parameters = TranscriptOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}
