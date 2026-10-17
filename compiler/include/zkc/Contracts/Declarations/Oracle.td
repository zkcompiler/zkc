// Logical contracts and curated exports owned by this domain.
def OpOracleCommitC : ZKC_Root<"C", CommitmentDomain>;
def OpOracleCommitValueField : ZKC_Project<OpOracleCommitC, CommitmentValueField>;
def OpOracleCommit : ZKC_Operation<"oracle.commit", [OpOracleCommitC, OpOracleCommitValueField],
    [ZKC_Apply<TypeVector, [OpOracleCommitValueField]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeCommitment, [OpOracleCommitC]>, ZKC_Apply<TypeOpeningState, [OpOracleCommitC]>], [ZKC_Holds<CapabilityVectorCommitment, [OpOracleCommitC]>]> {
  int ordinal = 109;
}

def OpOracleOpenC : ZKC_Root<"C", CommitmentDomain>;
def OpOracleOpenValueField : ZKC_Project<OpOracleOpenC, CommitmentValueField>;
def OpOracleOpen : ZKC_Operation<"oracle.open", [OpOracleOpenC, OpOracleOpenValueField],
    [ZKC_Apply<TypeOpeningState, [OpOracleOpenC]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [OpOracleOpenValueField]>, ZKC_Apply<TypeProof, [OpOracleOpenC]>], [ZKC_Holds<CapabilityVectorCommitment, [OpOracleOpenC]>]> {
  int ordinal = 110;
}

def OpOracleCheckC : ZKC_Root<"C", CommitmentDomain>;
def OpOracleCheckValueField : ZKC_Project<OpOracleCheckC, CommitmentValueField>;
def OpOracleCheck : ZKC_Operation<"oracle.check", [OpOracleCheckC, OpOracleCheckValueField],
    [ZKC_Apply<TypeCommitment, [OpOracleCheckC]>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeVector, [OpOracleCheckValueField]>, ZKC_Apply<TypeProof, [OpOracleCheckC]>],
    [ZKC_Apply<TypeBool, []>], [ZKC_Holds<CapabilityVectorCommitment, [OpOracleCheckC]>]> {
  int ordinal = 111;
}

def OpCommitmentsEmptyC : ZKC_Root<"C", CommitmentDomain>;
def OpCommitmentsEmptyValueField : ZKC_Project<OpCommitmentsEmptyC, CommitmentValueField>;
def OpCommitmentsEmpty : ZKC_Operation<"commitments.empty", [OpCommitmentsEmptyC, OpCommitmentsEmptyValueField],
    [],
    [ZKC_Apply<TypeCommitments, [OpCommitmentsEmptyC]>], [ZKC_Holds<CapabilityVectorCommitment, [OpCommitmentsEmptyC]>]> {
  int ordinal = 112;
}

def OpCommitmentsAppendC : ZKC_Root<"C", CommitmentDomain>;
def OpCommitmentsAppendValueField : ZKC_Project<OpCommitmentsAppendC, CommitmentValueField>;
def OpCommitmentsAppend : ZKC_Operation<"commitments.append", [OpCommitmentsAppendC, OpCommitmentsAppendValueField],
    [ZKC_Apply<TypeCommitments, [OpCommitmentsAppendC]>, ZKC_Apply<TypeCommitment, [OpCommitmentsAppendC]>],
    [ZKC_Apply<TypeCommitments, [OpCommitmentsAppendC]>], [ZKC_Holds<CapabilityVectorCommitment, [OpCommitmentsAppendC]>]> {
  int ordinal = 113;
}

def OpCommitmentsAtC : ZKC_Root<"C", CommitmentDomain>;
def OpCommitmentsAtValueField : ZKC_Project<OpCommitmentsAtC, CommitmentValueField>;
def OpCommitmentsAt : ZKC_Operation<"commitments.at", [OpCommitmentsAtC, OpCommitmentsAtValueField],
    [ZKC_Apply<TypeCommitments, [OpCommitmentsAtC]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeCommitment, [OpCommitmentsAtC]>], [ZKC_Holds<CapabilityVectorCommitment, [OpCommitmentsAtC]>]> {
  int ordinal = 114;
}

def OpCommitmentsLengthC : ZKC_Root<"C", CommitmentDomain>;
def OpCommitmentsLengthValueField : ZKC_Project<OpCommitmentsLengthC, CommitmentValueField>;
def OpCommitmentsLength : ZKC_Operation<"commitments.length", [OpCommitmentsLengthC, OpCommitmentsLengthValueField],
    [ZKC_Apply<TypeCommitments, [OpCommitmentsLengthC]>],
    [ZKC_Apply<TypeIndex, []>], [ZKC_Holds<CapabilityVectorCommitment, [OpCommitmentsLengthC]>]> {
  int ordinal = 115;
}

def OpOpeningStatesEmptyC : ZKC_Root<"C", CommitmentDomain>;
def OpOpeningStatesEmptyValueField : ZKC_Project<OpOpeningStatesEmptyC, CommitmentValueField>;
def OpOpeningStatesEmpty : ZKC_Operation<"opening_states.empty", [OpOpeningStatesEmptyC, OpOpeningStatesEmptyValueField],
    [],
    [ZKC_Apply<TypeOpeningStates, [OpOpeningStatesEmptyC]>], [ZKC_Holds<CapabilityVectorCommitment, [OpOpeningStatesEmptyC]>]> {
  int ordinal = 116;
}

def OpOpeningStatesAppendC : ZKC_Root<"C", CommitmentDomain>;
def OpOpeningStatesAppendValueField : ZKC_Project<OpOpeningStatesAppendC, CommitmentValueField>;
def OpOpeningStatesAppend : ZKC_Operation<"opening_states.append", [OpOpeningStatesAppendC, OpOpeningStatesAppendValueField],
    [ZKC_Apply<TypeOpeningStates, [OpOpeningStatesAppendC]>, ZKC_Apply<TypeOpeningState, [OpOpeningStatesAppendC]>],
    [ZKC_Apply<TypeOpeningStates, [OpOpeningStatesAppendC]>], [ZKC_Holds<CapabilityVectorCommitment, [OpOpeningStatesAppendC]>]> {
  int ordinal = 117;
}

def OpOpeningStatesAtC : ZKC_Root<"C", CommitmentDomain>;
def OpOpeningStatesAtValueField : ZKC_Project<OpOpeningStatesAtC, CommitmentValueField>;
def OpOpeningStatesAt : ZKC_Operation<"opening_states.at", [OpOpeningStatesAtC, OpOpeningStatesAtValueField],
    [ZKC_Apply<TypeOpeningStates, [OpOpeningStatesAtC]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeOpeningState, [OpOpeningStatesAtC]>], [ZKC_Holds<CapabilityVectorCommitment, [OpOpeningStatesAtC]>]> {
  int ordinal = 118;
}

def OpOpeningStatesLengthC : ZKC_Root<"C", CommitmentDomain>;
def OpOpeningStatesLengthValueField : ZKC_Project<OpOpeningStatesLengthC, CommitmentValueField>;
def OpOpeningStatesLength : ZKC_Operation<"opening_states.length", [OpOpeningStatesLengthC, OpOpeningStatesLengthValueField],
    [ZKC_Apply<TypeOpeningStates, [OpOpeningStatesLengthC]>],
    [ZKC_Apply<TypeIndex, []>], [ZKC_Holds<CapabilityVectorCommitment, [OpOpeningStatesLengthC]>]> {
  int ordinal = 119;
}

// One pruned authentication proof for several positions of one committed
// table; rows are concatenated in position order, duplicates included.
def OpOracleOpenManyC : ZKC_Root<"C", CommitmentDomain>;
def OpOracleOpenManyValueField : ZKC_Project<OpOracleOpenManyC, CommitmentValueField>;
def OpOracleOpenMany : ZKC_Operation<"oracle.open_many", [OpOracleOpenManyC, OpOracleOpenManyValueField],
    [ZKC_Apply<TypeOpeningState, [OpOracleOpenManyC]>, ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeVector, [OpOracleOpenManyValueField]>, ZKC_Apply<TypeProof, [OpOracleOpenManyC]>],
    [ZKC_Holds<CapabilityVectorCommitment, [OpOracleOpenManyC]>,
     ZKC_Holds<CapabilityMultiOpening, [OpOracleOpenManyC]>]> {
  int ordinal = 199;
}

def OpOracleCheckManyC : ZKC_Root<"C", CommitmentDomain>;
def OpOracleCheckManyValueField : ZKC_Project<OpOracleCheckManyC, CommitmentValueField>;
def OpOracleCheckMany : ZKC_Operation<"oracle.check_many", [OpOracleCheckManyC, OpOracleCheckManyValueField],
    [ZKC_Apply<TypeCommitment, [OpOracleCheckManyC]>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeVector, [OpOracleCheckManyValueField]>, ZKC_Apply<TypeProof, [OpOracleCheckManyC]>],
    [ZKC_Apply<TypeBool, []>],
    [ZKC_Holds<CapabilityVectorCommitment, [OpOracleCheckManyC]>,
     ZKC_Holds<CapabilityMultiOpening, [OpOracleCheckManyC]>]> {
  int ordinal = 200;
}
