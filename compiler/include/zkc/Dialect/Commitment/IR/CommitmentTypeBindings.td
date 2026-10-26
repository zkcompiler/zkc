// Native binding decisions owned by Commitment.
include "zkc/Dialect/TypeBindings.td"
def CommitmentTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "commitmentAdapters">;
def CommitmentNativeBinding : ZKC_CustomBinding<TypeCommitment, ["::zkc::commitment::PolynomialObjectType", "::zkc::commitment::VectorObjectType"], "decodeObject<true, true>", "encodeObject<true, true>", CommitmentTypeAdapters>;
def ProofNativeBinding : ZKC_CustomBinding<TypeProof, ["::zkc::commitment::PolynomialObjectType", "::zkc::commitment::VectorObjectType"], "decodeObject<true, true>", "encodeObject<true, true>", CommitmentTypeAdapters>;
def OpeningStateNativeBinding : ZKC_CustomBinding<TypeOpeningState, ["::zkc::commitment::PolynomialObjectType", "::zkc::commitment::VectorObjectType"], "decodeObject<true, true>", "encodeObject<true, true>", CommitmentTypeAdapters>;
def ProverKeyNativeBinding : ZKC_CustomBinding<TypeProverKey, ["::zkc::commitment::PolynomialObjectType"], "decodeObject<true, false>", "encodeObject<true, false>", CommitmentTypeAdapters>;
def VerifierKeyNativeBinding : ZKC_CustomBinding<TypeVerifierKey, ["::zkc::commitment::PolynomialObjectType"], "decodeObject<true, false>", "encodeObject<true, false>", CommitmentTypeAdapters>;
def CommitmentsNativeBinding : ZKC_CustomBinding<TypeCommitments, ["::zkc::commitment::VectorObjectType"], "decodeObject<false, true>", "encodeObject<false, true>", CommitmentTypeAdapters>;
def OpeningStatesNativeBinding : ZKC_CustomBinding<TypeOpeningStates, ["::zkc::commitment::VectorObjectType"], "decodeObject<false, true>", "encodeObject<false, true>", CommitmentTypeAdapters>;
