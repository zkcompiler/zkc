// Native binding decisions owned by Commitment.
include "zkc/Dialect/TypeBindings.td"
def CommitmentTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "commitmentAdapters">;
def CommitmentNativeBinding : ZKC_CustomBinding<CatalogType_commitment, ["::zkc::commitment::PolynomialObjectType", "::zkc::commitment::VectorObjectType"], "decodeObject<true, true>", "encodeObject<true, true>", "objectArguments<true, true>", CommitmentTypeAdapters>;
def ProofNativeBinding : ZKC_CustomBinding<CatalogType_proof, ["::zkc::commitment::PolynomialObjectType", "::zkc::commitment::VectorObjectType"], "decodeObject<true, true>", "encodeObject<true, true>", "objectArguments<true, true>", CommitmentTypeAdapters>;
def OpeningStateNativeBinding : ZKC_CustomBinding<CatalogType_opening_5fstate, ["::zkc::commitment::PolynomialObjectType", "::zkc::commitment::VectorObjectType"], "decodeObject<true, true>", "encodeObject<true, true>", "objectArguments<true, true>", CommitmentTypeAdapters>;
def ProverKeyNativeBinding : ZKC_CustomBinding<CatalogType_prover_5fkey, ["::zkc::commitment::PolynomialObjectType"], "decodeObject<true, false>", "encodeObject<true, false>", "objectArguments<true, false>", CommitmentTypeAdapters>;
def VerifierKeyNativeBinding : ZKC_CustomBinding<CatalogType_verifier_5fkey, ["::zkc::commitment::PolynomialObjectType"], "decodeObject<true, false>", "encodeObject<true, false>", "objectArguments<true, false>", CommitmentTypeAdapters>;
def CommitmentsNativeBinding : ZKC_CustomBinding<CatalogType_commitments, ["::zkc::commitment::VectorObjectType"], "decodeObject<false, true>", "encodeObject<false, true>", "objectArguments<false, true>", CommitmentTypeAdapters>;
def OpeningStatesNativeBinding : ZKC_CustomBinding<CatalogType_opening_5fstates, ["::zkc::commitment::VectorObjectType"], "decodeObject<false, true>", "encodeObject<false, true>", "objectArguments<false, true>", CommitmentTypeAdapters>;
