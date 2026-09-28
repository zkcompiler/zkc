// Existing nominal parameter vocabulary. Formation remains in C++ admission.
def FieldSort : ZKC_Sort<"Field">;
def FieldDomain : ZKC_Domain<FieldSort>;
def GroupSort : ZKC_Sort<"Group">;
def GroupDomain : ZKC_Domain<GroupSort>;
def CommitmentSort : ZKC_Sort<"Commitment">;
def CommitmentDomain : ZKC_Domain<CommitmentSort>;
def TranscriptSort : ZKC_Sort<"Transcript">;
def TranscriptDomain : ZKC_Domain<TranscriptSort>;
def CodecSort : ZKC_Sort<"Codec">;
def CodecDomain : ZKC_Domain<CodecSort>;
def FieldPairingG1 : ZKC_Member<"PairingG1", FieldDomain, GroupDomain>;
def FieldPairingG2 : ZKC_Member<"PairingG2", FieldDomain, GroupDomain>;
def FieldBaseField : ZKC_Member<"BaseField", FieldDomain, FieldDomain>;
def GroupScalar : ZKC_Member<"Scalar", GroupDomain, FieldDomain>;
def CommitmentValueField : ZKC_Member<"ValueField", CommitmentDomain, FieldDomain>;
def CommitmentPointField : ZKC_Member<"PointField", CommitmentDomain, FieldDomain>;
def CommitmentEvaluationField : ZKC_Member<"EvaluationField", CommitmentDomain, FieldDomain>;
def TranscriptChallengeField : ZKC_Member<"ChallengeField", TranscriptDomain, FieldDomain>;
def CapabilityCharacteristicNotTwo : ZKC_Capability<"CharacteristicNotTwo", [FieldDomain]>;
def CapabilityCommRing : ZKC_Capability<"CommRing", [FieldDomain]>;
def CapabilityEncodesBool : ZKC_Capability<"Encodes.bool", [CodecDomain]>;
def CapabilityEncodesCommitment : ZKC_Capability<"Encodes.commitment", [CodecDomain, CommitmentDomain]>;
def CapabilityEncodesCommitments : ZKC_Capability<"Encodes.commitments", [CodecDomain, CommitmentDomain]>;
def CapabilityEncodesField : ZKC_Capability<"Encodes.field", [CodecDomain, FieldDomain]>;
def CapabilityEncodesNonzeroField : ZKC_Capability<"Encodes.nonzero_field", [CodecDomain, FieldDomain]>;
def CapabilityEncodesGroup : ZKC_Capability<"Encodes.group", [CodecDomain, GroupDomain]>;
def CapabilityEncodesGroups : ZKC_Capability<"Encodes.groups", [CodecDomain, GroupDomain]>;
def CapabilityEncodesIndex : ZKC_Capability<"Encodes.index", [CodecDomain]>;
def CapabilityEncodesIndices : ZKC_Capability<"Encodes.indices", [CodecDomain]>;
def CapabilityEncodesMatrix : ZKC_Capability<"Encodes.matrix", [CodecDomain, FieldDomain]>;
def CapabilityEncodesPoint : ZKC_Capability<"Encodes.point", [CodecDomain, FieldDomain]>;
def CapabilityEncodesPolynomial : ZKC_Capability<"Encodes.polynomial", [CodecDomain, FieldDomain]>;
def CapabilityEncodesProof : ZKC_Capability<"Encodes.proof", [CodecDomain, CommitmentDomain]>;
def CapabilityEncodesRound : ZKC_Capability<"Encodes.round", [CodecDomain, FieldDomain]>;
def CapabilityEncodesTable : ZKC_Capability<"Encodes.table", [CodecDomain, FieldDomain]>;
def CapabilityEncodesVector : ZKC_Capability<"Encodes.vector", [CodecDomain, FieldDomain]>;
def CapabilityExtensionField : ZKC_Capability<"ExtensionField", [FieldDomain]>;
def CapabilityField : ZKC_Capability<"Field", [FieldDomain]>;
def CapabilityFieldTranscript : ZKC_Capability<"FieldTranscript", [TranscriptDomain]>;
def CapabilityGroup : ZKC_Capability<"Group", [GroupDomain]>;
def CapabilityIndexRandomness : ZKC_Capability<"IndexRandomness", [FieldDomain]>;
def CapabilityIndexTranscript : ZKC_Capability<"IndexTranscript", [TranscriptDomain]>;
def CapabilityMultilinearOpening : ZKC_Capability<"MultilinearOpening", [CommitmentDomain]>;
def CapabilityPairingField : ZKC_Capability<"PairingField", [FieldDomain]>;
def CapabilityPrimeField : ZKC_Capability<"PrimeField", [FieldDomain]>;
def CapabilityScalarAction : ZKC_Capability<"ScalarAction", [GroupDomain]>;
def CapabilityTranscript : ZKC_Capability<"Transcript", [TranscriptDomain]>;
def CapabilityTwoAdicField : ZKC_Capability<"TwoAdicField", [FieldDomain]>;
def CapabilityVectorCommitment : ZKC_Capability<"VectorCommitment", [CommitmentDomain]>;
def RuleTwoadicfield : ZKC_Implication<CapabilityTwoAdicField, CapabilityField> { int ordinal = 0; }
def RulePrimefield : ZKC_Implication<CapabilityPrimeField, CapabilityField> { int ordinal = 1; }
def RuleExtensionfield : ZKC_Implication<CapabilityExtensionField, CapabilityField> { int ordinal = 2; }
def RulePairingfield : ZKC_Implication<CapabilityPairingField, CapabilityField> { int ordinal = 3; }
def RuleField : ZKC_Implication<CapabilityField, CapabilityCommRing> { int ordinal = 4; }
def RuleFieldtranscript : ZKC_Implication<CapabilityFieldTranscript, CapabilityTranscript> { int ordinal = 5; }
def ExportCapabilityCommRing : ZKC_CapabilityExport<"zkc::algebra", "CommRing", CapabilityCommRing>;
def ExportCapabilityField : ZKC_CapabilityExport<"zkc::algebra", "Field", CapabilityField>;
def ExportCapabilityPrimeField : ZKC_CapabilityExport<"zkc::algebra", "PrimeField", CapabilityPrimeField>;
def ExportCapabilityExtensionField : ZKC_CapabilityExport<"zkc::algebra", "ExtensionField", CapabilityExtensionField>;
def ExportCapabilityTwoAdicField : ZKC_CapabilityExport<"zkc::algebra", "TwoAdicField", CapabilityTwoAdicField>;
def ExportCapabilityCharacteristicNotTwo : ZKC_CapabilityExport<"zkc::algebra", "CharacteristicNotTwo", CapabilityCharacteristicNotTwo>;
def ExportCapabilityPairingField : ZKC_CapabilityExport<"zkc::algebra", "PairingField", CapabilityPairingField>;
def ExportCapabilityIndexRandomness : ZKC_CapabilityExport<"zkc::random", "IndexRandomness", CapabilityIndexRandomness>;
def ExportCapabilityGroup : ZKC_CapabilityExport<"zkc::curve", "Group", CapabilityGroup>;
def ExportCapabilityScalarAction : ZKC_CapabilityExport<"zkc::curve", "ScalarAction", CapabilityScalarAction>;
def ExportCapabilityMultilinearOpening : ZKC_CapabilityExport<"zkc::pcs", "MultilinearOpening", CapabilityMultilinearOpening>;
def ExportCapabilityVectorCommitment : ZKC_CapabilityExport<"zkc::oracle", "VectorCommitment", CapabilityVectorCommitment>;
def ExportCapabilityTranscript : ZKC_CapabilityExport<"zkc::transcript", "TranscriptCapability", CapabilityTranscript>;
def ExportCapabilityFieldTranscript : ZKC_CapabilityExport<"zkc::transcript", "FieldTranscript", CapabilityFieldTranscript>;
def ExportCapabilityIndexTranscript : ZKC_CapabilityExport<"zkc::transcript", "IndexTranscript", CapabilityIndexTranscript>;
