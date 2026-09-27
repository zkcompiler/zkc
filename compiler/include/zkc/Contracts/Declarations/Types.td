// Copy/drop/custody are owned here, including special existing carriers.
def TypeBool : ZKC_Type<"bool", [], PublicValue, 1, 1> { int ordinal = 0; }
def TypeIndex : ZKC_Type<"index", [], PublicValue, 1, 1> { int ordinal = 1; }
def TypeIndices : ZKC_Type<"indices", [], PublicValue, 1, 1> { int ordinal = 2; }
def TypeField : ZKC_Type<"field", [FieldDomain], PublicValue, 1, 1> { int ordinal = 3; }
def TypeVector : ZKC_Type<"vector", [FieldDomain], PublicValue, 1, 1> { int ordinal = 4; }
def TypeMatrix : ZKC_Type<"matrix", [FieldDomain], PublicValue, 1, 1> { int ordinal = 5; }
def TypePolynomial : ZKC_Type<"polynomial", [FieldDomain], PublicValue, 1, 1> { int ordinal = 6; }
def TypeTable : ZKC_Type<"table", [FieldDomain], PublicValue, 1, 1> { int ordinal = 7; }
def TypePoint : ZKC_Type<"point", [FieldDomain], PublicValue, 1, 1> { int ordinal = 8; }
def TypeRound : ZKC_Type<"round", [FieldDomain], PublicValue, 1, 1> { int ordinal = 9; }
def TypeRng : ZKC_Type<"rng", [FieldDomain], Affine, 0, 0> { int ordinal = 10; }
def TypeNonce : ZKC_Type<"nonce", [FieldDomain], Affine, 0, 0> { int ordinal = 11; }
def TypeGroup : ZKC_Type<"group", [GroupDomain], PublicValue, 1, 1> { int ordinal = 12; }
def TypeGroups : ZKC_Type<"groups", [GroupDomain], PublicValue, 1, 1> { int ordinal = 13; }
def TypeTranscript : ZKC_Type<"transcript", [TranscriptDomain], Affine, 0, 0> { int ordinal = 14; }
def TypeCommitment : ZKC_Type<"commitment", [CommitmentDomain], PublicValue, 1, 1> { int ordinal = 15; }
def TypeCommitments : ZKC_Type<"commitments", [CommitmentDomain], PublicValue, 1, 1> { int ordinal = 16; }
def TypeOpeningStates : ZKC_Type<"opening_states", [CommitmentDomain], PrivateImmutable, 1, 1> { int ordinal = 17; }
def TypeProof : ZKC_Type<"proof", [CommitmentDomain], PublicValue, 1, 1> { int ordinal = 18; }
def TypeProverKey : ZKC_Type<"prover_key", [CommitmentDomain], PrivateImmutable, 1, 1> { int ordinal = 19; }
def TypeVerifierKey : ZKC_Type<"verifier_key", [CommitmentDomain], PrivateImmutable, 1, 1> { int ordinal = 20; }
def TypeOpeningState : ZKC_Type<"opening_state", [CommitmentDomain], PrivateImmutable, 1, 1> { int ordinal = 21; }
def TypeScalar : ZKC_Type<"scalar", [], PublicValue, 1, 1> { let commonGeneric = 0; int ordinal = 22; }
def TypeCapability : ZKC_Type<"capability", [], Affine, 0, 0> { let commonGeneric = 0; int ordinal = 23; }
def TypeResourceUnit : ZKC_Type<"resource_unit", [], Affine, 0, 1> { let commonGeneric = 0; int ordinal = 24; }
def ExportTypeField : ZKC_TypeExport<"zkc::algebra", "Element", TypeField>;
def ExportTypeVector : ZKC_TypeExport<"zkc::algebra", "FieldVector", TypeVector>;
def ExportTypeMatrix : ZKC_TypeExport<"zkc::algebra", "FieldMatrix", TypeMatrix>;
def ExportTypePolynomial : ZKC_TypeExport<"zkc::poly", "Polynomial", TypePolynomial>;
def ExportTypeTable : ZKC_TypeExport<"zkc::poly", "Table", TypeTable>;
def ExportTypePoint : ZKC_TypeExport<"zkc::poly", "Point", TypePoint>;
def ExportTypeRound : ZKC_TypeExport<"zkc::poly", "Round", TypeRound>;
def ExportTypeRng : ZKC_TypeExport<"zkc::random", "Rng", TypeRng>;
def ExportTypeNonce : ZKC_TypeExport<"zkc::random", "Nonce", TypeNonce>;
def ExportTypeGroup : ZKC_TypeExport<"zkc::curve", "Element", TypeGroup>;
def ExportTypeGroups : ZKC_TypeExport<"zkc::curve", "Groups", TypeGroups>;
def ExportTypeTranscript : ZKC_TypeExport<"zkc::transcript", "Transcript", TypeTranscript>;
def ExportTypeCommitment : ZKC_TypeExport<"zkc::pcs", "Commitment", TypeCommitment>;
def ExportTypeCommitments : ZKC_TypeExport<"zkc::oracle", "Commitments", TypeCommitments>;
def ExportTypeOpeningStates : ZKC_TypeExport<"zkc::oracle", "OpeningStates", TypeOpeningStates>;
def ExportTypeProof : ZKC_TypeExport<"zkc::pcs", "Proof", TypeProof>;
def ExportTypeProverKey : ZKC_TypeExport<"zkc::pcs", "ProverKey", TypeProverKey>;
def ExportTypeVerifierKey : ZKC_TypeExport<"zkc::pcs", "VerifierKey", TypeVerifierKey>;
def ExportTypeOpeningState : ZKC_TypeExport<"zkc::pcs", "OpeningState", TypeOpeningState>;
def ExportTypeIndices : ZKC_TypeExport<"zkc::algebra", "Indices", TypeIndices>;

// Source families reduce only for an explicitly known nominal element head.
def VectorFamily : ZKC_TypeFamily<"vector-family">;
def MatrixFamily : ZKC_TypeFamily<"matrix-family">;
def VectorFieldCase : ZKC_TypeFamilyCase<VectorFamily, TypeField, TypeVector>;
def VectorGroupCase : ZKC_TypeFamilyCase<VectorFamily, TypeGroup, TypeGroups>;
def MatrixFieldCase : ZKC_TypeFamilyCase<MatrixFamily, TypeField, TypeMatrix>;
def ExportVectorFamily : ZKC_TypeExport<"zkc::algebra", "Vector", VectorFamily>;
def ExportMatrixFamily : ZKC_TypeExport<"zkc::algebra", "Matrix", MatrixFamily>;
def FieldElement : ZKC_AssociatedType<FieldDomain, "Element", TypeField>;
def GroupElement : ZKC_AssociatedType<GroupDomain, "Element", TypeGroup>;
