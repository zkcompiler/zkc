// Logical contracts and curated exports owned by this domain.
def OpRandomVectorF : ZKC_Root<"F", FieldDomain>;
def OpRandomVector : ZKC_Operation<"random.vector", [OpRandomVectorF],
    [ZKC_Apply<TypeRng, [OpRandomVectorF]>],
    [ZKC_Apply<TypeVector, [OpRandomVectorF]>, ZKC_Apply<TypeRng, [OpRandomVectorF]>], [ZKC_Holds<CapabilityField, [OpRandomVectorF]>]> {
  int ordinal = 83;
  let parameters = ExtentParameter;
  let facets = [ZKC_Sampling<Entropy, VectorSample, -1>];
}
def ExportRandomVector : ZKC_OperationExport<"zkc::random", "vector",
    OpRandomVector, ["rng"]>;

def OpRandomIndexF : ZKC_Root<"F", FieldDomain>;
def OpRandomIndex : ZKC_Operation<"random.index", [OpRandomIndexF],
    [ZKC_Apply<TypeRng, [OpRandomIndexF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeRng, [OpRandomIndexF]>], [ZKC_Holds<CapabilityIndexRandomness, [OpRandomIndexF]>]> {
  int ordinal = 123;
  let derivedCounterpart = OpTranscriptDrawIndex;
  let facets = [ZKC_Sampling<Entropy, IndexSample, 1>];
}
def ExportRandomIndex : ZKC_OperationExport<"zkc::random", "index",
    OpRandomIndex, ["rng", "index"]>;

def OpRandomDrawF : ZKC_Root<"F", FieldDomain>;
def OpRandomDraw : ZKC_Operation<"random.draw", [OpRandomDrawF],
    [ZKC_Apply<TypeRng, [OpRandomDrawF]>],
    [ZKC_Apply<TypeField, [OpRandomDrawF]>, ZKC_Apply<TypeRng, [OpRandomDrawF]>], [ZKC_Holds<CapabilityField, [OpRandomDrawF]>]> {
  int ordinal = 125;
  let derivedCounterpart = OpTranscriptChallenge;
  let facets = [ZKC_Sampling<Entropy, FieldSample, -1>];
}
def ExportRandomDraw : ZKC_OperationExport<"zkc::random", "draw",
    OpRandomDraw, ["rng"]>;

// No transcript counterpart is installed for this nonzero challenge domain.
def OpRandomDrawNonzeroF : ZKC_Root<"F", FieldDomain>;
def OpRandomDrawNonzero : ZKC_Operation<"random.draw_nonzero", [OpRandomDrawNonzeroF],
    [ZKC_Apply<TypeRng, [OpRandomDrawNonzeroF]>],
    [ZKC_Apply<TypeNonzeroField, [OpRandomDrawNonzeroF]>, ZKC_Apply<TypeRng, [OpRandomDrawNonzeroF]>],
    [ZKC_Holds<CapabilityField, [OpRandomDrawNonzeroF]>]> {
  int ordinal = 155;
  let facets = [ZKC_Sampling<Entropy, NonzeroFieldSample, -1>];
}
def ExportRandomDrawNonzero : ZKC_OperationExport<"zkc::random", "draw_nonzero",
    OpRandomDrawNonzero, ["rng"]>;
