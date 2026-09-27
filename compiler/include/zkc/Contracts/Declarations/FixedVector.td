// A single nominal bulk value, distinct from source arrays and dynamic vectors.
def TypeFixedVector : ZKC_Type<"fixed_vector", [TypeParameter, NatParameter],
                              PrivateImmutable, 1, 1>;
def ExportFixedVector : ZKC_TypeExport<"zkc::algebra", "FixedVector",
                                       TypeFixedVector>;

// Type/Nat parameters survive common admission as a single nominal bulk value.
def FixedVectorF : ZKC_Root<"F", FieldDomain>;
def FixedVectorN : ZKC_Root<"N", NatParameter>;
def FixedVectorElement : ZKC_Apply<TypeField, [FixedVectorF]>;

def OpFixedVectorFromVector : ZKC_Operation<"fixed_vector.from_vector",
    [FixedVectorF, FixedVectorN, FixedVectorElement],
    [ZKC_Apply<TypeVector, [FixedVectorF]>],
    [ZKC_Apply<TypeFixedVector, [FixedVectorElement, FixedVectorN]>],
    [ZKC_Holds<CapabilityField, [FixedVectorF]>]>;
def OpFixedVectorToVector : ZKC_Operation<"fixed_vector.to_vector",
    [FixedVectorF, FixedVectorN, FixedVectorElement],
    [ZKC_Apply<TypeFixedVector, [FixedVectorElement, FixedVectorN]>],
    [ZKC_Apply<TypeVector, [FixedVectorF]>],
    [ZKC_Holds<CapabilityField, [FixedVectorF]>]> {
  let facets = [PublicReplay];
}
def OpFixedVectorDot : ZKC_Operation<"fixed_vector.dot",
    [FixedVectorF, FixedVectorN, FixedVectorElement],
    [ZKC_Apply<TypeFixedVector, [FixedVectorElement, FixedVectorN]>,
     ZKC_Apply<TypeFixedVector, [FixedVectorElement, FixedVectorN]>],
    [ZKC_Apply<TypeField, [FixedVectorF]>],
    [ZKC_Holds<CapabilityField, [FixedVectorF]>]>;

def ExportFixedVectorFromVector : ZKC_OperationExport<"zkc::algebra",
    "fixed_vector_from_vector", OpFixedVectorFromVector, ["vector"]>;
def ExportFixedVectorToVector : ZKC_OperationExport<"zkc::algebra",
    "fixed_vector_to_vector", OpFixedVectorToVector, ["vector"]>;
def ExportFixedVectorDot : ZKC_OperationExport<"zkc::algebra",
    "fixed_vector_dot", OpFixedVectorDot, ["left", "right"]>;
