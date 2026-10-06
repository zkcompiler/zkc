// Public finite data. Shape remains part of the logical type through lowering.
def TypeFieldArray : ZKC_Type<"field_array", [FieldDomain, NatParameter],
                             PrivateImmutable, 1, 1>;
// This custody means no common codec. Native exchange has a separate closed
// rule over the complete field/length/representation; it is not confidentiality.
def ArrayField : ZKC_Root<"F", FieldDomain>;
def ArrayLength : ZKC_Root<"N", NatParameter>;
def OpFieldArrayFromVector : ZKC_Operation<"field_array.from_vector",
    [ArrayField, ArrayLength], [ZKC_Apply<TypeVector, [ArrayField]>],
    [ZKC_Apply<TypeFieldArray, [ArrayField, ArrayLength]>],
    [ZKC_Holds<CapabilityField, [ArrayField]>]>;
def OpFieldArrayAt : ZKC_Operation<"field_array.at", [ArrayField, ArrayLength],
    [ZKC_Apply<TypeFieldArray, [ArrayField, ArrayLength]>],
    [ZKC_Apply<TypeField, [ArrayField]>],
    [ZKC_Holds<CapabilityField, [ArrayField]>]> {
  let parameters = NaturalParameter;
}
def ExportFieldArrayFromVector : ZKC_OperationExport<"zkc::algebra",
    "field_array_from_vector", OpFieldArrayFromVector, ["vector"]>;
def ExportFieldArrayAt : ZKC_OperationExport<"zkc::algebra",
    "field_array_at", OpFieldArrayAt, ["array"]>;
