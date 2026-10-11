// Mathematical value encodings with explicit byte order and checked decoding.
def EncodingFieldBeDomain : ZKC_Root<"F", FieldDomain>;
def OpEncodingFieldBe : ZKC_Operation<"encoding.field_be", [EncodingFieldBeDomain],
    [ZKC_Apply<TypeField, [EncodingFieldBeDomain]>],
    [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 171; }
def ExportEncodingFieldBe : ZKC_OperationExport<"zkc::encoding", "field_be", OpEncodingFieldBe, ["value"]>;
def EncodingFieldFromBeDomain : ZKC_Root<"F", FieldDomain>;
def OpEncodingFieldFromBe : ZKC_Operation<"encoding.field_from_be", [EncodingFieldFromBeDomain],
    [ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeBool, []>, ZKC_Apply<TypeField, [EncodingFieldFromBeDomain]>], []> { int ordinal = 172; }
def ExportEncodingFieldFromBe : ZKC_OperationExport<"zkc::encoding", "field_from_be", OpEncodingFieldFromBe, ["value"]>;
def EncodingFieldReduceBeDomain : ZKC_Root<"F", FieldDomain>;
def OpEncodingFieldReduceBe : ZKC_Operation<"encoding.field_reduce_be", [EncodingFieldReduceBeDomain],
    [ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeField, [EncodingFieldReduceBeDomain]>], []> { int ordinal = 173; }
def ExportEncodingFieldReduceBe : ZKC_OperationExport<"zkc::encoding", "field_reduce_be", OpEncodingFieldReduceBe, ["value"]>;
def EncodingGroupCompressedDomain : ZKC_Root<"G", GroupDomain>;
def OpEncodingGroupCompressed : ZKC_Operation<"encoding.group_compressed", [EncodingGroupCompressedDomain],
    [ZKC_Apply<TypeGroup, [EncodingGroupCompressedDomain]>],
    [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 174; }
def ExportEncodingGroupCompressed : ZKC_OperationExport<"zkc::encoding", "group_compressed", OpEncodingGroupCompressed, ["value"]>;
def EncodingGroupFromCompressedDomain : ZKC_Root<"G", GroupDomain>;
def OpEncodingGroupFromCompressed : ZKC_Operation<"encoding.group_from_compressed", [EncodingGroupFromCompressedDomain],
    [ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeBool, []>, ZKC_Apply<TypeGroup, [EncodingGroupFromCompressedDomain]>], []> { int ordinal = 175; }
def ExportEncodingGroupFromCompressed : ZKC_OperationExport<"zkc::encoding", "group_from_compressed", OpEncodingGroupFromCompressed, ["value"]>;
