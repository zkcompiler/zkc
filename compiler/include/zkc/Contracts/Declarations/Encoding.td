// Mathematical value encodings with explicit byte order and checked decoding.
def EncodingFieldBeDomain : ZKC_Root<"F", FieldDomain>;
def OpEncodingFieldBe : ZKC_Operation<"encoding.field_be", [EncodingFieldBeDomain],
    [ZKC_Apply<TypeField, [EncodingFieldBeDomain]>],
    [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 171; }
def EncodingFieldFromBeDomain : ZKC_Root<"F", FieldDomain>;
def OpEncodingFieldFromBe : ZKC_Operation<"encoding.field_from_be", [EncodingFieldFromBeDomain],
    [ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeBool, []>, ZKC_Apply<TypeField, [EncodingFieldFromBeDomain]>], []> { int ordinal = 172; }
def EncodingFieldReduceBeDomain : ZKC_Root<"F", FieldDomain>;
def OpEncodingFieldReduceBe : ZKC_Operation<"encoding.field_reduce_be", [EncodingFieldReduceBeDomain],
    [ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeField, [EncodingFieldReduceBeDomain]>], []> { int ordinal = 173; }
def EncodingGroupCompressedDomain : ZKC_Root<"G", GroupDomain>;
def OpEncodingGroupCompressed : ZKC_Operation<"encoding.group_compressed", [EncodingGroupCompressedDomain],
    [ZKC_Apply<TypeGroup, [EncodingGroupCompressedDomain]>],
    [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 174; }
def EncodingGroupFromCompressedDomain : ZKC_Root<"G", GroupDomain>;
def OpEncodingGroupFromCompressed : ZKC_Operation<"encoding.group_from_compressed", [EncodingGroupFromCompressedDomain],
    [ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeBool, []>, ZKC_Apply<TypeGroup, [EncodingGroupFromCompressedDomain]>], []> { int ordinal = 175; }

def EncodingFieldLeDomain : ZKC_Root<"F", FieldDomain>;
def OpEncodingFieldLe : ZKC_Operation<"encoding.field_le", [EncodingFieldLeDomain],
    [ZKC_Apply<TypeField, [EncodingFieldLeDomain]>],
    [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 179; }

def EncodingFieldFromLeDomain : ZKC_Root<"F", FieldDomain>;
def OpEncodingFieldFromLe : ZKC_Operation<"encoding.field_from_le", [EncodingFieldFromLeDomain],
    [ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeBool, []>, ZKC_Apply<TypeField, [EncodingFieldFromLeDomain]>], []> { int ordinal = 180; }

def EncodingFieldReduceLeDomain : ZKC_Root<"F", FieldDomain>;
def OpEncodingFieldReduceLe : ZKC_Operation<"encoding.field_reduce_le", [EncodingFieldReduceLeDomain],
    [ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeField, [EncodingFieldReduceLeDomain]>], []> { int ordinal = 181; }

def EncodingGroupDecodeCofactorDomain : ZKC_Root<"G", GroupDomain>;
def OpEncodingGroupDecodeCofactor : ZKC_Operation<"encoding.group_decode_cofactor", [EncodingGroupDecodeCofactorDomain],
    [ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeBool, []>, ZKC_Apply<TypeGroup, [EncodingGroupDecodeCofactorDomain]>], []> { int ordinal = 182; }

def EncodingCryptonoteMapDomain : ZKC_Root<"G", GroupDomain>;
def OpEncodingCryptonoteMap : ZKC_Operation<"encoding.cryptonote_map", [EncodingCryptonoteMapDomain],
    [ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeGroup, [EncodingCryptonoteMapDomain]>], []> { int ordinal = 183; }

def EncodingFieldsBeDomain : ZKC_Root<"T", FieldDomain>;
def OpEncodingFieldsBe : ZKC_Operation<"encoding.fields_be", [EncodingFieldsBeDomain],
    [ZKC_Apply<TypeVector, [EncodingFieldsBeDomain]>],
    [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 187; }

def EncodingFieldsLeDomain : ZKC_Root<"T", FieldDomain>;
def OpEncodingFieldsLe : ZKC_Operation<"encoding.fields_le", [EncodingFieldsLeDomain],
    [ZKC_Apply<TypeVector, [EncodingFieldsLeDomain]>],
    [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 188; }

def EncodingGroupsCompressedDomain : ZKC_Root<"T", GroupDomain>;
def OpEncodingGroupsCompressed : ZKC_Operation<"encoding.groups_compressed", [EncodingGroupsCompressedDomain],
    [ZKC_Apply<TypeGroups, [EncodingGroupsCompressedDomain]>],
    [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 189; }

// Shortest unsigned LEB128 of an entire u64 index; zero emits one byte.
def OpEncodingIndexUleb128 : ZKC_Operation<"encoding.index_uleb128", [],
    [ZKC_Apply<TypeIndex, []>], [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 190; }
