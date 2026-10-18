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

// Whole-vector decoding of consecutive 32-byte big-endian scalars. Either the
// length is a multiple of 32 and every element is canonical, or the flag is
// false and the vector is empty; there is no modular reduction.
def EncodingFieldsFromBeDomain : ZKC_Root<"T", FieldDomain>;
def OpEncodingFieldsFromBe : ZKC_Operation<"encoding.fields_from_be", [EncodingFieldsFromBeDomain],
    [ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeBool, []>, ZKC_Apply<TypeVector, [EncodingFieldsFromBeDomain]>], []> { int ordinal = 192; }

// Shortest unsigned LEB128 of an entire u64 index; zero emits one byte.
def OpEncodingIndexUleb128 : ZKC_Operation<"encoding.index_uleb128", [],
    [ZKC_Apply<TypeIndex, []>], [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 190; }

// Ordered concatenation of each element's exact encoding; the decoder accepts
// only whole elements whose words are all canonical.
def EncodingFieldsFromLeDomain : ZKC_Root<"T", FieldDomain>;
def OpEncodingFieldsFromLe : ZKC_Operation<"encoding.fields_from_le", [EncodingFieldsFromLeDomain],
    [ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeBool, []>, ZKC_Apply<TypeVector, [EncodingFieldsFromLeDomain]>], []> { int ordinal = 193; }

// Little-endian Montgomery residues x*R mod p with R = 2^(8*w) for the
// field's canonical encoding width w; extension elements encode coordinatewise.
def EncodingFieldMontgomeryLeDomain : ZKC_Root<"F", FieldDomain>;
def OpEncodingFieldMontgomeryLe : ZKC_Operation<"encoding.field_montgomery_le", [EncodingFieldMontgomeryLeDomain],
    [ZKC_Apply<TypeField, [EncodingFieldMontgomeryLeDomain]>],
    [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 194; }

def EncodingFieldFromMontgomeryLeDomain : ZKC_Root<"F", FieldDomain>;
def OpEncodingFieldFromMontgomeryLe : ZKC_Operation<"encoding.field_from_montgomery_le", [EncodingFieldFromMontgomeryLeDomain],
    [ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeBool, []>, ZKC_Apply<TypeField, [EncodingFieldFromMontgomeryLeDomain]>], []> { int ordinal = 195; }

def EncodingFieldsMontgomeryLeDomain : ZKC_Root<"T", FieldDomain>;
def OpEncodingFieldsMontgomeryLe : ZKC_Operation<"encoding.fields_montgomery_le", [EncodingFieldsMontgomeryLeDomain],
    [ZKC_Apply<TypeVector, [EncodingFieldsMontgomeryLeDomain]>],
    [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 196; }

def EncodingFieldsFromMontgomeryLeDomain : ZKC_Root<"T", FieldDomain>;
def OpEncodingFieldsFromMontgomeryLe : ZKC_Operation<"encoding.fields_from_montgomery_le", [EncodingFieldsFromMontgomeryLeDomain],
    [ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeBool, []>, ZKC_Apply<TypeVector, [EncodingFieldsFromMontgomeryLeDomain]>], []> { int ordinal = 197; }
