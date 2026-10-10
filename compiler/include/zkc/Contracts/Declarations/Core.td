// Logical contracts and curated exports owned by this domain.
def OpIndexConstant : ZKC_Operation<"index.constant", [],
    [],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 12;
  let parameters = NaturalParameter;
  let facets = [PublicReplay, ZKC_DomainValue<ConstantValue, 0, 0, 1>];
}
def ExportIndexConstant : ZKC_OperationExport<"zkc::algebra", "index_constant",
    OpIndexConstant, []>;

def OpIndexAdd : ZKC_Operation<"index.add", [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 13;
}
def ExportIndexAdd : ZKC_OperationExport<"zkc::algebra", "index_add",
    OpIndexAdd, ["index0", "index1"]>;

def OpIndexSub : ZKC_Operation<"index.sub", [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 14;
}
def ExportIndexSub : ZKC_OperationExport<"zkc::algebra", "index_sub",
    OpIndexSub, ["index0", "index1"]>;

def OpIndexMul : ZKC_Operation<"index.mul", [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 15;
}
def ExportIndexMul : ZKC_OperationExport<"zkc::algebra", "index_mul",
    OpIndexMul, ["index0", "index1"]>;

def OpIndexDiv : ZKC_Operation<"index.div", [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 16;
  let facets = [ZKC_DomainValue<DivideValue, 0, 0, 1>];
}
def ExportIndexDiv : ZKC_OperationExport<"zkc::algebra", "index_div",
    OpIndexDiv, ["index0", "index1"]>;

def OpIndexMod : ZKC_Operation<"index.mod", [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 17;
}
def ExportIndexMod : ZKC_OperationExport<"zkc::algebra", "index_mod",
    OpIndexMod, ["index0", "index1"]>;

def OpIndexEqual : ZKC_Operation<"index.equal", [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeBool, []>], []> {
  int ordinal = 18;
}
def ExportIndexEqual : ZKC_OperationExport<"zkc::algebra", "index_equal",
    OpIndexEqual, ["index0", "index1"]>;

def OpIndexLess : ZKC_Operation<"index.less", [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeBool, []>], []> {
  int ordinal = 19;
}
def ExportIndexLess : ZKC_OperationExport<"zkc::algebra", "index_less",
    OpIndexLess, ["index0", "index1"]>;

def OpIndicesEmpty : ZKC_Operation<"indices.empty", [],
    [],
    [ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 20;
}
def ExportIndicesEmpty : ZKC_OperationExport<"zkc::algebra", "indices_empty",
    OpIndicesEmpty, []>;

def OpIndicesAppend : ZKC_Operation<"indices.append", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 21;
}
def ExportIndicesAppend : ZKC_OperationExport<"zkc::algebra", "indices_append",
    OpIndicesAppend, ["indices", "index"]>;

def OpIndicesAt : ZKC_Operation<"indices.at", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 22;
}
def ExportIndicesAt : ZKC_OperationExport<"zkc::algebra", "indices_at",
    OpIndicesAt, ["indices", "index"]>;

def OpIndicesLength : ZKC_Operation<"indices.length", [],
    [ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 23;
}
def ExportIndicesLength : ZKC_OperationExport<"zkc::algebra", "indices_length",
    OpIndicesLength, ["indices"]>;

def OpBoolAnd : ZKC_Operation<"bool.and", [],
    [ZKC_Apply<TypeBool, []>, ZKC_Apply<TypeBool, []>],
    [ZKC_Apply<TypeBool, []>], []> {
  int ordinal = 97;
  let facets = [PublicReplay, Conjunction];
}
def ExportBoolAnd : ZKC_OperationExport<"zkc::core", "and",
    OpBoolAnd, ["bool0", "bool1"]>;

def OpBoolNot : ZKC_Operation<"bool.not", [],
    [ZKC_Apply<TypeBool, []>],
    [ZKC_Apply<TypeBool, []>], []> {
  int ordinal = 98;
  let facets = [PublicReplay];
}
def ExportBoolNot : ZKC_OperationExport<"zkc::core", "not",
    OpBoolNot, ["bool"]>;

def OpBoolOr : ZKC_Operation<"bool.or", [],
    [ZKC_Apply<TypeBool, []>, ZKC_Apply<TypeBool, []>],
    [ZKC_Apply<TypeBool, []>], []> {
  int ordinal = 99;
  let facets = [PublicReplay];
}
def ExportBoolOr : ZKC_OperationExport<"zkc::core", "or",
    OpBoolOr, ["bool0", "bool1"]>;

def OpControlRequire : ZKC_Operation<"control.require", [],
    [ZKC_Apply<TypeBool, []>],
    [], []> {
  int ordinal = 100;
  let facets = [AcceptanceGuard];
}
def ExportControlRequire : ZKC_OperationExport<"zkc::core", "require",
    OpControlRequire, ["bool"]>;
