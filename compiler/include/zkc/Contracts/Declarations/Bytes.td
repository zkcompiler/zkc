// Bounded byte data; no transcript or encoding policy is implicit.
def OpBytesEmpty : ZKC_Operation<"bytes.empty", [],
    [], [ZKC_Apply<TypeBytes, []>], []> {
  int ordinal = 161;
}
def ExportBytesEmpty : ZKC_OperationExport<"zkc::bytes", "empty",
    OpBytesEmpty, []>;

def OpBytesAppend : ZKC_Operation<"bytes.append", [],
    [ZKC_Apply<TypeBytes, []>, ZKC_Apply<TypeIndex, []>], [ZKC_Apply<TypeBytes, []>], []> {
  int ordinal = 162;
}
def ExportBytesAppend : ZKC_OperationExport<"zkc::bytes", "append",
    OpBytesAppend, ["bytes", "byte"]>;

def OpBytesConcat : ZKC_Operation<"bytes.concat", [],
    [ZKC_Apply<TypeBytes, []>, ZKC_Apply<TypeBytes, []>], [ZKC_Apply<TypeBytes, []>], []> {
  int ordinal = 163;
}
def ExportBytesConcat : ZKC_OperationExport<"zkc::bytes", "concat",
    OpBytesConcat, ["left", "right"]>;

def OpBytesSlice : ZKC_Operation<"bytes.slice", [],
    [ZKC_Apply<TypeBytes, []>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>], [ZKC_Apply<TypeBytes, []>], []> {
  int ordinal = 164;
}
def ExportBytesSlice : ZKC_OperationExport<"zkc::bytes", "slice",
    OpBytesSlice, ["bytes", "start", "length"]>;

def OpBytesAt : ZKC_Operation<"bytes.at", [],
    [ZKC_Apply<TypeBytes, []>, ZKC_Apply<TypeIndex, []>], [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 165;
}
def ExportBytesAt : ZKC_OperationExport<"zkc::bytes", "at",
    OpBytesAt, ["bytes", "position"]>;

def OpBytesLength : ZKC_Operation<"bytes.length", [],
    [ZKC_Apply<TypeBytes, []>], [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 166;
}
def ExportBytesLength : ZKC_OperationExport<"zkc::bytes", "length",
    OpBytesLength, ["bytes"]>;

def OpBytesEqual : ZKC_Operation<"bytes.equal", [],
    [ZKC_Apply<TypeBytes, []>, ZKC_Apply<TypeBytes, []>], [ZKC_Apply<TypeBool, []>], []> {
  int ordinal = 167;
}
def ExportBytesEqual : ZKC_OperationExport<"zkc::bytes", "equal",
    OpBytesEqual, ["left", "right"]>;

