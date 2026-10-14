// Bounded byte data; no transcript or encoding policy is implicit.
def OpBytesEmpty : ZKC_Operation<"bytes.empty", [],
    [], [ZKC_Apply<TypeBytes, []>], []> {
  int ordinal = 161;
}

def OpBytesAppend : ZKC_Operation<"bytes.append", [],
    [ZKC_Apply<TypeBytes, []>, ZKC_Apply<TypeIndex, []>], [ZKC_Apply<TypeBytes, []>], []> {
  int ordinal = 162;
}

def OpBytesConcat : ZKC_Operation<"bytes.concat", [],
    [ZKC_Apply<TypeBytes, []>, ZKC_Apply<TypeBytes, []>], [ZKC_Apply<TypeBytes, []>], []> {
  int ordinal = 163;
}

def OpBytesSlice : ZKC_Operation<"bytes.slice", [],
    [ZKC_Apply<TypeBytes, []>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>], [ZKC_Apply<TypeBytes, []>], []> {
  int ordinal = 164;
}

def OpBytesAt : ZKC_Operation<"bytes.at", [],
    [ZKC_Apply<TypeBytes, []>, ZKC_Apply<TypeIndex, []>], [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 165;
}

def OpBytesLength : ZKC_Operation<"bytes.length", [],
    [ZKC_Apply<TypeBytes, []>], [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 166;
}

def OpBytesEqual : ZKC_Operation<"bytes.equal", [],
    [ZKC_Apply<TypeBytes, []>, ZKC_Apply<TypeBytes, []>], [ZKC_Apply<TypeBool, []>], []> {
  int ordinal = 167;
}
