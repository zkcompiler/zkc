// Canonical coefficient arrays in (Z/qZ)[X]/(X^n+1). Ring parameters and
// residues are checked at invocation; these are partial executable operations.
def OpQuotientAdd : ZKC_Operation<"quotient.add", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndices, []>], []> { int ordinal = 204; }
def OpQuotientSubtract : ZKC_Operation<"quotient.subtract", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndices, []>], []> { int ordinal = 205; }
def OpQuotientMultiply : ZKC_Operation<"quotient.multiply", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndices, []>], []> { int ordinal = 206; }
def OpQuotientNormWithin : ZKC_Operation<"quotient.norm_within", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeBool, []>], []> { int ordinal = 207; }
// Explicit projection and transform coordinates are separate from checked
// coefficient arithmetic. All dynamic input validation remains ordered.
def OpQuotientProject : ZKC_Operation<"quotient.project", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndices, []>]>;
def OpQuotientNTT : ZKC_Operation<"quotient.ntt", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndices, []>]>;
def OpQuotientINTT : ZKC_Operation<"quotient.intt", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndices, []>]>;
def OpQuotientPointwise : ZKC_Operation<"quotient.pointwise", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndices, []>]>;
