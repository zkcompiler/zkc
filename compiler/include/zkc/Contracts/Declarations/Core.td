// Logical contracts and curated exports owned by this domain.
def OpIndexConstant : ZKC_Operation<"index.constant", [],
    [],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 12;
  let parameters = NaturalParameter;
  let facets = [PublicReplay, ZKC_DomainValue<ConstantValue, 0, 0, 1>];
}

def OpIndexAdd : ZKC_Operation<"index.add", [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 13;
}

def OpIndexSub : ZKC_Operation<"index.sub", [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 14;
}

def OpIndexMul : ZKC_Operation<"index.mul", [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 15;
}

def OpIndexDiv : ZKC_Operation<"index.div", [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 16;
  let facets = [ZKC_DomainValue<DivideValue, 0, 0, 1>];
}

def OpIndexMod : ZKC_Operation<"index.mod", [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 17;
}

def OpIndexEqual : ZKC_Operation<"index.equal", [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeBool, []>], []> {
  int ordinal = 18;
}

def OpIndexLess : ZKC_Operation<"index.less", [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeBool, []>], []> {
  int ordinal = 19;
}

def OpIndicesEmpty : ZKC_Operation<"indices.empty", [],
    [],
    [ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 20;
}

def OpIndicesAppend : ZKC_Operation<"indices.append", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 21;
}

def OpIndicesAt : ZKC_Operation<"indices.at", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 22;
}

def OpIndicesLength : ZKC_Operation<"indices.length", [],
    [ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 23;
}

def OpBoolAnd : ZKC_Operation<"bool.and", [],
    [ZKC_Apply<TypeBool, []>, ZKC_Apply<TypeBool, []>],
    [ZKC_Apply<TypeBool, []>], []> {
  int ordinal = 97;
  let facets = [PublicReplay, Conjunction];
}

def OpBoolNot : ZKC_Operation<"bool.not", [],
    [ZKC_Apply<TypeBool, []>],
    [ZKC_Apply<TypeBool, []>], []> {
  int ordinal = 98;
  let facets = [PublicReplay];
}

def OpBoolOr : ZKC_Operation<"bool.or", [],
    [ZKC_Apply<TypeBool, []>, ZKC_Apply<TypeBool, []>],
    [ZKC_Apply<TypeBool, []>], []> {
  int ordinal = 99;
  let facets = [PublicReplay];
}

def OpControlRequire : ZKC_Operation<"control.require", [],
    [ZKC_Apply<TypeBool, []>],
    [], []> {
  int ordinal = 100;
  let facets = [AcceptanceGuard];
}
