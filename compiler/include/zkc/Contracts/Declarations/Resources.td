// Logical contracts and curated exports owned by this domain.
def OpResourceUnitCreate : ZKC_Operation<"resource_unit.create", [],
    [],
    [ZKC_Apply<TypeResourceUnit>], []> {
  int ordinal = 0;
  let commonGeneric = 0;
  let stage = CompilerGenerated;
}

def OpResourceUnitPass : ZKC_Operation<"resource_unit.pass", [],
    [ZKC_Apply<TypeResourceUnit>],
    [ZKC_Apply<TypeResourceUnit>], []> {
  int ordinal = 1;
  let commonGeneric = 0;
  let stage = CompilerGenerated;
}

def OpResourceUnitConsume : ZKC_Operation<"resource_unit.consume", [],
    [ZKC_Apply<TypeResourceUnit>],
    [], []> {
  int ordinal = 2;
  let commonGeneric = 0;
  let stage = CompilerGenerated;
}
