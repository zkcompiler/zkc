// Nominal slot identity is part of every resource signature.
def ResourceSlot : ZKC_Root<"S", SlotDomain>;
def OpResourceUnitCreate : ZKC_Operation<"resource_unit.create", [ResourceSlot],
    [],
    [ZKC_Apply<TypeResourceUnit, [ResourceSlot]>], []> {
  int ordinal = 0;
  let stage = CompilerGenerated;
}

def OpResourceUnitPass : ZKC_Operation<"resource_unit.pass", [ResourceSlot],
    [ZKC_Apply<TypeResourceUnit, [ResourceSlot]>],
    [ZKC_Apply<TypeResourceUnit, [ResourceSlot]>], []> {
  int ordinal = 1;
  let stage = CompilerGenerated;
}

def OpResourceUnitConsume : ZKC_Operation<"resource_unit.consume", [ResourceSlot],
    [ZKC_Apply<TypeResourceUnit, [ResourceSlot]>],
    [], []> {
  int ordinal = 2;
  let stage = CompilerGenerated;
}
