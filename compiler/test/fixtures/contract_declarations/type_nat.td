include "zkc/Contracts/Declarations/Schema.td"
// These kinds are deliberately exercised only by the generator.
def ElementType : ZKC_Root<"Element", TypeParameter>;
def Length : ZKC_Root<"Length", NatParameter>;
def ArrayType : ZKC_Type<"fixture_array", [TypeParameter, NatParameter], PrivateImmutable> {
  let commonGeneric = 0;
}
def ArrayCopy : ZKC_Operation<"fixture.copy", [ElementType, Length],
    [ZKC_Apply<ArrayType, [ElementType, Length]>],
    [ZKC_Apply<ArrayType, [ElementType, Length]>]> {
  let commonGeneric = 0;
  let stage = CompilerGenerated;
}
