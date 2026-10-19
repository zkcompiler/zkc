#ifndef ZKC_CONTRACT_NUMERICAL
#define ZKC_CONTRACT_NUMERICAL
// Compiler-generated, consumer-owned positional signatures. Only F belongs to
// generic static scope. Numerical.cpp independently resolves [F,M] and all
// mask-selected ports; these declaration ports are the empty-mask signature.
def NumericalF : ZKC_Root<"F", FieldDomain>;
def OpNumericalMap
    : ZKC_Operation<"numerical.map", [NumericalF], [ZKC_Apply<TypeIndex, []>],
                    [ZKC_Apply<TypeVector, [NumericalF]>],
                    [ZKC_Holds<CapabilityField, [NumericalF]>]> {
  let parameters = NumericalExpression;
  let commonGeneric = 0;
  let stage = CompilerGenerated;
}
def OpNumericalSum
    : ZKC_Operation<"numerical.sum", [NumericalF], [ZKC_Apply<TypeIndex, []>],
                    [ZKC_Apply<TypeField, [NumericalF]>],
                    [ZKC_Holds<CapabilityField, [NumericalF]>]> {
  let parameters = NumericalExpression;
  let commonGeneric = 0;
  let stage = CompilerGenerated;
}
def OpNumericalProduct
    : ZKC_Operation<
          "numerical.product", [NumericalF], [ZKC_Apply<TypeIndex, []>],
          [ZKC_Apply<TypeField, [NumericalF]>],
          [ZKC_Holds<CapabilityField, [NumericalF]>]> {
  let parameters = NumericalExpression;
  let commonGeneric = 0;
  let stage = CompilerGenerated;
}
#endif
