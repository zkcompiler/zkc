#ifndef ZKC_CONTRACT_NUMERICAL
#define ZKC_CONTRACT_NUMERICAL
// The complete positional ABI is the declared numerical signature family.
def NumericalF : ZKC_Root<"F", FieldDomain>;
class NumericalOperation<string mode>
    : ZKC_Operation<!strconcat("numerical.", mode), [NumericalF], [], [],
                    [ZKC_Holds<CapabilityField, [NumericalF]>]> {
  let numerical = ZKC_NumericalSignature<NumericalF, mode>;
  let parameters = NumericalExpression;
  let stage = CompilerGenerated;
}
def OpNumericalMap : NumericalOperation<"map">;
def OpNumericalSum : NumericalOperation<"sum">;
def OpNumericalProduct : NumericalOperation<"product">;
#endif
