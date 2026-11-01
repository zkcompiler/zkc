#ifndef ZKC_DIALECT_RESIDUE_IR_RESIDUEDIALECT_TD
#define ZKC_DIALECT_RESIDUE_IR_RESIDUEDIALECT_TD
include "zkc/Dialect/Base.td"
def ResidueDialect : ZKCDialect {
  let name = "residue";
  let cppNamespace = "::zkc::residue";
  let useDefaultTypePrinterParser = 1;
  let useDefaultAttributePrinterParser = 1;
  let hasConstantMaterializer = 1;
}
#endif
