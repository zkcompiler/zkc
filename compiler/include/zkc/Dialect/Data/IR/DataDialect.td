#ifndef ZKC_DIALECT_DATA_IR_DATADIALECT_TD
#define ZKC_DIALECT_DATA_IR_DATADIALECT_TD
include "zkc/Dialect/Base.td"
def DataDialect : ZKCDialect {
  let name = "data";
  let cppNamespace = "::zkc::data";
  // Collection element observations construct their nominal scalar types.
  let dependentDialects = ["::zkc::algebra::AlgebraDialect"];
  let useDefaultTypePrinterParser = 1;
  let useDefaultAttributePrinterParser = 1;
  let hasConstantMaterializer = 1;
}
#endif
