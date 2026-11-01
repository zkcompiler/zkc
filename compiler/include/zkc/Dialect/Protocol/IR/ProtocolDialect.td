#ifndef ZKC_DIALECT_PROTOCOL_IR_PROTOCOLDIALECT_TD
#define ZKC_DIALECT_PROTOCOL_IR_PROTOCOLDIALECT_TD

include "zkc/Dialect/Base.td"

def ProtocolDialect : ZKCDialect {
  let name = "protocol";
  let cppNamespace = "::zkc::protocol_ir";
  // Oracle kinds and sequences derive their logical data carriers.
  let dependentDialects = ["::zkc::data::DataDialect"];
  let useDefaultTypePrinterParser = 1;
  let useDefaultAttributePrinterParser = 1;
  let extraClassDeclaration = ZkcStrictPropertyRegistration # [{
    void initializeAttributes();
  }];
}

#endif
