#ifndef ZKC_DIALECT_BASE_TD
#define ZKC_DIALECT_BASE_TD

include "mlir/IR/DialectBase.td"
include "zkc/Contracts/Declarations/Schema.td"

// Apply strict owned-property admission to every operation registered by a zkc
// dialect. The field names still come from ODS; no second schema is maintained.
defvar ZkcStrictPropertyRegistration = [{
    template <typename... Ops>
    void addOperations() {
      ::mlir::Dialect::addOperations<::zkc::detail::StrictProperties<Ops>...>();
    }
}];

class ZKCDialect : Dialect {
  let extraClassDeclaration = ZkcStrictPropertyRegistration;
}

#endif
