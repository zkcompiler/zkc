#ifndef ZKC_DIALECT_BASE_TD
#define ZKC_DIALECT_BASE_TD

include "mlir/IR/DialectBase.td"

// Apply strict owned-property admission to every operation registered by a zkc
// dialect. The field names still come from ODS; no second schema is maintained.
class ZKCDialect : Dialect {
  let extraClassDeclaration = [{
    template <typename... Ops>
    void addOperations() {
      ::mlir::Dialect::addOperations<::zkc::detail::StrictProperties<Ops>...>();
    }
  }];
}

#endif
