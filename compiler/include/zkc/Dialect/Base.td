#ifndef ZKC_DIALECT_BASE_TD
#define ZKC_DIALECT_BASE_TD

include "mlir/IR/DialectBase.td"
include "zkc/Contracts/Declarations/Schema.td"

// IR-owned associations reference neutral logical declarations. Multiple exact
// contracts on an Op must have identical installed signatures. Generation
// validates declaration ownership and rejects duplicate associations.
class ZKC_ContractMapping {
  list<ZKC_Operation> contracts = [];
}

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
