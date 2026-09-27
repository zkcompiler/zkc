#ifndef ZKC_DIALECT_BASE_TD
#define ZKC_DIALECT_BASE_TD

include "mlir/IR/DialectBase.td"
include "zkc/Contracts/Declarations/Schema.td"

// IR-owned associations reference neutral logical declarations. Multiple exact
// contracts on an Op must have identical installed signatures. Generation
// validates declaration ownership and rejects duplicate associations.
class ZKC_ContractMapping {
  list<ZKC_Operation> contracts = [];
  // A finite, explicit alternative for transcript observations: each declaration
  // retains its payload type, static scope and codec requirements. The generator
  // checks the common state transition and observation/history port layout.
  // These also emit exact rows, never a prefix accepting future declarations.
  list<ZKC_Operation> observationContracts = [];
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
