#ifndef ZKC_DIALECT_BASE_TD
#define ZKC_DIALECT_BASE_TD

include "mlir/IR/DialectBase.td"

// IR-owned associations, attached to actual Op records. Exact keys and family
// prefixes are explicit: neither operation spellings nor semantic properties
// are inferred from them. Families end in a dot and are restricted to installed
// Contracts by the IR adapter. The generator rejects overlapping associations.
class ZKC_ContractMapping {
  list<string> contractKeys = [];
  list<string> contractFamilies = [];
}

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
