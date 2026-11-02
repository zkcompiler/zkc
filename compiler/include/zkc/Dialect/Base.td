#ifndef ZKC_DIALECT_BASE_TD
#define ZKC_DIALECT_BASE_TD

include "mlir/IR/DialectBase.td"
include "mlir/IR/CommonAttrConstraints.td"
include "zkc/Contracts/Declarations/Schema.td"

// Call and callable metadata in an inherent field: the argument and result
// attribute dictionaries that MLIR's call interfaces declare. No semantic
// reader represents it, so the field inventory records it as refused, and a
// reader admits it only where it names it. Storage, accessors and the textual
// form are those of the wrapped attribute.
class CallMetadataAttr<Attr attr> : ConfinedAttr<attr, []>;

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
