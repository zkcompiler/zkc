#ifndef ZKC_DIALECT_PROPERTIES_H
#define ZKC_DIALECT_PROPERTIES_H

#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Dialect/Diagnostics.h"
#include "llvm/ADT/STLExtras.h"

namespace zkc::detail {
/// Registration adapter for the generated ODS property conversion. MLIR 23's
/// converter reads known fields but silently drops unknown dictionary entries.
/// Check the complete dictionary before calling it. Property-free operations
/// retain MLIR's empty-properties refusal. Discardable attributes are a
/// separate surface and never reach this check.
template <typename Op> class StrictProperties : public Op {
public:
  using Op::Op;
  using Properties = typename Op::Properties;

  // This is a registration adapter, not a new operation. Keep typed lookup,
  // casts, interfaces and property storage identical to the generated class.
  static mlir::TypeID resolveTypeID() { return mlir::TypeID::get<Op>(); }

  static mlir::LogicalResult setPropertiesFromAttr(
      Properties &properties, mlir::Attribute attr,
      llvm::function_ref<mlir::InFlightDiagnostic()> emitError) {
    if (auto dictionary = llvm::dyn_cast<mlir::DictionaryAttr>(attr)) {
      for (auto entry : dictionary) {
        if (!llvm::is_contained(Op::getAttributeNames(),
                                entry.getName().getValue())) {
          diagnostics::emit(emitError(), "mlir-unknown-property")
              << ": " << Op::getOperationName() << " has no property '"
              << entry.getName().getValue() << "'";
          return mlir::failure();
        }
      }
    }
    // Preserve ODS type checks, defaults and malformed-container diagnostics.
    return Op::setPropertiesFromAttr(properties, attr, emitError);
  }
};
} // namespace zkc::detail

#endif
