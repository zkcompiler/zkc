#ifndef ZKC_DIALECT_SEMANTICFIELDS_H
#define ZKC_DIALECT_SEMANTICFIELDS_H

#include "mlir/IR/Operation.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"

namespace zkc {
/// How semantic readers treat one inherent field of an operation in the closed
/// semantic profile. ODS records an operation's structure; this decision
/// records how its meaning is read, so a field that ODS gains is not admitted
/// merely because it is registered.
enum class FieldDecision {
  /// Part of the operation's specified meaning. Each semantic reader of the
  /// operation reads it through the typed accessor, restricts its value, or
  /// refuses the operation.
  Interpreted,
  /// Admitted only with the one supported value that the decision checks,
  /// such as an upstream flag left at its neutral setting.
  Restricted,
  /// Structure that MLIR verification owns, such as operand segment sizes.
  Structure,
  /// Upstream metadata that no reader represents. It is admitted only where a
  /// reader names it, like a discardable attribute.
  Refused,
};

/// One decided field of an operation in the closed semantic profile.
struct FieldCoverage {
  llvm::StringLiteral operation;
  llvm::StringLiteral field;
  FieldDecision decision;
  /// For a restricted field, whether a present value is the supported one.
  bool (*supported)(mlir::Attribute) = nullptr;
};

/// The operations in the closed semantic profile, ordered by name: every
/// operation of a zkc dialect, from the generated field inventory, and the
/// upstream operations that readers dispatch on, each through an explicit
/// adapter.
llvm::ArrayRef<llvm::StringLiteral> getSemanticOperations();
/// The decided fields of one operation in the closed profile, in ODS order for
/// a zkc operation. Every inherent attribute of a zkc operation is interpreted
/// and its segment sizes are structure.
llvm::ArrayRef<FieldCoverage> getFieldCoverage(llvm::StringRef operation);
/// Whether `operation` belongs to the closed profile.
bool isSemanticOperation(llvm::StringRef operation);

/// Whether a reader admits the present attribute `attribute` of `op`: one the
/// reader names in `named`, such as a discardable attribute it handles, or a
/// decided field of an operation in the closed profile whose decision admits
/// the value. An operation outside the profile admits only named attributes.
bool admitsField(mlir::Operation *op, mlir::NamedAttribute attribute,
                 llvm::ArrayRef<llvm::StringRef> named = {});
/// Whether `op` belongs to the closed profile and a reader that names `named`
/// admits every attribute it carries.
bool admitsFields(mlir::Operation *op,
                  llvm::ArrayRef<llvm::StringRef> named = {});
} // namespace zkc

#endif
