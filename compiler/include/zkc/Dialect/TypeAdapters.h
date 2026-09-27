#ifndef ZKC_DIALECT_TYPE_ADAPTERS_H
#define ZKC_DIALECT_TYPE_ADAPTERS_H

#include "mlir/IR/Types.h"
#include "zkc/Contracts/Bindings.h"
#include "llvm/ADT/ArrayRef.h"
#include <array>
#include <optional>
#include <type_traits>

namespace zkc::protocol::type_adapters {
/// Representation translation only; parseBoundType owns admission. Callbacks
/// receive the complete BoundType so structural constructors can use
/// the same seam. An encoder returns no value when its carrier does not apply.
struct TypeAdapter {
  llvm::StringLiteral constructor;
  mlir::Type (*decode)(mlir::MLIRContext *, const BoundType &);
  std::optional<BoundType> (*encode)(mlir::Type, llvm::StringRef constructor);
};

// Direct helper signatures are checked against the logical declaration at each
// generated registration. They describe logical parameters, not ODS storage.
enum class ParameterKind { Domain, Type, Nat };
template <ParameterKind... Kinds> struct ParameterKinds {};

/// Compiled, immutable owner tables, with no runtime registration mechanism.
llvm::ArrayRef<llvm::ArrayRef<TypeAdapter>> installedAdapters();
/// Unknown or multiply registered constructors have no adapter.
const TypeAdapter *findAdapter(llvm::StringRef constructor);
/// Refuses both missing and ambiguous carrier matches, independently of order.
llvm::Expected<BoundType> encodeLogicalType(mlir::Type);

} // namespace zkc::protocol::type_adapters

#endif
