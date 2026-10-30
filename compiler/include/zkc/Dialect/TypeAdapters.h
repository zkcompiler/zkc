#ifndef ZKC_DIALECT_TYPE_ADAPTERS_H
#define ZKC_DIALECT_TYPE_ADAPTERS_H

#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/Dialect.h"
#include "mlir/IR/DialectRegistry.h"
#include "mlir/IR/TypeSupport.h"
#include "mlir/IR/Types.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Interfaces/CatalogType.h"
#include "llvm/ADT/ArrayRef.h"
#include <array>
#include <optional>
#include <type_traits>

namespace zkc::protocol::type_adapters {
/// Native catalog observations and boundary translation are distinct callbacks.
/// Observations inspect MLIR storage; parseBoundType owns byte-type admission.
/// A callback returns no value when its carrier does not apply.
struct TypeAdapter {
  llvm::StringLiteral constructor;
  mlir::Type (*decode)(mlir::MLIRContext *, const BoundType &);
  std::optional<BoundType> (*encode)(mlir::Type, llvm::StringRef constructor);
  std::optional<llvm::SmallVector<mlir::Attribute>> (*arguments)(
      mlir::Type, llvm::StringRef constructor);
  void (*attachInterface)(mlir::MLIRContext *, mlir::Dialect *);
  mlir::Type (*construct)(llvm::function_ref<mlir::InFlightDiagnostic()>,
                          mlir::MLIRContext *, llvm::StringRef constructor,
                          llvm::ArrayRef<mlir::Attribute> arguments);
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

/// Native observations use typed getters, never the serialization callbacks.
std::optional<CatalogTypeApplication> observeCatalogType(mlir::Type);
void registerCatalogTypeInterfaces(mlir::DialectRegistry &);
/// Dialects whose intrinsic verifiers use catalog observations attach their
/// models immediately after registering types, even in a minimal context.
void attachCatalogTypeModels(mlir::Dialect &);

template <typename Native>
struct CatalogTypeModel
    : CatalogTypeInterface::ExternalModel<CatalogTypeModel<Native>, Native> {
  std::optional<CatalogTypeApplication>
  getCatalogApplication(mlir::Type type) const {
    return observeCatalogType(type);
  }
};
template <typename Native>
void attachCatalogTypeInterface(mlir::MLIRContext *context,
                                mlir::Dialect *dialect) {
  if (dialect->getNamespace() != Native::dialectName)
    return;
  auto registered = mlir::AbstractType::lookup(Native::name, context);
  if (registered && registered->get().getTypeID() == Native::getTypeID() &&
      !registered->get().hasInterface(CatalogTypeInterface::getInterfaceID()))
    Native::template attachInterface<CatalogTypeModel<Native>>(*context);
}
template <typename... Native>
void attachCatalogTypeInterfaces(mlir::MLIRContext *context,
                                 mlir::Dialect *dialect) {
  (attachCatalogTypeInterface<Native>(context, dialect), ...);
}
} // namespace zkc::protocol::type_adapters

#endif
