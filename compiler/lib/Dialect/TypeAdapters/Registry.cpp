#include "mlir/IR/BuiltinDialect.h"
#include "zkc/Dialect/TypeAdapters.h"
#include "zkc/Interfaces/CatalogType.cpp.inc"
#include "zkc/Support/Refusal.h"

namespace zkc::protocol::type_adapters {
std::optional<CatalogTypeApplication> observeCatalogType(mlir::Type type) {
  if (!type)
    return std::nullopt;
  std::optional<CatalogTypeApplication> result;
  for (auto table : installedAdapters())
    for (const auto &adapter : table) {
      if (!adapter.arguments)
        continue;
      auto arguments = adapter.arguments(type, adapter.constructor);
      if (!arguments)
        continue;
      if (result || findAdapter(adapter.constructor) != &adapter)
        return std::nullopt;
      result =
          CatalogTypeApplication{adapter.constructor, std::move(*arguments)};
    }
  return result;
}
void attachCatalogTypeModels(mlir::Dialect &dialect) {
  auto *context = dialect.getContext();
  auto *builtin = context->getLoadedDialect<mlir::BuiltinDialect>();
  for (auto table : installedAdapters())
    for (const auto &adapter : table)
      if (adapter.attachInterface) {
        adapter.attachInterface(context, &dialect);
        if (builtin && builtin != &dialect)
          adapter.attachInterface(context, builtin);
      }
}
namespace {
struct CatalogTypeExtension : mlir::DialectExtensionBase {
  CatalogTypeExtension() : DialectExtensionBase({}) {}
  void apply(mlir::MLIRContext *context,
             mlir::MutableArrayRef<mlir::Dialect *> dialects) const override {
    (void)context;
    for (auto *dialect : dialects)
      attachCatalogTypeModels(*dialect);
  }
  std::unique_ptr<DialectExtensionBase> clone() const override {
    return std::make_unique<CatalogTypeExtension>();
  }
};
} // namespace
void registerCatalogTypeInterfaces(mlir::DialectRegistry &registry) {
  registry.addExtensions<CatalogTypeExtension>();
}
const TypeAdapter *findAdapter(llvm::StringRef constructor) {
  const TypeAdapter *result = nullptr;
  for (auto table : installedAdapters())
    for (const auto &adapter : table)
      if (adapter.constructor == constructor) {
        if (result)
          return nullptr;
        result = &adapter;
      }
  return result;
}

llvm::Expected<BoundType> encodeLogicalType(mlir::Type type) {
  if (!type)
    return error("binding-type");
  std::optional<BoundType> result;
  for (auto table : installedAdapters())
    for (const auto &adapter : table) {
      auto candidate = adapter.encode(type, adapter.constructor);
      if (!candidate)
        continue;
      if (result || candidate->kind != adapter.constructor ||
          !candidate->representation.empty() ||
          findAdapter(adapter.constructor) != &adapter)
        return error("binding-type");
      result = std::move(candidate);
    }
  if (!result)
    return error("binding-type");
  return std::move(*result);
}
} // namespace zkc::protocol::type_adapters
