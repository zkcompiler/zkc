#include "zkc/Dialect/TypeAdapters.h"
#include "zkc/Support/Refusal.h"

namespace zkc::protocol::type_adapters {
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
