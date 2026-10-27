#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Support/Refusal.h"

namespace zkc::data {
llvm::Expected<llvm::SmallVector<mlir::Type>>
variantPayloadTypes(mlir::Type carrier, llvm::StringRef alternative) {
  if (!carrier)
    return error("variant-type");
  auto bound = protocol::encodeBoundType(
      carrier, mlir::isa<runtime::RepresentedType>(carrier));
  if (!bound)
    return bound.takeError();
  auto descriptor = protocol::decodeVariant("variant:" + bound->identity);
  if (bound->kind != "variant" || !descriptor)
    return error("variant-type");
  size_t offset = 0;
  for (const auto &arm : descriptor->alternatives) {
    if (arm.label != alternative) {
      offset += arm.payload.size();
      continue;
    }
    llvm::SmallVector<mlir::Type> result;
    for (auto [i, leaf] : llvm::enumerate(arm.payload)) {
      auto parsed = protocol::parseBoundType(leaf, false);
      if (!parsed)
        return parsed.takeError();
      if (!bound->representation.empty()) {
        if (!bound->physicalChildren ||
            offset + i >= bound->physicalChildren->size())
          return error("binding-representation");
        parsed = (*bound->physicalChildren)[offset + i];
      }
      auto type = protocol::decodeBoundType(carrier.getContext(), *parsed);
      if (!type)
        return error("variant-type");
      result.push_back(type);
    }
    return result;
  }
  return error("variant-alternative");
}
} // namespace zkc::data
