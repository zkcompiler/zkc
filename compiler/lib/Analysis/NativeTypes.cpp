#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
std::optional<NativeTypePolicy> nativeTypePolicy(Type type) {
  if (isa<poly::PolynomialType>(type))
    return NativeTypePolicy{true, false, false, false, false, false};
  auto logical = protocol::encodeBoundType(type, false);
  if (!logical) {
    consumeError(logical.takeError());
    return std::nullopt;
  }
  return protocol::nativeTypePolicy(*logical);
}
std::optional<NativeTypePolicy> NativeTypePolicies::get(Type type) {
  if (isa<poly::PolynomialType>(type))
    return NativeTypePolicy{true, false, false, false, false, false};
  if (auto found = cache.find(type); found != cache.end())
    return found->second;
  if (limited)
    return std::nullopt;
  auto logical = protocol::encodeBoundType(type, false);
  if (!logical) {
    consumeError(logical.takeError());
    cache[type] = std::nullopt;
    return std::nullopt;
  }
  size_t bytes = logical->spelling().size();
  std::optional<NativeTypePolicy> result;
  if (bytes > remainingBytes)
    limited = true;
  else {
    remainingBytes -= bytes;
    result = protocol::nativeTypePolicy(*logical, remaining, limited);
  }
  if (limited)
    (void)diagnostics::emit(owner->emitOpError(), "native-type-policy-limit",
                            "closed type analysis exceeds its node, depth or "
                            "distinct spelling budget");
  cache[type] = result;
  return result;
}
LogicalResult verifyTotalTypes(Operation *op, NativeTypePolicies &types) {
  for (auto type : op->getOperandTypes())
    if (auto policy = types.get(type);
        !policy || !policy->total || policy->affine)
      return diagnostics::emit(op->emitOpError(), "mathematical-formation",
                               "unsupported mathematical data type");
  for (auto type : op->getResultTypes())
    if (auto policy = types.get(type);
        !policy || !policy->total || policy->affine)
      return diagnostics::emit(op->emitOpError(), "mathematical-formation",
                               "unsupported mathematical data type");
  return success();
}

} // namespace zkc::mathematical
