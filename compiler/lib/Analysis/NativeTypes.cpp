#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Contracts/TypePolicy.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "zkc/Dialect/TypeFormation.h"
using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
bool isFormalType(Type type) {
  return isa_and_nonnull<poly::PolynomialType, poly::QuotientType>(type);
}
namespace {
struct PolicyInspection {
  unsigned &remaining;
  size_t &remainingBytes;
  bool &limited;

  bool charge(size_t bytes = 0) {
    if (!remaining || bytes > remainingBytes) {
      limited = true;
      return false;
    }
    --remaining;
    remainingBytes -= bytes;
    return true;
  }
  bool metadata(Attribute root) {
    SmallVector<Attribute> pending{root};
    while (!pending.empty()) {
      auto value = pending.pop_back_val();
      auto string = dyn_cast<StringAttr>(value);
      if (!charge(string ? string.getValue().size() : 0))
        return false;
      value.walkImmediateSubElements(
          [&](Attribute child) { pending.push_back(child); }, [](Type) {});
    }
    return true;
  }
  bool enter(unsigned depth) {
    if (depth >= 64) {
      limited = true;
      return false;
    }
    return charge();
  }
  std::optional<protocol::detail::PolicyNode> head(Type type) {
    if (auto variant = dyn_cast<data::VariantType>(type)) {
      if (!metadata(variant.getIdentity()))
        return std::nullopt;
      for (auto arm : variant.getAlternatives())
        if (!metadata(arm.getLabel()))
          return std::nullopt;
      return protocol::detail::PolicyNode{"variant", {}, false, false};
    }
    auto interface = dyn_cast<CatalogTypeInterface>(type);
    auto application =
        interface ? interface.getCatalogApplication() : std::nullopt;
    if (!application)
      return std::nullopt;
    for (auto argument : application->arguments)
      if (!metadata(argument))
        return std::nullopt;
    bool applied = !application->arguments.empty();
    StringRef identity;
    if (application->arguments.size() == 1)
      if (auto domain = dyn_cast<StringAttr>(application->arguments.front())) {
        identity = domain.getValue();
        applied = false;
      }
    return protocol::detail::PolicyNode{
        application->constructor, identity, applied,
        application->constructor == "field_array" &&
            protocol::nativeFieldArrayFrame(
                cast<StringAttr>(application->arguments[0]).getValue())};
  }
  template <class Include> bool children(Type type, Include include) {
    if (auto variant = dyn_cast<data::VariantType>(type)) {
      for (auto arm : variant.getAlternatives())
        for (auto payload : arm.getPayload())
          if (!include(payload))
            return false;
      return true;
    }
    auto application = cast<CatalogTypeInterface>(type).getCatalogApplication();
    for (auto argument : application->arguments)
      if (auto child = dyn_cast<TypeAttr>(argument))
        if (!include(child.getValue()))
          return false;
    return true;
  }
  std::optional<protocol::TypePolicyFacts> inspect(Type type) {
    return protocol::detail::walkTypePolicy(*this, type);
  }
};
bool formed(Type type) {
  if (!type)
    return false;
  // This optional query owns no diagnostic site. Its caller diagnoses an
  // unsupported use; the formed-type verifier still checks the entire tree.
  return succeeded(verifyLogicalType(
      [&] {
        auto diagnostic = emitError(UnknownLoc::get(type.getContext()));
        // Suppress only this diagnostic, retaining its failure status. A
        // context-wide handler could consume another thread's diagnostic.
        diagnostic.abandon();
        return diagnostic;
      },
      type));
}
} // namespace
std::optional<protocol::TypePolicyFacts> nativeTypeFacts(Type type,
                                                         unsigned &remaining,
                                                         size_t &remainingBytes,
                                                         bool &limited) {
  if (limited || !formed(type))
    return std::nullopt;
  return PolicyInspection{remaining, remainingBytes, limited}.inspect(type);
}
std::optional<NativeTypePolicy> nativeTypePolicy(Type type) {
  if (isFormalType(type))
    return NativeTypePolicy{true, false, false, false, false, false};
  unsigned remaining = 200000;
  size_t remainingBytes = 1024 * 1024;
  bool limited = false;
  auto facts = nativeTypeFacts(type, remaining, remainingBytes, limited);
  return facts ? facts->native : std::nullopt;
}
std::optional<NativeTypePolicy> NativeTypePolicies::get(Type type) {
  if (isFormalType(type))
    return NativeTypePolicy{true, false, false, false, false, false};
  if (auto found = cache.find(type); found != cache.end())
    return found->second;
  if (limited)
    return std::nullopt;
  std::optional<NativeTypePolicy> result;
  if (auto facts = nativeTypeFacts(type, remaining, remainingBytes, limited))
    result = facts->native;
  if (limited)
    (void)diagnostics::emit(owner->emitOpError(), "native-type-policy-limit",
                            "closed type analysis exceeds its node, depth or "
                            "native metadata budget");
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
