#include "zkc/Analysis/NativeTypes.h"
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
struct TypeFacts {
  NativeTypePolicy policy;
  bool copy, message;
};
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
  std::optional<TypeFacts> inspect(Type type, unsigned depth = 0) {
    if (depth >= 64 || !charge()) {
      limited = true;
      return std::nullopt;
    }
    bool childrenCopy = true, childrenTotal = true, childrenShared = true,
         protocolPort = true, childrenConstructible = true,
         childrenMessage = true;
    auto include = [&](Type child) {
      auto facts = inspect(child, depth + 1);
      if (!facts)
        return false;
      childrenCopy &= facts->copy;
      childrenTotal &= facts->policy.total;
      childrenShared &= facts->policy.shared;
      protocolPort &= facts->policy.protocolPort;
      childrenConstructible &= facts->policy.constructible;
      childrenMessage &= facts->message;
      return true;
    };
    auto aggregate = [&] {
      return TypeFacts{{childrenCopy && childrenTotal,
                        childrenCopy && childrenShared, !childrenCopy,
                        childrenCopy && protocolPort, childrenMessage,
                        childrenConstructible},
                       childrenCopy,
                       childrenMessage};
    };
    if (auto variant = dyn_cast<data::VariantType>(type)) {
      if (!metadata(variant.getIdentity()))
        return std::nullopt;
      for (auto arm : variant.getAlternatives()) {
        if (!metadata(arm.getLabel()))
          return std::nullopt;
        for (auto payload : arm.getPayload())
          if (!include(payload))
            return std::nullopt;
      }
      return aggregate();
    }
    auto interface = dyn_cast<CatalogTypeInterface>(type);
    auto application =
        interface ? interface.getCatalogApplication() : std::nullopt;
    if (!application)
      return std::nullopt;
    auto kind = application->constructor;
    auto constructor = protocol::nativeTypeConstructorPolicy(kind);
    auto *permissions = protocol::typePermissions(kind);
    if (!constructor || !permissions)
      return std::nullopt;
    for (auto argument : application->arguments) {
      if (auto nested = dyn_cast<TypeAttr>(argument)) {
        if (!charge() || !include(nested.getValue()))
          return std::nullopt;
      } else if (!metadata(argument))
        return std::nullopt;
    }
    if (kind == "sequence")
      return aggregate();
    // Atomic codecs are selected by the nominal domain, never by the printed
    // type. Complete-type containers do not inherit an element's codec.
    StringRef identity;
    bool atomic = application->arguments.empty();
    if (application->arguments.size() == 1)
      if (auto domain = dyn_cast<StringAttr>(application->arguments.front())) {
        identity = domain.getValue();
        atomic = true;
      }
    bool message = atomic && protocol::nativeMessageAtom(kind, identity);
    bool wire = constructor->shared && atomic &&
                permissions->custody == protocol::Custody::PublicValue &&
                protocol::installedDomains().defaultCodec(kind, identity);
    if (kind == "field_array") {
      // Logical formation has already checked Domain/Nat argument kinds and
      // extent bounds. This is the existing native frame's exact field.
      wire = cast<StringAttr>(application->arguments[0]).getValue() ==
             "bls12-381.fr";
      message = wire;
    }
    return TypeFacts{
        {constructor->total, constructor->shared,
         permissions->custody == protocol::Custody::Affine || !childrenCopy,
         protocolPort, wire,
         constructor->constructible && childrenConstructible},
        permissions->copy && childrenCopy,
        message};
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
std::optional<NativeTypePolicy> nativeTypePolicy(Type type) {
  if (isFormalType(type))
    return NativeTypePolicy{true, false, false, false, false, false};
  if (!formed(type))
    return std::nullopt;
  unsigned remaining = 200000;
  size_t remainingBytes = 1024 * 1024;
  bool limited = false;
  auto facts =
      PolicyInspection{remaining, remainingBytes, limited}.inspect(type);
  return facts ? std::optional(facts->policy) : std::nullopt;
}
std::optional<NativeTypePolicy> NativeTypePolicies::get(Type type) {
  if (isFormalType(type))
    return NativeTypePolicy{true, false, false, false, false, false};
  if (auto found = cache.find(type); found != cache.end())
    return found->second;
  if (limited)
    return std::nullopt;
  std::optional<NativeTypePolicy> result;
  if (formed(type))
    if (auto facts =
            PolicyInspection{remaining, remainingBytes, limited}.inspect(type))
      result = facts->policy;
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
