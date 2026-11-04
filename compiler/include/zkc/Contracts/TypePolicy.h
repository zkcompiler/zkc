#ifndef ZKC_CONTRACTS_TYPEPOLICY_H
#define ZKC_CONTRACTS_TYPEPOLICY_H
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/NativePolicy.h"

namespace zkc::protocol {
/// Independent judgments over a complete, formed logical type. A codec,
/// local copy permission and protocol availability are different authorities.
struct TypePolicyFacts {
  std::optional<NativeTypePolicy> native;
  bool copy = true, drop = true, message = true, setup = false;
  bool relation = true, protocolPort = true;
  Custody custody = Custody::PrivateImmutable;
};
namespace detail {
struct PolicyNode {
  llvm::StringRef kind, identity;
  bool applied = false, fieldArrayFrame = false;
};
struct PolicyChildren {
  bool supported = true, copy = true, drop = true, total = true, shared = true;
  bool protocolPort = true, constructible = true, message = true;
  bool setup = false, relation = true;
  void include(const TypePolicyFacts &child) {
    supported &= child.native.has_value();
    copy &= child.copy;
    drop &= child.drop;
    total &= child.native && child.native->total;
    shared &= child.native && child.native->shared;
    protocolPort &= child.protocolPort;
    constructible &= child.native && child.native->constructible;
    message &= child.message;
    setup |= child.setup;
    relation &= child.relation;
  }
};
std::optional<TypePolicyFacts> finishPolicy(const PolicyNode &,
                                            const PolicyChildren &);
/// The adapters borrow actual children and charge their own metadata. No
/// conversion to another type representation or spelling is needed to walk.
template <class Adapter, class Type>
std::optional<TypePolicyFacts> walkTypePolicy(Adapter &adapter, Type type,
                                              unsigned depth = 0) {
  if (!adapter.enter(depth))
    return std::nullopt;
  auto node = adapter.head(type);
  if (!node)
    return std::nullopt;
  PolicyChildren children;
  if (!adapter.children(type, [&](auto child) {
        auto facts = walkTypePolicy(adapter, child, depth + 1);
        if (!facts)
          return false;
        children.include(*facts);
        return true;
      }))
    return std::nullopt;
  return finishPolicy(*node, children);
}
} // namespace detail
/// Checks structural formation before walking; malformed public descriptors
/// cannot obtain optimistic facts. Physical layout is checked independently.
std::optional<TypePolicyFacts> typePolicy(const BoundType &, TypeParseBudget &);
std::optional<TypePolicyFacts> typePolicy(const BoundType &);
} // namespace zkc::protocol
#endif
