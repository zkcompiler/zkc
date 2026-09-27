#ifndef ZKC_FRONTEND_STATIC_TYPES_H
#define ZKC_FRONTEND_STATIC_TYPES_H

#include "../Syntax/Tree.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "llvm/ADT/STLExtras.h"
#include <set>

namespace zkc::frontend {
// Capability bounds must each determine one domain sort. Keep this probe
// shared with diagnostic dependency recovery; intersections of individually
// ambiguous bounds must not select a type in only one path.
inline std::vector<std::string> capabilityDomainSorts(llvm::StringRef bound) {
  std::vector<std::string> result;
  for (const auto &sort : protocol::domainSorts()) {
    generic::Signature signature;
    signature.scope.terms.push_back({"D", {}});
    signature.scope.sorts.push_back(sort);
    signature.requirements.push_back(
        requirements::Predicate::holds(bound.str(), {0}));
    if (auto error = protocol::checkStaticVocabulary(signature))
      llvm::consumeError(std::move(error));
    else
      result.push_back(sort);
  }
  return result;
}
// Resolution has already authorized these names. Internal names cannot be
// authored directly, and generated entry adapters carry resolved type data.
inline llvm::StringRef logicalConstructor(llvm::StringRef name) {
  if (name == "bool" || name == "index")
    return name;
  if (name.consume_front("__installed_type_"))
    return name;
  return {};
}
inline bool typeArgumentSyntax(const syntax::StaticTerm &term) {
  return !term.arguments.empty() ||
         !logicalConstructor(term.root.value).empty() ||
         (!term.members.empty() &&
          llvm::any_of(protocol::sourceAssociatedTypes(),
                       [&](const auto &member) {
                         return member.member == term.members.back();
                       }));
}
inline bool elementTypeFamily(llvm::StringRef name) {
  auto constructor = logicalConstructor(name);
  return llvm::any_of(protocol::sourceTypeFamilies(), [&](const auto &entry) {
    return entry.family == constructor;
  });
}
inline llvm::StringRef associatedTypeConstructor(llvm::StringRef sort,
                                                 llvm::StringRef member) {
  for (const auto &entry : protocol::sourceAssociatedTypes())
    if (entry.sort == sort && entry.member == member)
      return entry.constructor;
  return {};
}
inline llvm::StringRef familyResultConstructor(llvm::StringRef name,
                                               llvm::StringRef element) {
  auto family = logicalConstructor(name);
  for (const auto &entry : protocol::sourceTypeFamilies())
    if (entry.family == family && entry.elementConstructor == element)
      return entry.resultConstructor;
  return {};
}
} // namespace zkc::frontend
#endif
