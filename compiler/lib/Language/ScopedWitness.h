#ifndef ZKC_LANGUAGE_SCOPEDWITNESS_H
#define ZKC_LANGUAGE_SCOPEDWITNESS_H
#include "Internal.h"
#include "TypeInference.h"
namespace zkc::language::detail {
struct ScopedSource {
  DeclarationId owner;
  uint32_t expression;
  std::shared_ptr<const SyntaxDeclaration> syntax;
  struct Place {
    Type type;
    std::optional<ValueId> value;
    std::vector<std::pair<std::vector<unsigned>, ValueId>> pieces;
  };
  std::map<BindingId, Place> environment;
  std::map<BindingId, unsigned> scoped, domains;
  ScopedSignature signature;
};
struct ScopedInvocationSource {
  DeclarationId owner;
  uint32_t expression;
  std::shared_ptr<const SyntaxDeclaration> syntax;
};
struct ScopedCallSource {
  DeclarationId owner, target;
  uint32_t expression;
  std::shared_ptr<const SyntaxDeclaration> syntax;
  std::map<BindingId, unsigned> scoped, domains;
};
bool checkScopedValues(Semantics &, const CheckedStorage &,
                       const ScopedSource &, const ScopedBinding &);
llvm::Error checkScopedSources(const CheckedStorage &, Work &);
} // namespace zkc::language::detail
#endif
