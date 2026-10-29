#ifndef ZKC_LANGUAGE_COMPANIONS_H
#define ZKC_LANGUAGE_COMPANIONS_H
#include "zkc/Language/Project.h"
namespace zkc::language {
enum class ObligationRole {
  Postcondition,
  Request,
  SourceCorrespondence,
  ImplementationLaw,
  RealizationCorrespondence,
  StageLink
};
llvm::StringRef spelling(ObligationRole);
/// A reusable lookup address, never proof or artifact identity. The caller
/// independently fixes the context, substitution and expected Lean type.
llvm::Expected<std::string>
companionIdentity(llvm::StringRef owner,
                  std::optional<llvm::StringRef> instance, ObligationRole role,
                  std::optional<llvm::StringRef> label, uint64_t ordinal,
                  const Limits & = {});
} // namespace zkc::language
#endif
