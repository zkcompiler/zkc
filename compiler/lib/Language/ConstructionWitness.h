#ifndef ZKC_LANGUAGE_CONSTRUCTIONWITNESS_H
#define ZKC_LANGUAGE_CONSTRUCTIONWITNESS_H
#include "Internal.h"
namespace zkc::language::detail {
/// Only written header terms are retained here. Resolved member authority is
/// the existing authored reference inventory, shared through ReferenceSite.
struct ConstructionSource {
  std::optional<SyntaxType> parent, provider, codec;
};
/// Authenticate open construction projections before ordinary specialization.
/// This does not check handler bodies or reconstruct conformance premises.
llvm::Error checkConstructionSources(const CheckedStorage &, Work &);
} // namespace zkc::language::detail
#endif
