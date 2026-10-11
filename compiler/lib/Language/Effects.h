#ifndef ZKC_LANGUAGE_EFFECTS_H
#define ZKC_LANGUAGE_EFFECTS_H
#include "Semantics.h"
namespace zkc::language::detail {
bool joinEffects(Semantics &, EffectSummary &, const EffectSummary &,
                 Span = {});
bool effectsWithin(Semantics &, const EffectSummary &, const EffectSummary &,
                   Span = {});
std::optional<EffectSummary> bindingEffects(Semantics &, const Body &, unsigned,
                                            unsigned depth = 1);
std::optional<EffectSummary> substituteEffects(Semantics &,
                                               const EffectSummary &,
                                               llvm::ArrayRef<EffectSummary>,
                                               Span = {});
/// Reconstruct from operations, never from the body's advertised summary.
std::optional<EffectSummary> inferEffects(Semantics &,
                                          llvm::ArrayRef<Declaration>,
                                          const Body &, unsigned depth = 1);
} // namespace zkc::language::detail
#endif
