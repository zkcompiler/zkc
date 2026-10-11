#ifndef ZKC_LANGUAGE_EFFECTS_H
#define ZKC_LANGUAGE_EFFECTS_H
#include "Semantics.h"
namespace zkc::language::detail {
bool joinEffects(Semantics &, EffectSummary &, const EffectSummary &,
                 Span = {});
bool effectsWithin(Semantics &, const EffectSummary &, const EffectSummary &,
                   Span = {});
std::optional<EffectSummary> bindingEffects(Semantics &, const Body &, unsigned,
                                            unsigned depth = 1, Span = {});
std::optional<EffectSummary> substituteEffects(Semantics &,
                                               const EffectSummary &,
                                               llvm::ArrayRef<EffectSummary>,
                                               Span = {});
/// Reconstruct from immediate operations and independently checked child-body
/// summaries, never from this body's advertised summary. Producers finish child
/// bodies first; witnesses must reconstruct every child body as well.
std::optional<EffectSummary>
inferEffects(Semantics &, llvm::ArrayRef<Declaration>, const Body &);
} // namespace zkc::language::detail
#endif
