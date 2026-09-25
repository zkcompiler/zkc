#ifndef ZKC_FRONTEND_TOOLING_LINTS_H
#define ZKC_FRONTEND_TOOLING_LINTS_H

#include "zkc/Frontend/Analysis.h"

namespace zkc::frontend::tooling {
/// Ordinary lexical usage only, for successfully checked bodies retained in
/// this snapshot. The result is separate from errors and never changes source
/// completeness. No decision-result or acceptance judgment is made.
std::vector<Diagnostic> unusedBindingWarnings(const Analysis &);
} // namespace zkc::frontend::tooling
#endif
