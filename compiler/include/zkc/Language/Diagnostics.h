#ifndef ZKC_LANGUAGE_DIAGNOSTICS_H
#define ZKC_LANGUAGE_DIAGNOSTICS_H
#include "zkc/Language/Project.h"

namespace zkc::language {
/// Render bounded ASCII diagnostics from captured bytes. Never opens a path.
/// Locations use one-based byte columns; control and non-ASCII bytes are
/// escaped. Invalid spans and omitted diagnostics are reported explicitly.
std::string formatDiagnostics(const CapturedProject &,
                              llvm::ArrayRef<Diagnostic>);
} // namespace zkc::language
#endif
