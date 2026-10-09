#ifndef ZKC_LANGUAGE_DIAGNOSTICS_H
#define ZKC_LANGUAGE_DIAGNOSTICS_H
#include "zkc/Language/Project.h"

namespace zkc::language {
/// Render bounded ASCII diagnostics from captured bytes. Never opens a path.
/// Locations use one-based byte columns; control and non-ASCII bytes are
/// escaped. Invalid spans and omitted diagnostics are reported explicitly.
std::string formatDiagnostics(llvm::ArrayRef<Diagnostic>,
                              const CapturedProject * = nullptr);
/// Human-readable views of resolved terms; never used as semantic identities.
std::string formatType(const Type &);
std::string formatNatural(const Natural &);
} // namespace zkc::language
#endif
