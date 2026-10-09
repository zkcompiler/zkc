#ifndef ZKC_LANGUAGE_INSPECTION_H
#define ZKC_LANGUAGE_INSPECTION_H
#include "zkc/Language/Project.h"

namespace zkc::language {
/// JSON array of completed public callable declarations, sorted by qualified
/// name. This is a diagnostic view of checked facts, not an admitted artifact.
/// Output is bounded by limits.interfaceBytes; no partial array is returned.
llvm::Expected<std::string> inspectDeclarations(const CheckedProject &,
                                                const Limits & = {});
} // namespace zkc::language
#endif
