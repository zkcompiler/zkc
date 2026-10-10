#ifndef ZKC_LANGUAGE_INSPECTION_H
#define ZKC_LANGUAGE_INSPECTION_H
#include "zkc/Language/Project.h"

namespace zkc::language {
/// JSON inventory of canonical Entry names and run/proof kinds, sorted by name.
llvm::Expected<std::string> inspectEntries(const CheckedProject &,
                                           const Limits & = {});
/// JSON array of completed public callables from captured modules, sorted by
/// qualified name. Includes definition kind and source origin; installation
/// declarations remain in CheckedProject. This diagnostic view is not an
/// admitted artifact.
/// Output is bounded by limits.interfaceBytes; no partial array is returned.
llvm::Expected<std::string> inspectDeclarations(const CheckedProject &,
                                                const Limits & = {});
} // namespace zkc::language
#endif
