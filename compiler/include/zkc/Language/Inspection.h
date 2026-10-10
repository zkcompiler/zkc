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
struct NotationInspectionOptions {
  /// Include private declarations and lexical notation overrides/occurrences.
  bool includePrivate = false;
  /// Independently include records originating in installation sources.
  bool includeInstallation = false;
};
/// Version-0 diagnostic JSON with descriptors, original bindings, module and
/// lexical scopes, and occurrences. This separate view leaves declaration
/// inspection unchanged. Syntax metadata is not part of a native interface.
/// IDs are stable only within this CheckedProject; spans are UTF-8 byte
/// offsets. Named-call renderings describe checked targets and authored operand
/// order; they are tooling aids, not capture-preserving source rewrites.
/// Unemitted occurrences have no selected binding or runtime values. References
/// excluded by the requested filters are omitted or explicitly null, never
/// dangling. Rechecks retained work/declaration/notation limits before
/// traversal. Output is bounded during serialization by
/// limits.notationInspectionBytes (8 MiB by default); failure returns
/// source.limit, never a partial document.
llvm::Expected<std::string>
inspectNotations(const CheckedProject &, const NotationInspectionOptions & = {},
                 const Limits & = {});
} // namespace zkc::language
#endif
