#ifndef ZKC_LANGUAGE_INSPECTION_H
#define ZKC_LANGUAGE_INSPECTION_H
#include "zkc/Language/Project.h"

namespace zkc::language {
/// Retained source types and port grouping for component contract admission.
/// This is declaration context, not a pending-claim marker or a proof.
llvm::Expected<std::string> inspectComponentDeclarations(const ClosedEntry &,
                                                         const Limits & = {});
/// JSON inventory of canonical Entry names and function/proof/deployment kinds,
/// sorted by name.
llvm::Expected<std::string> inspectEntries(const CheckedProject &,
                                           const Limits & = {});
/// All authored claims, including claims for unselected subjects. Normalized
/// subject arguments and source nodes identify each declaration; this inventory
/// neither resolves requests nor certifies claims.
llvm::Expected<std::string> inspectSourceClaimInventory(const CheckedProject &,
                                                        const Limits & = {});
/// JSON array of public modules, interfaces, callables and constructions,
/// sorted by canonical declaration path, excluding import alias routes.
/// Includes definition kind, source origin, inferred usage bounds and derived
/// boundary obligations with their origin and call spans;
/// installation declarations remain in CheckedProject. This diagnostic view is
/// not an admitted artifact. Output is bounded by limits.interfaceBytes; no
/// partial array is returned.
llvm::Expected<std::string> inspectDeclarations(const CheckedProject &,
                                                const Limits & = {});
/// Version-0 public API graph, including reexports, public types and resolved
/// source references. Private representations are omitted. Module aliases are
/// graph edges; all alias-path combinations are never expanded. References
/// identify the selected source provider separately from canonical targets.
/// Diagnostic only; grants no access and changes no artifact identity. Rechecks
/// retained work/declaration/operation limits and bounds traversal, depth and
/// output by limits.apiInspectionBytes. Failure is source.limit with no output.
llvm::Expected<std::string> inspectPublicAPI(const CheckedProject &,
                                             const Limits & = {});
/// Version-0 wire claims for exactly this Entry. Registry definitions, budget
/// binding and request meaning are resolved by Lean, independently of methods.
/// This diagnostic view changes neither native interfaces nor program identity.
llvm::Expected<std::string> inspectSourceClaims(const ClosedEntry &,
                                                const Limits & = {});
/// Strict comparison with the current checked export. Unknown/duplicate fields,
/// noncanonical numbers and changed attachments, requests or Entry are refused.
llvm::Error checkSourceClaims(const ClosedEntry &, llvm::StringRef,
                              const Limits & = {});
/// Written syntax with structural node addresses, before inference or lowering.
/// Includes captured and installation modules and binds both identities. This
/// is an input to source correspondence, not a certificate or an admitted IR.
/// Traversal uses the requested work/depth limits; serialization is bounded by
/// limits.apiInspectionBytes and returns no partial document on refusal.
llvm::Expected<std::string> inspectWrittenSource(const CheckedProject &,
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
