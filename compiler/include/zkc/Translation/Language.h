#ifndef ZKC_TRANSLATION_LANGUAGE_H
#define ZKC_TRANSLATION_LANGUAGE_H
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Language/InspectionData.h"
#include "zkc/Language/Project.h"

namespace zkc::language {
struct SourceLocation {
  unsigned line, column;
  Span source;
};
/// A definition emission generates for a source operation rather than closing
/// it from a source declaration.
struct GeneratedDefinition {
  std::string symbol;
  /// `control`, `custody`, `finite` or `map`.
  std::string purpose;
  /// The emitter's local discriminator within that purpose.
  std::string part;
  /// Sorted, unique `(definition, site)` of every native instruction that
  /// created or reused it: provenance, never call ancestry.
  std::vector<std::pair<std::string, std::string>> origins;
};
/// What emission alone knows about the module it prints: every generated
/// definition, and every native site with the expression it was emitted for,
/// first assignment kept.
struct EmissionRecord {
  std::vector<GeneratedDefinition> generated;
  std::vector<EmittedSite> sites;
};
/// Direct, unsimplified Protocol IR. The caller supplies native dialects. A
/// supplied record receives the generated definitions and emitted sites.
llvm::Expected<std::string> emitOriginal(const ClosedEntry &,
                                         mlir::MLIRContext &,
                                         const Limits & = {},
                                         EmissionRecord * = nullptr);
struct Correspondence {
  uint64_t declarations = 0, operations = 0;
  std::vector<SourceLocation> locations;
};
/// Verify the module once, then compare actual SSA with the checked source.
/// Locations come from compared operations in the reparsed original. No
/// mutation, re-emission, canonicalization, or executable lowering occurs in
/// this check.
llvm::Expected<Correspondence>
compareOriginal(const ClosedEntry &, mlir::ModuleOp, const Limits & = {});
} // namespace zkc::language
#endif
