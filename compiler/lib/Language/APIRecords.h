#ifndef ZKC_LANGUAGE_APIRECORDS_H
#define ZKC_LANGUAGE_APIRECORDS_H

#include "zkc/Language/Project.h"

namespace zkc::language::detail {
/// Checked ordinary bindings form a compact export graph. Module aliases are
/// edges, rather than eagerly expanded combinations of all accessible paths.
struct ExportRecord {
  DeclarationId owner, target;
  std::string name;
  Span span;
  bool imported = false;
};
/// The resolution route that selected a reference. Every successful route
/// records exactly one reference; a discarded lookup records none.
enum class ReferenceRoute {
  Path,
  Import,
  ImportName,
  Method,
  ModuleMember,
  Service,
  Notation,
  Construction
};
llvm::StringRef referenceRouteName(ReferenceRoute);
struct ReferenceNodeId {
  uint32_t index;
};
struct ReferencePosition {
  ReferenceNodeId node;
  ReferenceRoute kind;
  /// A node may own several references (for example selected import names).
  std::string slot;
  /// Repeated written names in the same node still occupy distinct positions.
  uint32_t ordinal = 0;
};
/// The provider is the source module selected by the written route. A facade
/// reference therefore retains its facade provider and its canonical target.
struct ReferenceRecord {
  DeclarationId owner, provider, target;
  Span span;
  std::string written;
  std::optional<std::string> abstractModule;
  ReferenceRoute route;
  ResolvedReference reference;
  ReferencePosition position;
};
struct APIRecords {
  std::vector<ExportRecord> exports;
  std::vector<ReferenceRecord> references;
  std::vector<bool> writtenRequirements, writtenEffects;
};
} // namespace zkc::language::detail
#endif
