#ifndef ZKC_FRONTEND_DEPENDENCIES_H
#define ZKC_FRONTEND_DEPENDENCIES_H

#include "zkc/Frontend/Diagnostic.h"
#include "zkc/Frontend/Input.h"

namespace zkc::frontend {
enum class SourceForm { Unknown, Module, CarrierModule, Construction };

struct ModuleReference {
  std::string name;
  std::optional<source::Span> location;
};
struct RelationReference {
  std::string name, family, path;
  std::optional<source::Span> location;
};
struct LibraryIdentityDeclaration {
  std::string nameSpace, name, version, resolution;
  std::optional<source::Span> location;
};
struct LibraryDependency {
  std::string name;
  LibraryIdentityDeclaration identity;
  std::optional<source::Span> location;
};

/// Owned dependency spelling and declaration classification, without filesystem
/// access, relation decoding, name resolution, or semantic admission. Locations
/// use the caller's snapshot-local file ID and byte offsets in the input.
struct DependencyDeclarations {
  SourceForm form = SourceForm::Unknown;
  std::optional<source::Span> location;
  std::optional<std::string> profile;
  std::vector<ModuleReference> modules;
  std::vector<RelationReference> relations;
  std::vector<LibraryIdentityDeclaration> libraryIdentities;
  std::vector<LibraryDependency> libraries;
  std::vector<Diagnostic> diagnostics;
  /// True only when parsing and dependency declaration checks both succeed.
  bool complete = false;
  /// A parsed document exists and its recognized dependency declarations pass
  /// duplicate-name, module-name, and family checks. A recovering loader may
  /// discover these dependencies even when complete is false. This never
  /// authorizes compilation or overrides project admission.
  bool recoverable = false;
};

/// Inspect textual frontend syntax using the ordinary recovering parser.
/// Malformed declarations are omitted by that parser; fully recognized ones
/// retain their spelling even when a later declaration fails. Portable JSON
/// documents use parseProtocolDocument and contain no external requests.
DependencyDeclarations inspectDependencies(const Input &, uint32_t file = 0);
} // namespace zkc::frontend
#endif
