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
/// The provider is the source module selected by the written route. A facade
/// reference therefore retains its facade provider and its canonical target.
struct ReferenceRecord {
  DeclarationId owner, provider, target;
  Span span;
  std::string written;
  std::optional<std::string> abstractModule;
};
struct APIRecords {
  std::vector<ExportRecord> exports;
  std::vector<ReferenceRecord> references;
  std::vector<bool> writtenRequirements, writtenEffects;
};
} // namespace zkc::language::detail
#endif
