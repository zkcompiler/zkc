#ifndef ZKC_LANGUAGE_NOTATIONRECORDS_H
#define ZKC_LANGUAGE_NOTATIONRECORDS_H

#include "zkc/Language/Project.h"

namespace zkc::language::detail {
// CheckedStorage owns these diagnostic records. IDs are vector indices, stable
// for this checked project and independent of inspection filters. No parser or
// inference state survives here, and none of these records is a native
// interface.
struct NotationDescriptorRecord {
  NotationDescriptor descriptor;
  Span span;
  bool isPublic = false, fixed = false, explicitSyntax = false;
};
struct NotationBindingRecord {
  uint32_t descriptor, scope;
  DeclarationId target;
  std::optional<std::string> component;
  std::vector<std::optional<std::string>> arguments;
  Span span, targetSpan;
  std::vector<Span> authoredArguments;
  std::vector<std::string> holes;
  std::string identity;
  bool isPublic = false, local = false;
};
struct NotationImportRecord {
  ModuleId module;
  Span span;
  std::optional<std::string> alias;
  std::vector<std::string> names, operators, notations, reductions;
  bool isPublic = false;
};
struct NotationScopeRecord {
  Span span;
  std::optional<uint32_t> parent;
  std::optional<DeclarationId> owner;
  std::optional<uint32_t> body;
  // Only module scopes retain complete visibility. Lexical scopes hold their
  // own declarations; matching descriptor keys replace the inherited family.
  std::vector<uint32_t> descriptors, bindings, visible, exported;
  std::vector<NotationImportRecord> imports;
  bool isPublic = true;
};
struct NotationOperandRecord {
  uint32_t expression;
  Span span;
};
struct NotationEmissionRecord {
  uint32_t binding, region, operation;
  // Owned by CheckedStorage::declarations and its immutable nested Bodies.
  // Never points into the temporary syntax tree or a solver candidate cache.
  const Operation *emitted;
  std::vector<std::string> arguments;
  std::optional<std::string> component;
  std::vector<uint32_t> family;
};
struct NotationOccurrenceRecord {
  uint32_t descriptor, scope, expression;
  DeclarationId owner;
  Span span;
  std::vector<NotationOperandRecord> operands;
  std::optional<NotationEmissionRecord> selection;
  bool isPublic = false;
};
struct NotationRecords {
  std::vector<NotationDescriptorRecord> descriptors;
  std::vector<NotationBindingRecord> bindings;
  std::vector<NotationScopeRecord> scopes;
  std::vector<NotationOccurrenceRecord> occurrences;
};
} // namespace zkc::language::detail
#endif
