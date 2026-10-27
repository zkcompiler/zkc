#ifndef ZKC_LANGUAGE_LEXICALRECORDS_H
#define ZKC_LANGUAGE_LEXICALRECORDS_H
#include "zkc/Language/Project.h"

namespace zkc::language::detail {
/// Private parser coordinates. Inspection translates them through the frozen
/// written tree; no parser token, expression index or BindingId is serialized.
struct LexicalNode {
  enum class Kind { Expression, Pattern, Input } kind;
  unsigned index;
};
struct LexicalReference {
  enum class Access { Read, Call, Assign } access;
  LexicalNode use;
  std::optional<LexicalNode> binder;
};
struct LexicalResolution {
  Span declaration;
  std::vector<LexicalReference> references;
};
} // namespace zkc::language::detail
#endif
