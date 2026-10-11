#ifndef ZKC_LANGUAGE_VALUEORIGINS_H
#define ZKC_LANGUAGE_VALUEORIGINS_H
#include "Semantics.h"
namespace zkc::language::detail {
/// Immutable SSA place identity. Equal contents, types, and lexical names do
/// not establish identity; a projection preserves its root and complete path.
using ValueOrigin = std::pair<unsigned, std::vector<unsigned>>;
class ValueOrigins {
  Semantics &types;
  const Body &body;
  std::vector<const Projection *> projections;
  std::vector<std::optional<ValueOrigin>> origins;
  std::set<unsigned> active;
  bool initialized = false;
  bool initialize();

public:
  ValueOrigins(Semantics &types, const Body &body) : types(types), body(body) {}
  std::optional<ValueOrigin> get(ValueId, Span = {}, unsigned depth = 1);
};
} // namespace zkc::language::detail
#endif
