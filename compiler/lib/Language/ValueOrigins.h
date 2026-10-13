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
  std::vector<const Operation *> producers;
  std::map<ValueOrigin, ValueOrigin> selections;
  std::vector<std::optional<ValueOrigin>> origins;
  std::set<unsigned> active;
  bool initialized = false;
  bool initialize();

public:
  ValueOrigins(Semantics &types, const Body &body) : types(types), body(body) {}
  bool describes(const Body &value) const { return &value == &body; }
  std::optional<ValueOrigin> get(ValueId, Span = {});
  /// The checked SSA definition; null for an input. Shares the origin index.
  const Operation *producer(ValueId, Span = {});
  /// Resolve a field through ordinary immutable record construction.
  std::optional<ValueOrigin> select(ValueId, llvm::ArrayRef<unsigned>, Span);
};
} // namespace zkc::language::detail
#endif
