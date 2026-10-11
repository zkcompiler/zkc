#ifndef ZKC_LANGUAGE_MATHEMATICALFACTS_H
#define ZKC_LANGUAGE_MATHEMATICALFACTS_H
#include "ValueOrigins.h"
#include "zkc/Contracts/MathematicalFacts.h"
namespace zkc::language::detail {
struct SourceDataFact {
  DataPrecondition::Kind kind;
  ValueOrigin left, right;
  unsigned leftAxis = 0, rightAxis = 0;
};

/// Static source dimensions retain Natural interpretation. No runtime index
/// arithmetic is interpreted here, and no shape establishes value identity.
const Natural *staticExtent(const Type &, unsigned axis);

/// Independent source extraction over one ContractCheck traversal. Body
/// occurrences supply distinct roots; captures supply their actual origins.
/// Every extraction and nested core query debits the same Semantics allowance.
class MathematicalFacts {
  Semantics &types;
  Span span;
  facts::Work work;
  facts::Snapshot snapshot;
  facts::Scope current;
  std::map<Natural::Terms, facts::Extent> dimensions;

public:
  explicit MathematicalFacts(Semantics &);
  facts::Scope scope() const { return current; }
  facts::Status enter(Span);
  void restore(facts::Scope scope) { current = scope; }
  facts::Status record(const ValueOrigin &, const Type &, Span);
  facts::Status constant(const ValueOrigin &, uint64_t, Span);
  facts::Status assume(const SourceDataFact &, Span);
  facts::Status prove(const SourceDataFact &, Span);
};
} // namespace zkc::language::detail
#endif
