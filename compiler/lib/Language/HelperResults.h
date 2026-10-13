#ifndef ZKC_LANGUAGE_HELPERRESULTS_H
#define ZKC_LANGUAGE_HELPERRESULTS_H

#include "ValueOrigins.h"
#include "zkc/Contracts/MathematicalFacts.h"
#include <memory>

namespace zkc::language::detail {

/// A shape relative to the helper's inputs. Domain parameters describe only
/// cardinality, never item identity or permission to omit domain admission.
struct ResultShape {
  std::optional<ValueOrigin> input;
  unsigned axis = 0;
  std::optional<unsigned> domain;
  std::optional<facts::Cardinality> count;
  bool filtered = false;
};
struct HelperResult {
  std::optional<ValueOrigin> forwarded;
  ResultShape shape;
  unsigned height = 0;
};

/// Small result projections of an immutable checked declaration closure.
/// No snapshot identities or caller premises are cached. Callers instantiate
/// input selectors at each invocation and keep constructed results fresh.
/// Recreate this reader when checked declarations or bodies change.
class HelperResults {
  Semantics &types;
  llvm::ArrayRef<Declaration> declarations;
  using Key = std::tuple<unsigned, unsigned, std::vector<unsigned>>;
  std::map<Key, HelperResult> memo;
  std::map<unsigned, std::unique_ptr<ValueOrigins>> origins;
  std::set<Key> active;
  class Extraction;

public:
  HelperResults(Semantics &types, llvm::ArrayRef<Declaration> declarations)
      : types(types), declarations(declarations) {}
  const HelperResult *get(unsigned helper, unsigned result,
                          llvm::ArrayRef<unsigned> path, Span,
                          unsigned depth = 0);
};
} // namespace zkc::language::detail
#endif
