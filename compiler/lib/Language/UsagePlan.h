#ifndef ZKC_LANGUAGE_USAGEPLAN_H
#define ZKC_LANGUAGE_USAGEPLAN_H
#include "Semantics.h"

namespace zkc::language::detail {
/// Temporary checking data, discarded before final body elaboration. Authored
/// uses consume places; mutable-state transport records transfers and retains
/// conditional predecessor history when needed. Exclusive branches therefore
/// neither duplicate a value nor hide a use on a continuing path.
class UsagePlan {
public:
  using Guard = unsigned;
  static constexpr Guard never = 0, always = 1;
  struct Transfer {
    std::vector<unsigned> path;
    uint64_t before;
  };
  struct Part {
    std::vector<unsigned> path;
    unsigned origin;
    std::vector<unsigned> sourcePath;
    Guard guard;
    std::vector<Transfer> transfers;
  };
  using Value = std::vector<Part>;
  using Requirement = std::function<bool(const Type &, Usage, Span,
                                         llvm::StringRef, llvm::StringRef)>;

  UsagePlan(Semantics &, const Declaration &);
  unsigned branch(unsigned arms);
  Guard arm(unsigned branch, unsigned ordinal, Span);
  Guard intersect(Guard, Guard, Span);
  Guard unite(Guard, Guard, Span);
  Value own(const Type &, Span, Guard);
  /// Safe transfers coalesce into fresh state. Only later authored uses demand
  /// that partially consumed predecessors preserve a whole successor.
  Value join(Value, const Type &, Span);
  Value within(const Value &, Guard, Span);
  Value project(const Value &, llvm::ArrayRef<unsigned>, Span);
  Value product(llvm::ArrayRef<Value>, Span);
  bool use(const Value &, llvm::ArrayRef<unsigned>, Guard, Span);
  /// Normal region exits allow subsequent uses through forwarded state.
  /// Assignment and early completion instead inspect the current prefix.
  bool finish(const Value &, Guard, Span, bool prefixOnly);
  bool solve(const Requirement &);

private:
  Semantics &types;
  const Declaration &scope;
  struct Node {
    unsigned variable;
    std::vector<Guard> children;
    unsigned depth = 0;
    std::vector<Guard> ancestors;
  };
  // A node implies the common mandatory ancestor of its nonfalse children.
  // Jump links make implication between sequential prefixes logarithmic.
  Guard ancestorAtDepth(Guard, unsigned) const;
  Guard commonAncestor(Guard, Guard) const;
  bool impliesAncestor(Guard, Guard) const;
  std::vector<unsigned> arities;
  std::vector<Node> nodes;
  std::map<std::pair<unsigned, std::vector<Guard>>, Guard> unique;
  std::map<std::tuple<bool, Guard, Guard>, Guard> combinations;
  Guard node(unsigned, std::vector<Guard>, Span);
  Guard combine(bool disjunction, Guard, Guard, Span);
  struct Use {
    std::vector<unsigned> path;
    Guard guard;
    Span span;
    uint64_t order;
    std::vector<Transfer> transfers;
  };
  struct Origin {
    Type type;
    Span span;
    std::vector<Use> uses;
  };
  struct Exit {
    unsigned origin;
    std::vector<unsigned> path;
    Guard guard;
    Span span;
    std::optional<uint64_t> before;
  };
  std::vector<Origin> origins;
  std::vector<Exit> exits;
  uint64_t order = 0;
  using Coverage =
      std::map<std::vector<unsigned>, std::vector<std::pair<uint64_t, Guard>>>;
  bool finishPlace(const Exit &, const Type &, std::vector<unsigned>,
                   std::optional<Coverage> &, const Requirement &, unsigned);
};
} // namespace zkc::language::detail
#endif
