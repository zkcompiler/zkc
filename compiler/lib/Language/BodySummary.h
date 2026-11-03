#ifndef ZKC_LANGUAGE_BODYSUMMARY_H
#define ZKC_LANGUAGE_BODYSUMMARY_H
#include "Semantics.h"
#include <memory>
namespace zkc::language::detail {
/// An unresolved callback is distinct from a concrete constant result.
struct Dependencies {
  std::vector<unsigned> inputs;
  bool parameterized = false;
};
struct ScopedSummaryBinding {
  const ScopedComputation *computation = nullptr;
  ScopedSignature signature;
  Substitution statics;
  std::vector<Dependencies> captures;
  std::vector<ScopedSummaryBinding> scoped;
  std::vector<Dependencies> domains;
  /// A completed literal may belong to a discarded usage-inference scratch
  /// body. Retained instances extend its immutable lifetime explicitly.
  std::shared_ptr<const ScopedComputation> owner = {};
};
struct BodySummary {
  // Math dependencies compose exactly at logical-value granularity. Local
  // execution conservatively depends on eager operands and capture snapshots;
  // these summaries never select an owner from a callback's constant result.
  std::vector<Dependencies> values, results, formation;
  bool parameterized = false;
};
/// A boundary dependency product, without the body's internal SSA inventory.
/// It establishes neither common-value equality nor exact input forwarding.
struct BodySummaryApplication {
  std::vector<Dependencies> results, formation;
  bool parameterized = false;
};
/// Reconstruct the selected implementation's lexical self frame, while keeping
/// callback frames at the definition site where their actuals were written.
std::optional<Substitution>
bodySummaryFrame(Semantics &, llvm::ArrayRef<Declaration>, const Declaration &,
                 llvm::ArrayRef<Type>, const std::optional<Type> & = {});
/// Owned by one source Checker. Only completed immutable bodies may enter;
/// specialization and independent candidate reconstruction use summarizeBody
/// without this owner. Body addresses never escape that checking lifetime.
class BodySummaryCache {
public:
  BodySummaryCache();
  ~BodySummaryCache();
  BodySummaryCache(const BodySummaryCache &) = delete;
  BodySummaryCache &operator=(const BodySummaryCache &) = delete;
  std::optional<BodySummaryApplication>
  apply(Semantics &, llvm::ArrayRef<Declaration>, const Body &,
        const Substitution &, llvm::ArrayRef<Dependencies>,
        llvm::ArrayRef<ScopedSummaryBinding>, unsigned = 1,
        llvm::ArrayRef<Dependencies> domains = {});
  /// Whether completed logical dependencies are independent of static dispatch.
  std::optional<bool> staticIndependent(Semantics &,
                                        llvm::ArrayRef<Declaration>,
                                        const Body &, unsigned);

  /// Include nested operation traversal in the retained height.
  void observeDepth(unsigned);

private:
  struct Storage;
  std::unique_ptr<Storage> storage;
};
/// Full operation-derived inventory for construction and independent witnesses.
/// A source-checking consumer may share completed nested applications
/// explicitly.
std::optional<BodySummary>
summarizeBody(Semantics &, llvm::ArrayRef<Declaration>, const Body &,
              const Substitution &, llvm::ArrayRef<Dependencies>,
              llvm::ArrayRef<ScopedSummaryBinding>, unsigned = 1,
              llvm::ArrayRef<Dependencies> domains = {},
              BodySummaryCache *retained = nullptr);
std::optional<ScopedSummaryBinding>
summarizeScopedBinding(Semantics &, const Body &, unsigned,
                       const Substitution &, llvm::ArrayRef<Dependencies>,
                       llvm::ArrayRef<ScopedSummaryBinding>, unsigned = 1,
                       bool identityValues = false,
                       llvm::ArrayRef<Dependencies> domains = {});
/// Resolve a domain's eager operand dependencies in the caller's value space.
/// Unknown domain formals remain parameterized rather than appearing constant.
std::optional<Dependencies>
summarizeDomainBinding(Semantics &, const Body &, unsigned,
                       llvm::ArrayRef<Dependencies> values,
                       llvm::ArrayRef<Dependencies> environment = {},
                       unsigned depth = 1, bool identityValues = false);
} // namespace zkc::language::detail
#endif
