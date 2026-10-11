#ifndef ZKC_LANGUAGE_BODYSUMMARY_H
#define ZKC_LANGUAGE_BODYSUMMARY_H
#include "Semantics.h"
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
};
struct BodySummary {
  // Math dependencies compose exactly at logical-value granularity. Local
  // execution conservatively depends on eager operands and capture snapshots;
  // these summaries never select an owner from a callback's constant result.
  std::vector<Dependencies> values, results, formation;
  Effects effects;
  bool parameterized = false;
};
std::optional<BodySummary>
summarizeBody(Semantics &, llvm::ArrayRef<Declaration>, const Body &,
              const Substitution &, llvm::ArrayRef<Dependencies>,
              llvm::ArrayRef<ScopedSummaryBinding>, unsigned = 1,
              llvm::ArrayRef<Dependencies> domains = {});
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
