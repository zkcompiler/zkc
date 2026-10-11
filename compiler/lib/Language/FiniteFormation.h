#ifndef ZKC_LANGUAGE_FINITEFORMATION_H
#define ZKC_LANGUAGE_FINITEFORMATION_H
#include "Semantics.h"
#include "llvm/ADT/STLFunctionalExtras.h"
namespace zkc::language::detail {
/// Queries over the current immutable data environment. ValueIds index the
/// closed descriptor inputs. No evidence is inferred from source names.
struct FiniteFormationEvidence {
  llvm::function_ref<std::optional<uint64_t>(ValueId)> constant;
  llvm::function_ref<std::optional<uint64_t>(ValueId, unsigned)> extent;
  llvm::function_ref<bool(ValueId, ValueId)> same;
  llvm::function_ref<bool(ValueId, unsigned, ValueId, unsigned)> equalExtent;
  llvm::function_ref<bool(ValueId, ValueId, unsigned)> bound;
};
/// Check every constructor in an already validated, closed domain graph and
/// the exact cardinality required by a fixed collection result.
bool checkFiniteFormation(Semantics &, const FiniteComputation &, const Type &,
                          bool total, Span, const FiniteFormationEvidence &);
} // namespace zkc::language::detail
#endif
