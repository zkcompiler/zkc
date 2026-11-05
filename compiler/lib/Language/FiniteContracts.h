#ifndef ZKC_LANGUAGE_FINITECONTRACTS_H
#define ZKC_LANGUAGE_FINITECONTRACTS_H
#include "Semantics.h"
namespace zkc::language::detail {
class HelperResults;
/// A fold step receives state before its item; collect and predicates do not.
constexpr unsigned finiteItemInput(FiniteApplication::Kind kind,
                                   bool predicate = false) {
  return kind == FiniteApplication::Kind::Fold && !predicate ? 1 : 0;
}
/// Check scoped invocation restrictions over an already elaborated body.
/// Domain arguments and eager capture snapshots are fixed before this pass;
/// its provenance facts are reconstructed, never accepted as annotations.
bool checkFiniteContracts(Semantics &, llvm::ArrayRef<Declaration>,
                          const Declaration &, const Body &, HelperResults &);
/// Propagate requirements through a closed helper graph. Callees must already
/// carry their checked requirements. Residual facts may mention only immutable
/// mathematical input places; entry execution never acquires assumptions.
/// Root assumptions are supplied separately so replay can borrow the candidate
/// declaration without trusting its derived preconditions or copying its body.
std::optional<std::vector<DataPrecondition>> deriveDataPreconditions(
    Semantics &, llvm::ArrayRef<Declaration>, const Declaration &, const Body &,
    llvm::ArrayRef<DataPrecondition> rootAssumptions, bool allowAdditional);
} // namespace zkc::language::detail
#endif
