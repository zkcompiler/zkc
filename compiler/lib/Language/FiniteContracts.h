#ifndef ZKC_LANGUAGE_FINITECONTRACTS_H
#define ZKC_LANGUAGE_FINITECONTRACTS_H
#include "Semantics.h"
namespace zkc::language::detail {
/// Check scoped invocation restrictions over an already elaborated body.
/// Domain arguments and eager capture snapshots are fixed before this pass;
/// its provenance facts are reconstructed, never accepted as annotations.
bool checkFiniteContracts(Semantics &, llvm::ArrayRef<Declaration>,
                          const Declaration &, const Body &);
/// Propagate requirements through a closed helper graph. Callees must already
/// carry their checked requirements. Residual facts may mention only immutable
/// mathematical input places; entry execution never acquires assumptions.
std::optional<std::vector<DataPrecondition>>
deriveDataPreconditions(Semantics &, llvm::ArrayRef<Declaration>,
                        const Declaration &, const Body &,
                        bool allowAdditional);
} // namespace zkc::language::detail
#endif
