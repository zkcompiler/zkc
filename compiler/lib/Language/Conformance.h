#ifndef ZKC_LANGUAGE_CONFORMANCE_H
#define ZKC_LANGUAGE_CONFORMANCE_H
#include "Semantics.h"
namespace zkc::language::detail {
/// Compare ports, roles, service roots and scoped input contracts.
bool memberInputs(Semantics &, const Declaration &required,
                  const Declaration &provided, const Substitution &,
                  llvm::StringRef diagnostic);
/// Compare one universally quantified member after owner specialization. The
/// witness calls this with independently reconstructed headers and premises;
/// candidate requirements are goals, never assumptions.
bool memberContract(Semantics &, const Declaration &module,
                    const Declaration &interface, const Declaration &required,
                    const Declaration &provided, Substitution,
                    llvm::StringRef diagnostic);
} // namespace zkc::language::detail
#endif
