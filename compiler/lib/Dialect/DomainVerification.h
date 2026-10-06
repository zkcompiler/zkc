#ifndef ZKC_DIALECT_DOMAIN_VERIFICATION_H
#define ZKC_DIALECT_DOMAIN_VERIFICATION_H
#include "zkc/Contracts/Domains.h"
#include "zkc/Dialect/Diagnostics.h"
namespace zkc {
inline mlir::LogicalResult
verifyFieldDomain(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
                  llvm::StringRef d) {
  if (d != "f2" && d != "f7" && d != "reference.scalar" &&
      protocol::installedDomains().identitySort(d) != "Field")
    return diagnostics::emit(emit(), "unknown-domain");
  return mlir::success();
}
} // namespace zkc
#endif
