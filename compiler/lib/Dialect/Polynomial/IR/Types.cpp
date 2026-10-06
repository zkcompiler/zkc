#include "../../DomainVerification.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialOps.h"
using namespace mlir;
using namespace llvm;
namespace zkc {
static bool digits(StringRef n) {
  return !n.empty() && n.size() <= 1024 &&
         (n.size() == 1 || n.front() != '0') &&
         llvm::all_of(n, [](char c) { return c >= '0' && c <= '9'; });
}
LogicalResult
zkc::poly::PointType::verify(llvm::function_ref<InFlightDiagnostic()> e,
                             StringRef d) {
  return verifyFieldDomain(e, d);
}
LogicalResult
zkc::poly::TableType::verify(llvm::function_ref<InFlightDiagnostic()> e,
                             StringRef d, StringRef n) {
  if (failed(verifyFieldDomain(e, d)))
    return failure();
  if (!digits(n))
    return diagnostics::emit(e(), "invalid-original-rank");
  return success();
}
LogicalResult
zkc::poly::ResidualType::verify(llvm::function_ref<InFlightDiagnostic()> e,
                                StringRef d, StringRef n) {
  return zkc::poly::TableType::verify(e, d, n);
}
} // namespace zkc
