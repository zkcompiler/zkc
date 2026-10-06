#include "../../DomainVerification.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
using namespace mlir;
using namespace llvm;
namespace zkc {
LogicalResult
zkc::algebra::FieldType::verify(llvm::function_ref<InFlightDiagnostic()> e,
                                StringRef d) {
  return verifyFieldDomain(e, d);
}
LogicalResult zkc::algebra::FixedVectorType::verify(
    llvm::function_ref<InFlightDiagnostic()> emit, Type element,
    uint64_t length) {
  auto logical = protocol::encodeBoundType(element, false);
  if (!logical) {
    consumeError(logical.takeError());
    return emit() << "fixed vector requires an admitted logical element type";
  }
  auto type = protocol::applyBoundType(
      "fixed_vector", {logical->spelling(), std::to_string(length)});
  if (!type) {
    consumeError(type.takeError());
    return emit() << "fixed vector exceeds logical type limits";
  }
  return success();
}
} // namespace zkc
