#include "../../DomainVerification.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
using namespace mlir;
using namespace llvm;
namespace zkc::algebra {
LogicalResult FieldType::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                                StringRef domain) {
  return verifyFieldDomain(emit, domain);
}
} // namespace zkc::algebra
