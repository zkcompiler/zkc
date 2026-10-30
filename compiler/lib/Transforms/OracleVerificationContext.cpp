#include "OracleVerificationContext.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Support/Refusal.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
Expected<OracleVerificationContext>
OracleVerificationContext::read(ModuleOp module) {
  if (!module || !hasSingleElement(module.getBody()->getOperations()))
    return error("oracle-verification-source");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol ||
      failed(zkc::admitStage(module)))
    return error("oracle-verification-source");
  auto closure = readSourceExecutionClosure(unit);
  if (!closure)
    return closure.takeError();
  return OracleVerificationContext(module, unit, std::move(*closure));
}
} // namespace zkc::protocol
