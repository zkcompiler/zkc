#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
namespace {
Error verifyExportSubject(Operation *root) {
  if (!root)
    return error("interactive-malformed-ir");
  Error refusals = Error::success();
  ScopedDiagnosticHandler capture(
      root->getContext(), [&](Diagnostic &diagnostic) {
        if (diagnostic.getSeverity() == DiagnosticSeverity::Error)
          for (const auto &refusal : diagnostics::refusals(diagnostic))
            refusals = joinErrors(std::move(refusals),
                                  error(refusal.code, refusal.detail));
        // Preserve the caller's diagnostic handling and location information.
        return failure();
      });
  if (failed(zkc::admitStage(root))) {
    if (refusals)
      return refusals;
    return error("interactive-malformed-ir");
  }
  if (refusals)
    return refusals;
  return Error::success();
}
} // namespace
Expected<program::Participants> exportProgram(Operation *root) {
  if (auto refusal = verifyExportSubject(root))
    return refusal;
  return readExecutionModel(root);
}
Expected<json::Value> exportModule(Operation *root) {
  if (auto refusal = verifyExportSubject(root))
    return refusal;
  auto *subject = root;
  if (auto module = dyn_cast<ModuleOp>(root)) {
    if (!llvm::hasSingleElement(*module.getBody()))
      return error("interactive-module-count");
    subject = &module.getBody()->front();
  }
  // Bytes publish a physical program. A valid logical scoped body may still
  // have source return boundaries, so check its phase before native decoding.
  if (auto unit = dyn_cast<protocol_ir::ProtocolModuleOp>(subject))
    if (unit.getProfile() != protocol_ir::Profile::Physical)
      return error("native-physical-required");
  auto value = readExecutionModel(root);
  if (!value)
    return value.takeError();
  if (value->stage != program::Participants::Stage::Physical)
    return error("native-physical-required");
  auto encoded = program::encode(*value);
  auto checked = verifyProgramArtifact(root, printJson(encoded));
  if (!checked)
    return checked.takeError();
  return encoded;
}
} // namespace zkc::protocol
