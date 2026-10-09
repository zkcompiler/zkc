#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
Expected<program::Participants> exportProgram(Operation *root) {
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
  if (failed(verify(root))) {
    if (refusals)
      return std::move(refusals);
    return error("interactive-malformed-ir");
  }
  if (refusals)
    return std::move(refusals);
  return readExecutionModel(root);
}
Expected<json::Value> exportModule(Operation *root) {
  auto value = exportProgram(root);
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
