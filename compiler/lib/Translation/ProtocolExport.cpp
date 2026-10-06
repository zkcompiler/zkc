#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
Expected<source::Content> exportSource(Operation *root) {
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
  auto value = exportSource(root);
  if (!value)
    return value.takeError();
  if (const auto *participants = std::get_if<source::Participants>(&*value))
    if (source::isProgram(participants->contract) &&
        participants->stage != source::Participants::Stage::Physical)
      return error("native-physical-required");
  auto encoded = source::encode(*value);
  if (const auto *participants = std::get_if<source::Participants>(&*value))
    if (source::isProgram(participants->contract)) {
      if (auto e = verifyProgramArtifact(root, printJson(encoded)))
        return std::move(e);
    }
  return encoded;
}
} // namespace zkc::protocol
