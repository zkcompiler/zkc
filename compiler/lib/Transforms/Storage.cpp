#include "../Conversion/Storage.h"
#include "../Target/PhysicalPlan.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Protocol.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
bool physical(ModuleOp module) {
  if (!hasSingleElement(*module.getBody()))
    return false;
  auto root =
      dyn_cast<protocol_ir::ProtocolModuleOp>(&module.getBody()->front());
  return root && root.getProfile() == protocol_ir::Profile::Physical;
}
} // namespace
LogicalResult verifyStoragePreserved(ModuleOp before, ModuleOp after) {
  if (failed(zkc::admitStage(before)) || failed(zkc::admitStage(after)))
    return failure();
  if (!physical(before) || !physical(after))
    return diagnostics::emit(after.emitError(), "storage-correspondence-stage");
  auto releases = readStorageReleases(before, after);
  if (!releases)
    return diagnostics::emit(after.emitError(), releases.takeError());
  if (auto e = target::validateStorage(before, {}, *releases))
    return diagnostics::emit(after.emitError(), std::move(e));
  return success();
}
LogicalResult releaseLocalStorage(ModuleOp module) {
  if (failed(zkc::admitStage(module)))
    return failure();
  if (!physical(module))
    return diagnostics::emit(module.emitError(), "interactive-release-context");
  auto releases = target::proposeStorage(module);
  if (!releases)
    return diagnostics::emit(module.emitError(), releases.takeError());
  if (releases->empty())
    return success();
  if (auto e = target::validateStorage(module, {}, *releases))
    return diagnostics::emit(module.emitError(), std::move(e));
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(module->clone()));
  if (auto e = applyStorage(*candidate, *releases))
    return diagnostics::emit(module.emitError(), std::move(e));
  if (failed(zkc::admitStage(*candidate)))
    return failure();
  if (auto e = verifyStorageMaterialization(module, *candidate, *releases))
    return diagnostics::emit(module.emitError(), std::move(e));
  module.getBodyRegion().takeBody(candidate->getBodyRegion());
  return success();
}
} // namespace zkc::protocol
