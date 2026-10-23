#include "ImplementationPlan.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Mathematical.h"

using namespace llvm;
using namespace mlir;
using namespace zkc::protocol;
namespace zkc::target {
namespace {
std::string structure(ModuleOp module) {
  std::string result;
  raw_string_ostream out(result);
  module->print(out, OpPrintingFlags().printGenericOpForm().enableDebugInfo());
  return result;
}
SmallVector<const void *> identities(ModuleOp module) {
  SmallVector<const void *> result;
  module->walk<WalkOrder::PreOrder>([&](Operation *op) {
    result.push_back(op);
    for (auto &region : op->getRegions())
      for (auto &block : region) {
        result.push_back(&block);
        for (auto arg : block.getArguments())
          result.push_back(arg.getAsOpaquePointer());
      }
    for (auto value : op->getResults())
      result.push_back(value.getAsOpaquePointer());
  });
  return result;
}
} // namespace

ImplementationPlan::ImplementationPlan(
    ModuleOp module, ArrayRef<std::pair<std::string, std::string>> selections,
    MathematicalSelectionPolicy policy)
    : source(module), contents(structure(module)),
      addresses(identities(module)),
      requests(selections.begin(), selections.end()), policy(policy) {}

Error ImplementationPlan::checkInput(ModuleOp module) const {
  // Saved addresses are opaque identity witnesses, never dereferenced. A
  // structurally equal replacement is not the original selected source.
  if (module != source || identities(module) != addresses ||
      structure(module) != contents)
    return error("binding-stale-selection");
  return Error::success();
}
ModuleOp ImplementationPlan::subject(ModuleOp original) const {
  return realization ? *realization : original;
}
Error ImplementationPlan::verifyRealization(ModuleOp original) const {
  if (auto e = checkInput(original))
    return e;
  if (failed(mlir::verify(original)))
    return error("binding-operation");
  if (realization && failed(mathematical::verifyNumericalLowering(
                         original, *realization, policy, requests)))
    return error("numerical-lowering-correspondence");
  return Error::success();
}
} // namespace zkc::target
