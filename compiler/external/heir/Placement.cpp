#include "Admission.h"
#include "lib/Dialect/Polynomial/Transforms/Passes.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Transforms/Passes.h"

namespace zkc::heir {
mlir::FailureOr<mlir::OwningOpRef<mlir::ModuleOp>>
placeTransforms(mlir::ModuleOp source) {
  // Reject outside the supported profile before invoking upstream analyses.
  if (mlir::failed(compareArithmetic(source, source)))
    return mlir::failure();
  mlir::OwningOpRef<mlir::ModuleOp> candidate(source.clone());
  mlir::PassManager passes(source.getContext());
  passes.addNestedPass<mlir::func::FuncOp>(
      mlir::heir::polynomial::createPolyMulToNTT());
  passes.addPass(mlir::heir::polynomial::createAttachNTTRoots());
  passes.addPass(mlir::createCanonicalizerPass());
  passes.addPass(mlir::createCSEPass());
  if (mlir::failed(passes.run(*candidate)) ||
      mlir::failed(compareArithmetic(source, *candidate)))
    return mlir::failure();
  return candidate;
}
} // namespace zkc::heir
