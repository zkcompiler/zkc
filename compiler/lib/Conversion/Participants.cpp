#include "Bindings.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/LinearContraction.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Transforms/Protocol.h"
#include "llvm/ADT/DenseMap.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
LogicalResult
lowerPhysical(ModuleOp module,
              ArrayRef<std::pair<std::string, std::string>> selections,
              bool linearContractions, LinearContractionStats *stats,
              bool releaseStorage) {
  if (stats)
    *stats = {};
  module.getContext()->getOrLoadDialect<zkc::plan::PlanDialect>();
  if (failed(verify(module)))
    return failure();
  auto candidate = readExecutionModel(module);
  if (!candidate)
    return diagnostics::emit(module.emitError(), candidate.takeError());
  if (auto e = admit(*candidate, true))
    return diagnostics::emit(module.emitError(), std::move(e));
  auto root =
      cast<zkc::protocol_ir::ProtocolModuleOp>(&module.getBody()->front());
  if (root.getProfile() != zkc::protocol_ir::Profile::Exec)
    return diagnostics::emit(root.emitError(), "interactive-physical-stage");
  OwningOpRef<ModuleOp> selected(cast<ModuleOp>(module->clone()));
  LinearContractionStats selectedStats;
  if (failed(lowerBoundPhysical(*selected, selections, linearContractions,
                                &selectedStats)) ||
      (releaseStorage && failed(releaseLocalStorage(*selected))) ||
      failed(verify(*selected)))
    return failure();
  module.getBodyRegion().takeBody(selected->getBodyRegion());
  if (stats)
    *stats = selectedStats;
  return success();
}
namespace {
struct PhysicalPass : PassWrapper<PhysicalPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(PhysicalPass)
  PhysicalPass(source::Assignments selected, bool linear, bool release,
               LinearContractionStats *output)
      : selections(std::move(selected)), output(output) {
    linearContractions = linear;
    releaseStorage = release;
  }
  PhysicalPass(const PhysicalPass &other)
      : PassWrapper(other), selections(other.selections), output(other.output) {
  }
  source::Assignments selections;
  LinearContractionStats *output;
  Option<bool> linearContractions{
      *this, "linear-contractions",
      llvm::cl::desc("Select local all-uses depth-one diagonal contractions"),
      llvm::cl::init(false)};
  Option<bool> releaseStorage{
      *this, "release-storage",
      llvm::cl::desc("Release discardable local storage after last use"),
      llvm::cl::init(false)};
  Statistic eligible{this, "linear-contraction-eligible",
                     "Semantic all-uses contraction pairs"};
  Statistic selected{this, "linear-contraction-selected",
                     "Selected local pairs"};
  Statistic selectedProducers{this, "linear-contraction-selected-producers",
                              "Atomically selected local producers"};
  StringRef getArgument() const final { return "zkc-select-physical"; }
  StringRef getDescription() const final {
    return "Select installed kernels and physical value representations for "
           "role programs";
  }
  void getDependentDialects(DialectRegistry &registry) const final {
    registry.insert<zkc::plan::PlanDialect>();
  }
  void runOnOperation() final {
    LinearContractionStats stats;
    if (failed(lowerPhysical(getOperation(), selections, linearContractions,
                             &stats, releaseStorage))) {
      signalPassFailure();
      return;
    }
    eligible += stats.eligiblePairs;
    selected += stats.selectedPairs;
    selectedProducers += stats.selectedProducers;
    if (output)
      *output = stats;
    else if (linearContractions)
      printLinearContractionStats(stats, llvm::errs());
  }
};
} // namespace
std::unique_ptr<Pass>
createSelectPhysicalPass(source::Assignments selections,
                         bool linearContractions, bool releaseStorage,
                         LinearContractionStats *statistics) {
  return std::make_unique<PhysicalPass>(
      std::move(selections), linearContractions, releaseStorage, statistics);
}
} // namespace zkc::protocol
