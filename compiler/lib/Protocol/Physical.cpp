#include "BindingPhysical.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Dialect/Builders.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/LinearContraction.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Transforms/Protocol.h"
#include "zkc/Translation/Protocol.h"
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
  module.getContext()->getOrLoadDialect<PlanDialect>();
  if (failed(verify(module)))
    return failure();
  auto candidate = exportSource(module);
  if (!candidate)
    return module.emitError() << toString(candidate.takeError());
  if (auto e = admit(*candidate, true))
    return module.emitError() << toString(std::move(e));
  auto root = cast<ProtocolModuleOp>(&module.getBody()->front());
  if (root.getStage() != "logical")
    return root.emitError("interactive-physical-stage");
  if (failed(lowerBoundPhysical(module, selections, linearContractions, stats)))
    return failure();
  return releaseStorage ? releaseLocalStorage(module) : success();
}
namespace {
struct PhysicalPass : PassWrapper<PhysicalPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(PhysicalPass)
  PhysicalPass(source::Assignments selected, bool linear, bool release)
      : selections(std::move(selected)) {
    linearContractions = linear;
    releaseStorage = release;
  }
  PhysicalPass(const PhysicalPass &other)
      : PassWrapper(other), selections(other.selections) {}
  source::Assignments selections;
  Option<bool> linearContractions{
      *this, "linear-contractions",
      llvm::cl::desc("Select local all-uses depth-one diagonal contractions"),
      llvm::cl::init(false)};
  Option<bool> releaseStorage{
      *this, "release-storage",
      llvm::cl::desc("Release discardable local storage after last use"),
      llvm::cl::init(false)};
  Statistic eligible{this, "linear-contraction-eligible",
                     "Eligible local pairs"};
  Statistic selected{this, "linear-contraction-selected",
                     "Selected local pairs"};
  Statistic selectedProducers{this, "linear-contraction-selected-producers",
                              "Atomically selected local producers"};
  StringRef getArgument() const final { return "zkc-plan-participants"; }
  StringRef getDescription() const final {
    return "Select installed kernels and physical value representations for "
           "role programs";
  }
  void getDependentDialects(DialectRegistry &registry) const final {
    registry.insert<PlanDialect>();
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
    if (linearContractions)
      printLinearContractionStats(stats, llvm::errs());
  }
};
} // namespace
std::unique_ptr<Pass> createPlanParticipantsPass(source::Assignments selections,
                                                 bool linearContractions,
                                                 bool releaseStorage) {
  return std::make_unique<PhysicalPass>(std::move(selections),
                                        linearContractions, releaseStorage);
}
} // namespace zkc::protocol
