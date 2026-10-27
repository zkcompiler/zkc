#include "Bindings.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecDialect.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Kernel.h"
#include "zkc/Transforms/LinearContraction.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Transforms/Protocol.h"
#include "llvm/ADT/DenseMap.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
LogicalResult lowerPhysical(
    ModuleOp module, ArrayRef<std::pair<std::string, std::string>> selections,
    bool linearContractions, LinearContractionStats *stats, bool releaseStorage,
    ArrayRef<target::FunctionPortSelection> functionPorts,
    MathematicalSelectionPolicy numericalPolicy,
    const target::CpuTarget &cpuTarget) {
  if (stats)
    *stats = {};
  module.getContext()->getOrLoadDialect<zkc::exec::ExecDialect>();
  module.getContext()->getOrLoadDialect<zkc::runtime::RuntimeDialect>();
  if (failed(verify(module)))
    return failure();
  if (!llvm::hasSingleElement(*module.getBody()))
    return diagnostics::emit(module.emitError(), "interactive-module-count");
  auto root =
      dyn_cast<zkc::protocol_ir::ProtocolModuleOp>(&module.getBody()->front());
  if (!root || !zkc::protocol_ir::isExecutableProfile(root.getProfile()))
    return diagnostics::emit(module.emitError(), "interactive-module");
  // For executable profiles, ProtocolModuleOp::verifyRegions already reads
  // and admits the execution model. Keep the wrapper/profile checks here
  // without reconstructing and discarding the same admitted records.
  if (root.getProfile() != zkc::protocol_ir::Profile::Exec)
    return diagnostics::emit(root.emitError(), "interactive-physical-stage");
  return lowerBoundPhysical(module, selections, linearContractions, stats,
                            releaseStorage, functionPorts, numericalPolicy,
                            cpuTarget);
}
namespace {
struct PhysicalPass : PassWrapper<PhysicalPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(PhysicalPass)
  PhysicalPass(protocol::Assignments selected, bool linear, bool release,
               LinearContractionStats *output,
               ArrayRef<target::FunctionPortSelection> functionPorts,
               MathematicalSelectionPolicy numericalPolicy,
               const target::CpuTarget &cpuTarget)
      : selections(std::move(selected)), output(output),
        functionPorts(functionPorts), cpuTarget(cpuTarget) {
    linearContractions = linear;
    releaseStorage = release;
    optimizeFinite = numericalPolicy.finiteBulk;
    fuseVectorReductions = numericalPolicy.vectorReductionFusion;
    fuseCollectFold = numericalPolicy.collectFoldFusion;
    calculationBatching = numericalPolicy.calculationBatching;
  }
  PhysicalPass(const PhysicalPass &other)
      : PassWrapper(other), selections(other.selections), output(other.output),
        functionPorts(other.functionPorts), cpuTarget(other.cpuTarget) {}
  protocol::Assignments selections;
  LinearContractionStats *output;
  SmallVector<target::FunctionPortSelection> functionPorts;
  target::CpuTarget cpuTarget;
  Option<bool> linearContractions{
      *this, "linear-contractions",
      llvm::cl::desc("Select local all-uses depth-one diagonal contractions"),
      llvm::cl::init(false)};
  Option<bool> releaseStorage{
      *this, "release-storage",
      llvm::cl::desc("Release discardable local storage after last use"),
      llvm::cl::init(false)};
  Option<bool> optimizeFinite{
      *this, "optimize-finite", llvm::cl::init(true),
      llvm::cl::desc("Select checked bulk finite realizations")};
  Option<bool> fuseVectorReductions{
      *this, "fuse-vector-reductions", llvm::cl::init(false),
      llvm::cl::desc("Fuse admitted vector maps and reductions")};
  Option<bool> fuseCollectFold{
      *this, "fuse-collect-fold", llvm::cl::init(false),
      llvm::cl::desc("Compose total collect and ordered fold traversals")};
  Option<bool> calculationBatching{
      *this, "calculation-batching", llvm::cl::init(true),
      llvm::cl::desc("Realize the selected calculation schedule")};
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
    registry.insert<zkc::exec::ExecDialect, zkc::runtime::RuntimeDialect>();
    kernel::createLowerKernelsPass()->getDependentDialects(registry);
  }
  void runOnOperation() final {
    LinearContractionStats stats;
    if (failed(lowerPhysical(getOperation(), selections, linearContractions,
                             &stats, releaseStorage, functionPorts,
                             {optimizeFinite, fuseVectorReductions,
                              fuseCollectFold, calculationBatching},
                             cpuTarget))) {
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
createSelectPhysicalPass(protocol::Assignments selections,
                         bool linearContractions, bool releaseStorage,
                         LinearContractionStats *statistics,
                         ArrayRef<target::FunctionPortSelection> functionPorts,
                         MathematicalSelectionPolicy numericalPolicy,
                         const target::CpuTarget &cpuTarget) {
  return std::make_unique<PhysicalPass>(
      std::move(selections), linearContractions, releaseStorage, statistics,
      functionPorts, numericalPolicy, cpuTarget);
}
} // namespace zkc::protocol
