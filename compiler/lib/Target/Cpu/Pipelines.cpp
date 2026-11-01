#include "../../Compiler/MathematicalOptions.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Target/Cpu/Passes.h"
#include "zkc/Target/Cpu/Stages.h"
#include "zkc/Transforms/PipelineOptions.h"
#include "zkc/Transforms/Stages.h"
namespace zkc {
namespace {
using detail::MathematicalOptions;
template <typename Derived>
struct PhysicalOptions : MathematicalOptions<Derived> {
  using Base = MathematicalOptions<Derived>;
  typename Base::template Option<bool> linear{
      *this, "linear-contractions", llvm::cl::init(false),
      llvm::cl::desc("Select eligible local diagonal contractions")};
  typename Base::template Option<bool> release{
      *this, "release-storage", llvm::cl::init(false),
      llvm::cl::desc("Release local storage after last use")};
  typename Base::template Option<target::CpuTarget> cpuTarget{
      *this, "cpu-target", llvm::cl::init(target::CpuTarget{}),
      llvm::cl::desc("Compiled CPU installation restriction descriptor")};
  typename Base::template Option<std::string> bindings{
      *this, "bindings", llvm::cl::init("[]"),
      llvm::cl::desc("JSON pairs of binding symbol and implementation")};
  typename Base::template Option<std::string> functionPorts{
      *this, "function-ports", llvm::cl::init("[]"),
      llvm::cl::desc("JSON function port representation selections")};
  llvm::Expected<PhysicalPipelineOptions> normalized() const {
    PhysicalPipelineOptions options;
    auto selected = target::parseImplementationSelections(bindings);
    if (!selected)
      return selected.takeError();
    options.selections = std::move(*selected);
    auto ports = target::parseFunctionPortSelections(functionPorts);
    if (!ports)
      return ports.takeError();
    options.functionPorts.assign(ports->begin(), ports->end());
    options.mathematics = this->mathematics();
    options.linearContractions = linear;
    options.releaseStorage = release;
    options.cpuTarget = cpuTarget;
    return options;
  }
};
struct PhysicalOptionsOnly : PhysicalOptions<PhysicalOptionsOnly> {};
struct ParticipantOptions : PhysicalOptions<ParticipantOptions> {
  Option<bool> projectOnly{*this, "project-only", llvm::cl::init(false),
                           llvm::cl::desc("Stop after participant projection")};
  Option<bool> simplify{*this, "simplify", llvm::cl::init(true),
                        llvm::cl::desc("Simplify prepared mathematics")};
};
// The upstream convenience registration accepts only void builders. Use its
// checked registry API when semantic option normalization can refuse.
template <typename Options, typename Builder>
bool registerCheckedPipeline(llvm::StringRef name, llvm::StringRef description,
                             Builder build) {
  mlir::registerPassPipeline(
      name, description,
      [build](
          mlir::OpPassManager &pm, llvm::StringRef text,
          llvm::function_ref<mlir::LogicalResult(const llvm::Twine &)> error) {
        Options options;
        std::string diagnostics;
        llvm::raw_string_ostream stream(diagnostics);
        if (mlir::failed(options.parseFromString(text, stream)))
          return error(diagnostics);
        auto selected = options.normalized();
        if (!selected)
          return error(llvm::toString(selected.takeError()));
        build(pm, options, *selected);
        return mlir::success();
      },
      [](llvm::function_ref<void(const mlir::detail::PassOptions &)> visit) {
        visit(Options());
      });
  return true;
}
} // namespace
void registerCpuPipelines() {
  static const bool physical = registerCheckedPipeline<PhysicalOptionsOnly>(
      "zkc-physical-pipeline", "Select the compiled physical installation",
      [](mlir::OpPassManager &pm, const PhysicalOptionsOnly &,
         const PhysicalPipelineOptions &selected) {
        buildPhysicalPipeline(pm, selected);
      });
  static const bool participants = registerCheckedPipeline<ParticipantOptions>(
      "zkc-participant-pipeline", "Project and plan an interactive protocol",
      [](mlir::OpPassManager &pm, const ParticipantOptions &options,
         const PhysicalPipelineOptions &selected) {
        buildProjectionPipeline(pm, options.simplify, options.mathematics());
        if (!options.projectOnly) {
          buildClosedExecutionPipeline(pm, false, false, options.mathematics());
          buildPhysicalPipeline(pm, selected);
        }
      });
  (void)physical;
  (void)participants;
}
} // namespace zkc
