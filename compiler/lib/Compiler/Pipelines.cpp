#include "zkc/Compiler/Pipelines.h"
#include "MathematicalOptions.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Pass/PassRegistry.h"
#include "zkc/Transforms/Stages.h"

namespace zkc {
namespace {
using detail::MathematicalOptions;
struct PreparationOptions : MathematicalOptions<PreparationOptions> {
  Option<bool> simplify{*this, "simplify", llvm::cl::init(true),
                        llvm::cl::desc("Simplify prepared mathematics")};
};
struct ExecutionOptions : MathematicalOptions<ExecutionOptions> {
  Option<bool> simplify{*this, "simplify", llvm::cl::init(false),
                        llvm::cl::desc("Simplify participant mathematics")};
  Option<bool> fixPolynomials{
      *this, "fix-polynomials", llvm::cl::init(false),
      llvm::cl::desc("Distribute prefix fixing before demand lowering")};
};
} // namespace
void registerCompilerPipelines() {
  static mlir::PassPipelineRegistration<PreparationOptions> preparation(
      "zkc-preparation-pipeline", "Admit and prepare protocol mathematics",
      [](mlir::OpPassManager &pm, const PreparationOptions &options) {
        buildPreparationPipeline(pm, options.simplify, options.mathematics());
      });
  static mlir::PassPipelineRegistration<PreparationOptions> projection(
      "zkc-projection-pipeline", "Prepare and project protocol mathematics",
      [](mlir::OpPassManager &pm, const PreparationOptions &options) {
        buildProjectionPipeline(pm, options.simplify, options.mathematics());
      });
  static mlir::PassPipelineRegistration<ExecutionOptions> execution(
      "zkc-execution-pipeline", "Form ordered executable computations",
      [](mlir::OpPassManager &pm, const ExecutionOptions &options) {
        buildExecutionPipeline(pm, options.simplify, options.fixPolynomials,
                               options.mathematics());
      });
  static mlir::PassPipelineRegistration<ExecutionOptions> closed(
      "zkc-closed-execution-pipeline",
      "Form checked closed executable computations",
      [](mlir::OpPassManager &pm, const ExecutionOptions &options) {
        buildClosedExecutionPipeline(pm, options.simplify,
                                     options.fixPolynomials,
                                     options.mathematics());
      });
}
} // namespace zkc
