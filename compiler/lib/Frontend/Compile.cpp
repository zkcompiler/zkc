#include "zkc/Frontend/Compile.h"
#include "Model/Checked.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Mathematical/Placement.h"
#include "zkc/Support/Refusal.h"
namespace zkc::frontend {
llvm::Expected<source::Content> lower(const CheckedModule &module) {
  if (const auto &placement = module.completed->model.mathematicalPlacement) {
    const auto *actual =
        std::get_if<source::Module>(&module.completed->content);
    if (!actual)
      return error("math-placement-target-custody");
    auto digest = mathematical::placementTargetDigest(*actual);
    if (!digest)
      return digest.takeError();
    if (*digest != placement->witness.target)
      return error("math-placement-target-custody");
  }
  return module.completed->content;
}
llvm::Expected<source::Content> compileProject(const ProjectInput &input) {
  return compileProject(input, {});
}
llvm::Expected<source::Content> compileProject(const ProjectInput &input,
                                               WorkLimits limits) {
  return analyzeProject(input, limits).lower();
}
} // namespace zkc::frontend
