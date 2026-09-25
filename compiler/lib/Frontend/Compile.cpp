#include "zkc/Frontend/Compile.h"
#include "Model/Module.h"
#include "zkc/Frontend/Analysis.h"
namespace zkc::frontend {
llvm::Expected<source::Content> lower(const CheckedModule &module) {
  if (!module.model->finalized)
    llvm::report_fatal_error("checked analysis has no finalized source");
  return *module.model->finalized;
}
llvm::Expected<source::Content> compileProject(const ProjectInput &input) {
  return analyzeProject(input).lower();
}
} // namespace zkc::frontend
