#include "zkc/Frontend/Compile.h"
#include "Model/Checked.h"
#include "zkc/Frontend/Analysis.h"
namespace zkc::frontend {
llvm::Expected<source::Content> lower(const CheckedModule &module) {
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
