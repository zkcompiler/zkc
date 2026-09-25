#ifndef ZKC_FRONTEND_COMPILE_H
#define ZKC_FRONTEND_COMPILE_H
#include "zkc/Frontend/Input.h"
#include "zkc/Frontend/Module.h"
#include "llvm/Support/Error.h"
namespace zkc::frontend {
/// Lower a checked source module; PIR admission remains independent.
llvm::Expected<source::Content> lower(const CheckedModule &);
llvm::Expected<source::Content> compileProject(const ProjectInput &);
/// Resolve a separate descriptor using the same immutable source project.
/// Explicit closed symbols remain low-level selectors and are checked by PIR.
llvm::Expected<source::Construction> bindConstruction(const ProjectInput &,
                                                      const source::Module &,
                                                      source::Construction);
} // namespace zkc::frontend
#endif
