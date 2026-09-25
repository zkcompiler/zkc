#ifndef ZKC_FRONTEND_COMPILE_H
#define ZKC_FRONTEND_COMPILE_H
#include "zkc/Frontend/Input.h"
#include "zkc/Frontend/Module.h"
#include "llvm/Support/Error.h"
namespace zkc::frontend {
/// Lower a checked source module; PIR admission remains independent.
llvm::Expected<source::Content> lower(const CheckedModule &);
llvm::Expected<source::Content> compileProject(const ProjectInput &);
/// Bind a descriptor to the checked snapshot and its retained name graph.
/// Explicit closed symbols remain low-level selectors and are checked by PIR.
llvm::Expected<source::Construction> bindConstruction(const CheckedModule &,
                                                      source::Construction);
} // namespace zkc::frontend
#endif
