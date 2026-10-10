#ifndef ZKC_TRANSLATION_LANGUAGE_H
#define ZKC_TRANSLATION_LANGUAGE_H
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Language/Project.h"

namespace zkc::language {
struct SourceLocation {
  unsigned line, column;
  Span source;
};
/// Direct, unsimplified Protocol IR. The caller supplies native dialects.
llvm::Expected<std::string>
emitOriginal(const ClosedEntry &, mlir::MLIRContext &, const Limits & = {});
struct Correspondence {
  uint64_t declarations = 0, operations = 0;
  std::vector<SourceLocation> locations;
};
/// Verify the module once, then compare actual SSA with the checked source.
/// Locations come from compared operations in the reparsed original. No
/// mutation, re-emission, canonicalization, or executable lowering occurs in
/// this check.
llvm::Expected<Correspondence>
compareOriginal(const ClosedEntry &, mlir::ModuleOp, const Limits & = {});
} // namespace zkc::language
#endif
