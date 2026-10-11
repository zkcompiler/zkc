#ifndef ZKC_TRANSFORMS_CHECKEDCANDIDATE_H
#define ZKC_TRANSFORMS_CHECKEDCANDIDATE_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "llvm/ADT/STLFunctionalExtras.h"

namespace zkc::mathematical {
/// A complete private proposal against an immutable admitted module. The
/// supplied reader must check the actual candidate, including formation and
/// unchanged surrounding declarations, without trusting producer matches.
/// Destroying an unpublished proposal leaves the original unchanged. External
/// occurrence state must be published only after this operation succeeds.
class CheckedCandidate {
  mlir::ModuleOp source;
  mlir::OwningOpRef<mlir::ModuleOp> candidate;
  bool published = false;

public:
  explicit CheckedCandidate(mlir::ModuleOp source)
      : source(source), candidate(mlir::cast<mlir::ModuleOp>(source->clone())) {
  }
  mlir::ModuleOp operator*() const { return *candidate; }
  mlir::ModuleOp *operator->() { return candidate.operator->(); }

  mlir::LogicalResult publish(
      llvm::function_ref<mlir::LogicalResult(mlir::ModuleOp, mlir::ModuleOp)>
          reader) {
    if (published)
      return diagnostics::emit(source.emitError(), "mathematical-candidate",
                               "candidate was already published");
    // This transaction replaces only the body. A changed module contract must
    // never be silently discarded while a reader checks a different subject.
    if (source->getAttrDictionary() != (*candidate)->getAttrDictionary())
      return diagnostics::emit(source.emitError(), "mathematical-candidate",
                               "candidate changed the module attributes");
    if (mlir::failed(reader(source, *candidate)))
      return mlir::failure();
    source.getBodyRegion().takeBody(candidate->getBodyRegion());
    published = true;
    return mlir::success();
  }
};
} // namespace zkc::mathematical
#endif
