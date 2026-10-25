#ifndef ZKC_TRANSLATION_EXECUTION_DEFINITIONS_H
#define ZKC_TRANSLATION_EXECUTION_DEFINITIONS_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/StringSet.h"

namespace zkc::protocol::detail {
// Formation shared by the two independent body checks. Do not verify the
// enclosing operation: its region verifier may be the consumer of this API.
// Every direct Func is owned, including dormant roots and outlined regions.
inline mlir::LogicalResult
verifyExecutionDefinitionScope(mlir::Operation *scope) {
  using namespace mlir;
  if (!scope || !scope->hasTrait<OpTrait::SymbolTable>() ||
      scope->getNumRegions() != 1 ||
      !llvm::hasSingleElement(scope->getRegion(0)))
    return failure();
  auto &definitions = scope->getRegion(0).front();
  llvm::StringSet<> symbols;
  unsigned count = 0, remaining = 1000000;
  // Reject collisions before any nested symbol user performs a lookup. Other
  // declarations cannot shadow or ambiguously select an execution definition.
  for (Operation &op : definitions) {
    if (++count > 4096)
      return failure();
    if (auto raw = op.getAttr(SymbolTable::getSymbolAttrName())) {
      auto name = dyn_cast<StringAttr>(raw);
      if (!name || name.getValue().empty() ||
          !symbols.insert(name.getValue()).second)
        return failure();
    }
  }
  for (Operation &op : definitions) {
    if (!isa<func::FuncOp, runtime::BindingOp>(op))
      continue;
    if (op.walk<WalkOrder::PreOrder>([&](Operation *nested) {
            if (!remaining || (nested != &op && nested->getNumRegions()))
              return WalkResult::interrupt();
            --remaining;
            return WalkResult::advance();
          }).wasInterrupted() ||
        failed(verify(&op)))
      return failure();
  }
  return success();
}
} // namespace zkc::protocol::detail
#endif
