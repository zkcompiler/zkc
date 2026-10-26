#ifndef ZKC_DIALECT_EXEC_EXECUTION_DEFINITIONS_H
#define ZKC_DIALECT_EXEC_EXECUTION_DEFINITIONS_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Analysis/TotalClosure.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecTypes.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/StringSet.h"

namespace zkc::protocol::detail {
// Formation shared by the two independent body checks. Do not verify the
// enclosing operation: its region verifier may be the consumer of this API.
// Every direct Func is owned, including dormant roots and outlined regions.
// Source functions can also belong to the independently admitted mathematical
// closure. This checks admission, not their correspondence to source equations.
inline mlir::LogicalResult
verifyExecutionDefinitionScope(mlir::Operation *scope, bool source = false) {
  using namespace mlir;
  if (!scope || !scope->hasTrait<OpTrait::SymbolTable>() ||
      scope->getNumRegions() != 1 ||
      !llvm::hasSingleElement(scope->getRegion(0)))
    return failure();
  auto &definitions = scope->getRegion(0).front();
  llvm::StringSet<> symbols;
  unsigned definitionsCount = 0, bindingsCount = 0, remaining = 1000000;
  // Reject collisions before any nested symbol user performs a lookup. Other
  // declarations cannot shadow or ambiguously select an execution definition.
  for (Operation &op : definitions) {
    if (!remaining)
      return failure();
    --remaining;
    // Bindings and callable/domain definitions have independent inventories.
    // Enclosing protocol metadata belongs to neither; collision inspection
    // still consumes the shared structural allowance.
    if ((isa<runtime::BindingOp>(op) && ++bindingsCount > 4096) ||
        (isa<func::FuncOp, data::DomainOp>(op) && ++definitionsCount > 4096))
      return failure();
    if (auto raw = op.getAttr(SymbolTable::getSymbolAttrName())) {
      auto name = dyn_cast<StringAttr>(raw);
      if (!name || name.getValue().empty() ||
          !symbols.insert(name.getValue()).second)
        return failure();
    }
  }
  for (Operation &op : definitions) {
    if (!isa<func::FuncOp, runtime::BindingOp>(op) &&
        !(source && isa<data::DomainOp>(op)))
      continue;
    auto function = dyn_cast<func::FuncOp>(op);
    bool scoped = !source || (function && isScopedExecutionFunction(function));
    if (op.walk<WalkOrder::PreOrder>([&](Operation *nested) {
            if (!remaining ||
                (scoped && nested != &op && nested->getNumRegions()))
              return WalkResult::interrupt();
            --remaining;
            return WalkResult::advance();
          }).wasInterrupted() ||
        failed(verify(&op)))
      return failure();
  }
  if (source) {
    SmallVector<func::FuncOp> mathematics;
    SmallVector<Operation *> mathematicalDefinitions;
    for (Operation &op : definitions) {
      if (isa<data::DomainOp>(op))
        mathematicalDefinitions.push_back(&op);
      if (auto function = dyn_cast<func::FuncOp>(op))
        if (!isScopedExecutionFunction(function)) {
          mathematics.push_back(function);
          mathematicalDefinitions.push_back(&op);
        }
    }
    if (!mathematics.empty()) {
      // These premises precede TotalClosure queries. The same live analysis
      // checks every retained mathematical body with one cumulative budget.
      if (failed(
              finite::verifyDefinitionClosure(scope, mathematicalDefinitions)))
        return failure();
      SymbolTableCollection symbols;
      mathematical::TotalClosure closure(scope, symbols);
      for (auto function : mathematics) {
        const mathematical::TotalSummary *summary;
        if (failed(closure.get(function, summary)))
          return failure();
      }
    }
  }
  return success();
}
} // namespace zkc::protocol::detail
#endif
