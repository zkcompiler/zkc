#ifndef ZKC_DIALECT_EXEC_EXECUTION_DEFINITIONS_H
#define ZKC_DIALECT_EXEC_EXECUTION_DEFINITIONS_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Analysis/TotalClosure.h"
#include "zkc/Dialect/Exec/IR/ExecTypes.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/StringSet.h"

namespace zkc::protocol::detail {
// Select a checking owner, never grant admission from an annotation. Malformed
// or partial execution signatures must not escape into the mathematical set.
inline bool isScopedExecutionFunction(mlir::func::FuncOp function) {
  using namespace mlir;
  if (function->hasAttr("runtime.origin") ||
      function->hasAttr("runtime.region"))
    return true;
  auto raw = function->getAttrOfType<TypeAttr>("function_type");
  auto type = raw ? dyn_cast<FunctionType>(raw.getValue()) : FunctionType();
  if (!type)
    return true;
  auto executionType = [](Type type) {
    return isa<runtime::ScopeType, runtime::TransferType, exec::OutcomeType,
               exec::StopType>(type);
  };
  return llvm::any_of(type.getInputs(), executionType) ||
         llvm::any_of(type.getResults(), executionType);
}

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
