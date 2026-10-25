#include "../HelperNormalization.h"
#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::kernel {
bool chargeCopy(Operation *body, uint64_t &remaining,
                std::optional<CapacityCause> *capacity) {
  auto walk = body->walk([&](Operation *op) {
    uint64_t cost = 1 + op->getNumOperands() + op->getNumResults();
    if (cost > remaining) {
      if (capacity)
        *capacity =
            CapacityCause{WorkOwner::AlgorithmExpansion, cost, remaining};
      return WalkResult::interrupt();
    }
    remaining -= cost;
    return WalkResult::advance();
  });
  return !walk.wasInterrupted();
}
namespace {
// This is structural substitution only: no folding, DCE, polynomial rewrite,
// recipe selection or numerical emission. Every unused operation is copied.
class Readback {
  SymbolTable symbols;
  llvm::DenseSet<Operation *> active;
  uint64_t &remaining;
  OpBuilder builder;
  bool charge(Operation *op) {
    uint64_t cost = 1 + op->getNumOperands() + op->getNumResults();
    if (cost > remaining)
      return false;
    remaining -= cost;
    return true;
  }

public:
  Readback(Operation *owner, uint64_t &remaining)
      : symbols(owner), remaining(remaining), builder(owner->getContext()) {}
  FailureOr<SmallVector<Value>> copy(func::FuncOp source, ValueRange arguments,
                                     Block *target) {
    if (!source || !source.getBody().hasOneBlock() ||
        source.getNumArguments() != arguments.size() || active.size() >= 64 ||
        !active.insert(source).second || !charge(source))
      return failure();
    IRMapping values;
    for (auto [formal, actual] : zip(source.getArguments(), arguments)) {
      if (formal.getType() != actual.getType())
        return failure();
      values.map(formal, actual);
    }
    for (auto &op : source.front().without_terminator()) {
      if (!charge(&op) || op.getNumRegions())
        return failure();
      SmallVector<Value> inputs;
      for (auto operand : op.getOperands()) {
        auto actual = values.lookupOrNull(operand);
        if (!actual)
          return failure();
        inputs.push_back(actual);
      }
      if (auto call = dyn_cast<func::CallOp>(op)) {
        auto callee = symbols.lookup<func::FuncOp>(call.getCallee());
        auto outputs = copy(callee, inputs, target);
        if (failed(outputs) || outputs->size() != call.getNumResults())
          return failure();
        values.map(call.getResults(), *outputs);
      } else {
        if (!mathematical::isTotal(&op))
          return failure();
        builder.setInsertionPointToEnd(target);
        builder.clone(op, values);
      }
    }
    auto returned = dyn_cast<func::ReturnOp>(source.front().back());
    if (!returned || !charge(returned))
      return failure();
    SmallVector<Value> results;
    for (auto value : returned.getOperands()) {
      auto actual = values.lookupOrNull(value);
      if (!actual)
        return failure();
      results.push_back(actual);
    }
    active.erase(source);
    return results;
  }
};
} // namespace
OwningOpRef<func::FuncOp> exactReadback(func::FuncOp source, Operation *owner,
                                        uint64_t &remaining) {
  if (!source || !source.getBody().hasOneBlock())
    return {};
  OwningOpRef<func::FuncOp> snapshot(
      cast<func::FuncOp>(source->cloneWithoutRegions()));
  auto *target = snapshot->addEntryBlock();
  auto values =
      Readback(owner, remaining).copy(source, target->getArguments(), target);
  if (failed(values))
    return {};
  OpBuilder builder(source.getContext());
  builder.setInsertionPointToEnd(target);
  func::ReturnOp::create(builder, source.getLoc(), *values);
  return snapshot;
}
// Normalization is an explicit checked edge, separate from exact substitution.
// The original unit and all of its dependency/source roots stay immutable.
OwningOpRef<mlir::ModuleOp>
normalizeUnit(mlir::ModuleOp unit, uint64_t &remaining,
              llvm::DenseSet<Operation *> &polynomialGenerated,
              std::optional<CapacityCause> *capacity) {
  auto entry = mathematical::getComputationEntry(unit);
  if (!entry || !entry.getBody().hasOneBlock())
    return {};
  if (!chargeCopy(unit, remaining, capacity))
    return {};
  mathematical::CheckedHelperNormalizations helpers(unit);
  if (failed(helpers.prepare(entry)))
    return {};
  auto normalized = helpers.lookup(entry);
  if (!normalized)
    return {};
  for (auto &op : normalized.front().without_terminator())
    if (!mathematical::isTotal(&op) || isa<func::CallOp>(op) ||
        poly::isPolynomialNormalizationOperation(&op))
      return {};

  // Clone each selected standard declaration once, retaining unit/function
  // attributes, positional ports and dependency symbols in their original
  // owner. Only the helper cache proposes and checks normalized bodies.
  OwningOpRef<mlir::ModuleOp> scratch(
      cast<mlir::ModuleOp>(unit->cloneWithoutRegions()));
  scratch->getBodyRegion().emplaceBlock();
  OpBuilder builder(unit.getContext());
  builder.setInsertionPointToEnd(scratch->getBody());
  IRMapping mapping;
  for (auto &declaration : *unit.getBody()) {
    auto checked = helpers.lookup(&declaration);
    auto *selected = checked ? checked.getOperation() : &declaration;
    if (!chargeCopy(selected, remaining, capacity))
      return {};
    builder.clone(*selected, mapping);
  }
  // Publish only identities owned by the completed proposal. A refused copy
  // leaves both the immutable source and the caller's evidence set unchanged.
  for (auto &op : normalized.front().without_terminator()) {
    if (helpers.isPolynomialGenerated(&op))
      polynomialGenerated.insert(mapping.lookup(&op));
  }
  return scratch;
}
} // namespace zkc::kernel
