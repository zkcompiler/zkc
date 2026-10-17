#include "../HelperNormalization.h"
#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Transforms/Algorithms.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::kernel {
bool chargeCopy(Operation *body, uint64_t &remaining) {
  auto walk = body->walk([&](Operation *op) {
    uint64_t cost = 1 + op->getNumOperands() + op->getNumResults();
    if (cost > remaining)
      return WalkResult::interrupt();
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
OwningOpRef<protocol_ir::ProtocolModuleOp>
normalizationWorkspace(ModuleOp unit, local::FuncOp &localEntry,
                       uint64_t &remaining,
                       llvm::DenseSet<Operation *> &shareable) {
  auto entry = getEntry(unit);
  if (!entry || !entry.getBody().hasOneBlock())
    return {};
  if (!chargeCopy(unit, remaining))
    return {};
  mathematical::CheckedHelperNormalizations helpers(unit);
  if (failed(helpers.prepare(entry)))
    return {};
  auto normalized = helpers.lookup(entry);
  if (!normalized)
    return {};

  OpBuilder builder(unit.getContext());
  OperationState state(unit.getLoc(),
                       protocol_ir::ProtocolModuleOp::getOperationName());
  state.addAttribute("profile",
                     protocol_ir::ProfileAttr::get(unit.getContext(),
                                                   protocol_ir::Profile::Exec));
  state.addRegion();
  OwningOpRef<protocol_ir::ProtocolModuleOp> scratch(
      cast<protocol_ir::ProtocolModuleOp>(builder.create(state)));
  scratch->getBody().emplaceBlock();
  builder.setInsertionPointToEnd(&scratch->getBody().front());
  for (auto &declaration : unit.getBody().front()) {
    if (&declaration == entry.getOperation())
      continue;
    auto checked = helpers.lookup(&declaration);
    auto *selected = checked ? checked.getOperation() : &declaration;
    if (!chargeCopy(selected, remaining))
      return {};
    builder.clone(*selected);
  }
  localEntry = local::FuncOp::create(
      builder, entry.getLoc(), entry.getSymName(), entry.getFunctionType());
  auto *body = localEntry.addEntryBlock();
  builder.setInsertionPointToEnd(body);
  IRMapping values;
  values.map(normalized.getArguments(), body->getArguments());
  for (auto &op : normalized.front().without_terminator()) {
    if (!mathematical::isTotal(&op) || isa<func::CallOp>(op) ||
        op.getName().getDialectNamespace() == "poly")
      return {};
    uint64_t cost = 1 + op.getNumOperands() + op.getNumResults();
    if (cost > remaining)
      return {};
    remaining -= cost;
    auto *copy = builder.clone(op, values);
    if (helpers.isPolynomialGenerated(&op))
      shareable.insert(copy);
    copy->removeAttr("site");
  }
  SmallVector<Value> outputs;
  for (auto value : normalized.front().back().getOperands())
    outputs.push_back(values.lookup(value));
  local::ReturnOp::create(builder, entry.getLoc(), outputs);
  return scratch;
}
// Exact adapter for an already checked normalized mathematical subject. This
// reader never calls a normalizer or any numerical emitter. Recipe verification
// consumes the actual candidate against this retained mathematical body.
OwningOpRef<protocol_ir::ProtocolModuleOp>
recipeWorkspace(ModuleOp unit, local::FuncOp &localEntry, StringRef callSite,
                uint64_t &remaining, uint64_t &remainingBytes) {
  auto entry = getEntry(unit);
  if (!entry || !entry.getBody().hasOneBlock())
    return {};
  if (!chargeCopy(unit, remaining))
    return {};
  OpBuilder builder(unit.getContext());
  OperationState state(unit.getLoc(),
                       protocol_ir::ProtocolModuleOp::getOperationName());
  state.addAttribute("profile",
                     protocol_ir::ProfileAttr::get(unit.getContext(),
                                                   protocol_ir::Profile::Exec));
  state.addRegion();
  OwningOpRef<protocol_ir::ProtocolModuleOp> scratch(
      cast<protocol_ir::ProtocolModuleOp>(builder.create(state)));
  scratch->getBody().emplaceBlock();
  builder.setInsertionPointToEnd(&scratch->getBody().front());
  for (auto &declaration : unit.getBody().front())
    if (&declaration != entry.getOperation())
      builder.clone(declaration);
  localEntry = local::FuncOp::create(
      builder, entry.getLoc(), entry.getSymName(), entry.getFunctionType());
  auto *body = localEntry.addEntryBlock();
  builder.setInsertionPointToEnd(body);
  IRMapping values;
  values.map(entry.getArguments(), body->getArguments());
  unsigned ordinal = 0;
  for (auto &op : entry.front().without_terminator()) {
    if (!mathematical::isTotal(&op) || op.getNumRegions() ||
        op.getName().getDialectNamespace() == "poly")
      return {};
    auto site =
        protocol::algorithmSite({{callSite.str(), "kernel"}},
                                std::to_string(ordinal++), remainingBytes);
    if (!site) {
      diagnostics::emit(entry.emitError(), site.takeError());
      return {};
    }
    auto *copy = builder.clone(op, values);
    copy->setAttr("site", builder.getStringAttr(*site));
  }
  SmallVector<Value> outputs;
  for (Value value : entry.front().back().getOperands())
    outputs.push_back(values.lookup(value));
  local::ReturnOp::create(builder, entry.getLoc(), outputs);
  return scratch;
}
} // namespace zkc::kernel
