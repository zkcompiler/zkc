#include "ResourceOrigins.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecTypes.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/ScopeExit.h"

using namespace mlir;
using namespace llvm;

namespace zkc::mathematical {
namespace {
LogicalResult malformed(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "mathematical-formation", detail);
}
} // namespace
LogicalResult ResourceOrigins::limit(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "mathematical-analysis-limit",
                           detail);
}
LogicalResult ResourceOrigins::charge(Operation *op, uint64_t amount) {
  if (amount > remaining)
    return limit(op, "resource-origin work limit exceeded");
  remaining -= amount;
  return success();
}
bool ResourceOrigins::affine(Value value) {
  auto policy = types.get(value.getType());
  return policy && policy->affine;
}

LogicalResult ResourceOrigins::call(Operation *op, unsigned depth,
                                    const Summary *&result) {
  auto name = op->getAttrOfType<FlatSymbolRefAttr>("callee");
  Operation *callee =
      name ? symbols.lookupNearestSymbolFrom(op, name) : nullptr;
  if (auto function = dyn_cast_or_null<func::FuncOp>(callee)) {
    // Protocol calls expose logical ports; the scoped function prepends its
    // borrowed scope and wraps its results in an explicit outcome. The reader
    // validates the complete actual profile before the native view drops those
    // administrative ports. A name, origin marker or matching type is not a
    // resource successor law.
    if (isa<protocol_ir::ApplyOp>(op) ||
        function.getNumArguments() != op->getNumOperands() + 1 ||
        function.getNumResults() != 1 ||
        !isa<runtime::ScopeType>(function.getArgumentTypes().front()) ||
        !llvm::equal(function.getArgumentTypes().drop_front(),
                     op->getOperandTypes()))
      return malformed(op, "resource origins require a scoped helper");
    auto outcome =
        dyn_cast<exec::OutcomeType>(function.getFunctionType().getResult(0));
    if (!outcome || !llvm::equal(outcome.getPayload(), op->getResultTypes()))
      return malformed(op, "inconsistent scoped resource-origin signature");
    if (!execution) {
      executionOwner = function->getParentOp();
      auto closure = protocol::readSourceExecutionClosure(executionOwner);
      if (!closure)
        return diagnostics::emit(op->emitOpError(), closure.takeError());
      auto analysis = exec::ResourceOriginAnalysis::create(
          executionOwner, std::move(*closure), remaining, depthLimit);
      if (!analysis)
        return diagnostics::emit(op->emitOpError(), analysis.takeError());
      execution = std::move(*analysis);
    }
    if (executionOwner != function->getParentOp())
      return malformed(op, "resource-origin query crossed its source closure");
    auto roots = execution->get(function, depth + 1);
    if (!roots)
      return diagnostics::emit(op->emitOpError(), roots.takeError());
    Summary summary;
    summary.continues = roots->continues;
    summary.depth = roots->depth;
    for (auto [output, input] : roots->roots)
      summary.roots[output] = input;
    result =
        &summaries.insert_or_assign(callee, std::move(summary)).first->second;
    return success();
  }
  if (!callee || !isa<protocol_ir::ApplyOp>(op) ||
      !isa<protocol_ir::MathematicalOp>(callee) ||
      callee->getNumRegions() != 1 || !hasSingleElement(callee->getRegion(0)) ||
      callee->getRegion(0).front().empty())
    return malformed(op, "resource origins require a defined matching callee");
  if (callee->getRegion(0).front().getNumArguments() != op->getNumOperands())
    return malformed(op, "inconsistent resource-origin call signature");
  if (active.contains(callee))
    return malformed(op, "resource-origin calls must be acyclic");
  if (auto found = summaries.find(callee); found != summaries.end()) {
    // A cached shallow invocation cannot hide the same callee's nested depth
    // when it is later reached through a deeper caller.
    if (depth > depthLimit || found->second.depth > depthLimit - depth)
      return limit(op, "resource-origin nesting limit exceeded");
    result = &found->second;
    return success();
  }
  if (failed(charge(op, 1))) // summary entry, before growing the cache
    return failure();
  active.insert(callee);
  auto cleanup = scope_exit([&] { active.erase(callee); });
  Summary summary;
  if (failed(block(callee->getRegion(0).front(), depth + 1, summary)))
    return failure();
  result = &summaries.try_emplace(callee, std::move(summary)).first->second;
  return success();
}

LogicalResult ResourceOrigins::successors(Operation *op,
                                          Environment &environment) {
  if (none_of(op->getOperands(), [&](Value value) { return affine(value); }) ||
      none_of(op->getResults(), [&](Value value) { return affine(value); }))
    return success();
  if (!op->hasAttr("binding"))
    return success();
  auto binding = lookupNativeBinding(op);
  if (failed(binding))
    return failure();
  auto facts = protocol::operationContracts(binding->declaration.getContract());
  if (!facts)
    return success();
  // At most three installed facets. Unknown/conflicting equations for the same
  // output stay unknown; no later facet can overwrite an earlier constraint.
  llvm::DenseMap<unsigned, std::optional<unsigned>> roots;
  auto pair = [&](unsigned input, unsigned output) -> LogicalResult {
    if (failed(charge(op, 1)))
      return failure();
    if (output >= op->getNumResults() || !affine(op->getResult(output)))
      return success();
    std::optional<unsigned> root;
    if (input < op->getNumOperands() && affine(op->getOperand(input))) {
      auto found = environment.find(op->getOperand(input));
      if (found != environment.end())
        root = found->second;
    }
    auto [entry, inserted] = roots.try_emplace(output, root);
    if (!inserted && entry->second != root)
      entry->second.reset();
    return success();
  };
  if ((facts->history &&
       failed(pair(facts->history->stateInput, facts->history->stateOutput))) ||
      (facts->sampling && failed(pair(facts->sampling->stateInput,
                                      facts->sampling->stateOutput))) ||
      (facts->observation && failed(pair(facts->observation->stateInput,
                                         facts->observation->stateOutput))))
    return failure();
  for (auto [output, root] : roots)
    if (root)
      environment[op->getResult(output)] = *root;
  return success();
}

LogicalResult ResourceOrigins::block(Block &body, unsigned depth,
                                     Summary &result) {
  auto *owner = body.getParentOp();
  if (depth > depthLimit)
    return limit(owner, "resource-origin nesting limit exceeded");
  if (failed(charge(owner, body.getNumArguments())))
    return failure();
  Environment environment;
  for (auto [index, argument] : enumerate(body.getArguments()))
    if (affine(argument))
      environment[argument] = index;
  for (auto &operation : body) {
    auto *op = &operation;
    // Charge scans even for copyable values. Each operand/result visit covers
    // its lookup/substitution or stored fact; no wide signature is free.
    if (failed(charge(op, 1 + uint64_t(op->getNumOperands()) +
                              op->getNumResults())))
      return failure();
    if (isa<protocol_ir::MathematicalReturnOp, protocol_ir::ProtocolYieldOp>(
            op)) {
      for (auto [index, input] : enumerate(op->getOperands()))
        if (auto found = environment.find(input); found != environment.end())
          result.roots[index] = found->second;
      return success();
    }
    if (isa<protocol_ir::LocalCallOp, protocol_ir::ApplyOp>(op)) {
      // Common protocol flow needs origins only for affine results.
      if (none_of(op->getResults(), [&](Value v) { return affine(v); }))
        continue;
      const Summary *callee;
      if (failed(call(op, depth, callee)))
        return failure();
      result.depth = std::max(result.depth, callee->depth + 1);
      if (!callee->continues) {
        // A role's stop cannot prune another role's common actions.
        continue;
      }
      for (auto [index, input] : callee->roots) {
        if (index >= op->getNumResults() || input >= op->getNumOperands())
          return malformed(op, "inconsistent resource-origin call signature");
        auto found = environment.find(op->getOperand(input));
        if (affine(op->getResult(index)) && affine(op->getOperand(input)) &&
            found != environment.end())
          environment[op->getResult(index)] = found->second;
      }
    } else if (auto completion = dyn_cast<protocol_ir::FinishIfOp>(op)) {
      // Only the continuing edge supplies SSA results. Completion of one role
      // cannot prune another role's mathematical suffix or its obligations.
      unsigned resultIndex = 0;
      for (Value input : completion.getValues()) {
        if (!affine(input))
          continue;
        auto found = environment.find(input);
        if (found != environment.end())
          environment[completion.getResult(resultIndex)] = found->second;
        ++resultIndex;
      }
    } else if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(op)) {
      // Ordinary formation checks shape before the separate origin phase;
      // every callee repeat invariant is also an independent obligation.
      if (repeat.getInputs().size() < repeat.getNumResults() + 1)
        return malformed(op, "inconsistent resource-origin repeat inputs");
      for (auto [index, output] : enumerate(repeat.getResults())) {
        auto input = repeat.getInputs()[index + 1];
        auto found = environment.find(input);
        if (affine(output) && affine(input) && found != environment.end())
          environment[output] = found->second;
      }
    } else if (failed(successors(op, environment)))
      return failure();
  }
  return malformed(owner, "resource-origin body has no terminator");
}

LogicalResult ResourceOrigins::verify(protocol_ir::RepeatOp repeat) {
  // Do not spend origin work on programs without affine root obligations.
  if (none_of(repeat.getResults(), [&](Value v) { return affine(v); }))
    return success();
  Summary summary;
  if (failed(block(repeat.getBody().front(), 1, summary)))
    return failure();
  for (auto [index, output] : enumerate(repeat.getResults())) {
    if (!affine(output))
      continue;
    auto root = summary.roots.find(index);
    if (root == summary.roots.end() || root->second != index + 1)
      return malformed(repeat,
                       "yield must preserve the exact carried resource root");
  }
  return success();
}
} // namespace zkc::mathematical
