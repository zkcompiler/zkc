#include "ResourceOrigins.h"
#include "mlir/Interfaces/ControlFlowInterfaces.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
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
  bool local = isa_and_nonnull<local::FuncOp>(callee);
  if (!callee ||
      (isa<protocol_ir::ApplyOp>(op) ? !isa<protocol_ir::MathematicalOp>(callee)
                                     : !local) ||
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
  if (failed(block(callee->getRegion(0).front(), local, depth + 1, summary)))
    return failure();
  result = &summaries.try_emplace(callee, std::move(summary)).first->second;
  return success();
}

LogicalResult ResourceOrigins::successors(Operation *op,
                                          Environment &environment) {
  if (none_of(op->getOperands(), [&](Value value) { return affine(value); }) ||
      none_of(op->getResults(), [&](Value value) { return affine(value); }))
    return success();
  auto binding = protocol::operationBinding(op);
  if (!binding) {
    consumeError(binding.takeError());
    return success();
  }
  auto facts = protocol::operationContracts(binding->application.contract);
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

LogicalResult ResourceOrigins::control(Operation *op, unsigned depth,
                                       Environment &environment,
                                       Summary &result) {
  auto interface = cast<RegionBranchOpInterface>(op);
  bool loop = isa<local::LocalForOp>(op);
  bool continuingArm = false;
  llvm::DenseMap<unsigned, unsigned> joined;
  for (auto &region : op->getRegions()) {
    if (failed(charge(op, 1))) // region entry
      return failure();
    Summary nested;
    if (failed(block(region.front(), true, depth + 1, nested)))
      return failure();
    result.depth = std::max(result.depth, nested.depth + 1);
    RegionSuccessor successor(&region);
    auto inputs = interface.getEntrySuccessorOperands(successor);
    auto arguments = interface.getSuccessorInputs(successor);
    if (inputs.size() != arguments.size())
      return malformed(op, "inconsistent resource-origin region mapping");
    if (failed(charge(op, inputs.size() + op->getNumResults())))
      return failure();
    Environment mapped;
    for (auto [argument, input] : zip(arguments, inputs)) {
      auto found = environment.find(input);
      if (affine(argument) && affine(input) && found != environment.end())
        mapped[argument] = found->second;
    }
    llvm::DenseMap<unsigned, unsigned> roots;
    for (auto [index, output] : enumerate(op->getResults())) {
      if (!affine(output))
        continue;
      auto root = nested.roots.find(index);
      if (loop) {
        // Each carried slot is its own symbol. Other slots may remain unknown.
        auto carried = cast<BlockArgument>(arguments[index]);
        if (nested.continues && (root == nested.roots.end() ||
                                 root->second != carried.getArgNumber()))
          continue;
        if (auto initial = mapped.find(carried); initial != mapped.end())
          roots[index] = initial->second;
      } else if (root != nested.roots.end()) {
        auto argument = region.front().getArgument(root->second);
        // Payload arguments of a match are absent from mapped.
        if (auto actual = mapped.find(argument); actual != mapped.end())
          roots[index] = actual->second;
      }
    }
    if (loop || nested.continues) {
      if (!continuingArm)
        joined = std::move(roots);
      else {
        for (auto it = joined.begin(); it != joined.end();) {
          auto found = roots.find(it->first);
          if (found == roots.end() || found->second != it->second)
            joined.erase(it++);
          else
            ++it;
        }
      }
      continuingArm = true;
    }
  }
  result.continues = continuingArm;
  for (auto [index, root] : joined)
    environment[op->getResult(index)] = root;
  return success();
}

LogicalResult ResourceOrigins::block(Block &body, bool local, unsigned depth,
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
    if (isa<local::StopOp>(op)) {
      if (!local)
        return malformed(op, "local stop requires local execution");
      result.continues = false;
      return success();
    }
    if (isa<local::ReturnOp, local::LocalYieldOp, local::LocalConditionOp,
            protocol_ir::MathematicalReturnOp, protocol_ir::ProtocolYieldOp>(
            op)) {
      for (auto [index, input] : enumerate(op->getOperands().drop_front(
               isa<local::LocalConditionOp>(op) ? 1 : 0)))
        if (auto found = environment.find(input); found != environment.end())
          result.roots[index] = found->second;
      return success();
    }
    if (isa<local::LocalIfOp, local::LocalMatchOp, local::LocalForOp>(op)) {
      if (!local)
        return malformed(op, "local control requires local execution");
      if (failed(control(op, depth, environment, result)))
        return failure();
      if (!result.continues)
        return success();
    } else if (isa<local::CallOp, local::ApplyOp, protocol_ir::LocalCallOp,
                   protocol_ir::ApplyOp>(op)) {
      // Common execution ignores role-local continuation and needs a summary
      // only if this call could supply an affine result. A preparation-time
      // declaration has no body yet; its profile admits only data ports.
      auto name = op->getAttrOfType<FlatSymbolRefAttr>("callee");
      bool prepared = isa<local::ApplyOp>(op) && name &&
                      isa_and_nonnull<PreparationCallableOpInterface>(
                          symbols.lookupNearestSymbolFrom(op, name));
      if ((!local || prepared) &&
          none_of(op->getResults(), [&](Value v) { return affine(v); }))
        continue;
      const Summary *callee;
      if (failed(call(op, depth, callee)))
        return failure();
      result.depth = std::max(result.depth, callee->depth + 1);
      if (!callee->continues) {
        if (local) {
          result.continues = false;
          return success();
        }
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
  if (failed(block(repeat.getBody().front(), false, 1, summary)))
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
