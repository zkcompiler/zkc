#include "ExecutionPorts.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"

using namespace mlir;
using namespace llvm;
namespace zkc::target {
Expected<ExecutionPorts> ExecutionPorts::read(ModuleOp module) {
  if (!module || failed(verify(module)) || !hasSingleElement(*module.getBody()))
    return error("binding-execution-profile");
  auto root =
      dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  if (!root || (root.getProfile() != protocol_ir::Profile::Exec &&
                root.getProfile() != protocol_ir::Profile::Physical))
    return error("binding-execution-profile");
  auto checked = root.getProfile() == protocol_ir::Profile::Physical
                     ? protocol::readExecutionClosure(root, true)
                     : protocol::readSourceExecutionClosure(root);
  if (!checked)
    return checked.takeError();
  if (!checked->computations.empty())
    return error("binding-unresolved-execution");
  ExecutionPorts result;
  result.closure = std::make_shared<const protocol::SourceExecutionClosure>(
      std::move(*checked));
  uint64_t remaining = 1000000;
  auto charge = [&](uint64_t amount) {
    if (amount > remaining)
      return false;
    remaining -= amount;
    return true;
  };
  auto walked = module.walk<WalkOrder::PreOrder>([&](Operation *op) {
    if (!charge(1 + op->getNumOperands() + op->getNumResults()))
      return WalkResult::interrupt();
    result.ordered.push_back(op);
    result.nodes.try_emplace(op);
    return WalkResult::advance();
  });
  if (walked.wasInterrupted())
    return error("binding-execution-limit");
  for (auto *op : result.ordered) {
    auto dialect = op->getName().getDialectNamespace();
    if (dialect == "local" || dialect == "plan" || dialect == "kernel" ||
        isa<data::DomainOp>(op) ||
        (isa<ModuleOp>(op) && op != module.getOperation()))
      return error("binding-unresolved-execution");
  }
  // A scope owner and every closed control body have one logical data entry.
  // Payload definitions inside the CFG are registered by their actual step.
  for (auto function : root.getBody().front().getOps<func::FuncOp>()) {
    if (!protocol::isScopedExecutionFunction(function))
      return error("binding-unresolved-execution");
    auto &node = result.nodes.at(function);
    node.scoped = true;
    auto payload = cast<exec::OutcomeType>(function.getResultTypes().front());
    node.callable = FunctionType::get(module.getContext(),
                                      function.getArgumentTypes().drop_front(),
                                      payload.getPayload());
    auto *entry = &function.front();
    node.bodies.push_back(entry);
    Body body{
        function, entry, Values(function.getArguments().drop_front()), {}};
    auto found = result.closure->bodies.find(function.getSymName().str());
    if (found == result.closure->bodies.end())
      return error("binding-execution-profile");
    for (const auto &step : found->second) {
      if (isa<func::CallOp, exec::ComputeOp, exec::FoldOp, exec::CollectOp>(
              step.operation))
        return error("binding-unresolved-execution");
      auto &instruction = result.nodes.at(step.operation);
      instruction.scoped = true;
      instruction.step = &step;
      instruction.inputs = step.inputs;
      instruction.outputs = step.outputs;
      for (func::FuncOp region : step.regions) {
        instruction.bodies.push_back(&region.front());
        result.incoming[region].push_back(step.operation);
      }
      result.enclosing[step.operation] = entry;
      body.instructions.push_back(step.operation);
    }
    result.bodies.try_emplace(entry, std::move(body));
  }
  // Participant actions and repetition retain their own protocol-owned data
  // ports. No administrative operation inside a scoped function enters here.
  for (auto *op : result.ordered) {
    if (isa<func::FuncOp>(op) || op->getParentOfType<func::FuncOp>())
      continue;
    auto &node = result.nodes.at(op);
    append_range(node.inputs, op->getOperands());
    append_range(node.outputs, op->getResults());
    // An external runtime binding owns a call ABI, not a body whose entry
    // values physical selection may rewrite. Only this protocol body owner
    // exposes data ports here; scoped Func bodies are handled above.
    if (auto participant = dyn_cast<protocol_ir::ParticipantOp>(op))
      node.callable = participant.getFunctionType();
    if (!isa<protocol_ir::ParticipantOp, protocol_ir::ProtocolLoopOp>(op))
      continue;
    for (auto &region : op->getRegions())
      for (auto &block : region) {
        node.bodies.push_back(&block);
        Body body{op, &block, Values(block.getArguments()), {}};
        for (auto &instruction : block) {
          body.instructions.push_back(&instruction);
          result.enclosing[&instruction] = &block;
        }
        result.bodies.try_emplace(&block, std::move(body));
      }
  }
  auto define = [&](Value value, Definition coordinate) {
    return result.definitions.try_emplace(value, coordinate).second;
  };
  for (auto *op : result.ordered) {
    const auto &node = result.nodes.at(op);
    if (!charge(node.inputs.size() + node.outputs.size() + node.bodies.size()))
      return error("binding-execution-limit");
    for (auto [index, value] : enumerate(node.outputs))
      if (!define(value, {op, unsigned(index), false}))
        return error("binding-execution-coordinate");
    for (auto [blockIndex, entry] : enumerate(node.bodies)) {
      const auto &body = result.bodies.at(entry);
      if (body.owner != op)
        continue; // A control occurrence borrows an outlined function's body.
      if (!charge(body.arguments.size()))
        return error("binding-execution-limit");
      for (auto [index, value] : enumerate(body.arguments))
        if (!define(value, {op, unsigned(index), true, unsigned(blockIndex)}))
          return error("binding-execution-coordinate");
    }
    for (auto [index, value] : enumerate(node.inputs))
      result.users[value].push_back({op, unsigned(index)});
  }
  for (auto &[value, uses] : result.users)
    if (!result.definitions.contains(value))
      return error("binding-execution-coordinate");
  return result;
}
const ExecutionPorts::Node &ExecutionPorts::get(Operation *op) const {
  return nodes.at(op);
}
const ExecutionPorts::Body &ExecutionPorts::body(Block *entry) const {
  return bodies.at(entry);
}
ArrayRef<Operation *> ExecutionPorts::callers(Operation *function) const {
  auto found = incoming.find(function);
  return found == incoming.end() ? ArrayRef<Operation *>{} : found->second;
}
Block *ExecutionPorts::enclosingBody(Operation *instruction) const {
  return enclosing.lookup(instruction);
}
const ExecutionPorts::Definition &
ExecutionPorts::definition(Value value) const {
  return definitions.at(value);
}
ArrayRef<ExecutionPorts::Use> ExecutionPorts::uses(Value value) const {
  auto found = users.find(value);
  return found == users.end() ? ArrayRef<Use>{} : found->second;
}
} // namespace zkc::target
