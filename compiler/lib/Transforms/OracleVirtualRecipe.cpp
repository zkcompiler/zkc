#include "OracleVirtualRecipe.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using IDs = std::vector<unsigned>;
using Environment = llvm::DenseMap<Value, unsigned>;
Error refuse() { return error("oracle-virtual-functions"); }
struct Planner {
  protocol_ir::OracleDefinitionOp source;
  OracleVirtualFunctionWork &work;
  OracleVirtualRecipe result;
  OracleVirtualBlock expanded;
  Environment values;
  llvm::DenseSet<Operation *> active;
  unsigned next = 0;
  Planner(protocol_ir::OracleDefinitionOp source,
          OracleVirtualFunctionWork &work)
      : source(source), work(work) {}
  bool charge(uint64_t slots) {
    if (!work.operations || slots > work.slots)
      return false;
    --work.operations;
    work.slots -= slots;
    return true;
  }
  Expected<IDs> operands(ValueRange inputs, const Environment &environment) {
    IDs mapped;
    for (Value input : inputs) {
      auto found = environment.find(input);
      if (found == environment.end())
        return refuse();
      mapped.push_back(found->second);
    }
    return mapped;
  }
  Error instruction(Operation &op, OracleVirtualBlock &target,
                    Environment &environment, unsigned depth) {
    if (depth >= 64 || !charge(op.getNumOperands() + op.getNumResults()))
      return error("oracle-virtual-function-limit");
    auto inputs = operands(op.getOperands(), environment);
    if (!inputs)
      return inputs.takeError();
    if (auto call = dyn_cast<func::CallOp>(op)) {
      auto callee = SymbolTable::lookupNearestSymbolFrom<func::FuncOp>(
          &op, call.getCalleeAttr());
      if (!callee || !callee.getBody().hasOneBlock() ||
          callee.getNumArguments() != inputs->size() ||
          !active.insert(callee).second)
        return refuse();
      auto leave = llvm::scope_exit([&] { active.erase(callee); });
      Environment local;
      for (auto [formal, value] : zip(callee.getArguments(), *inputs))
        local[formal] = value;
      for (auto &nested : callee.front().without_terminator())
        if (auto e = instruction(nested, target, local, depth + 1))
          return e;
      auto returned = dyn_cast<func::ReturnOp>(callee.front().back());
      if (!returned || !charge(returned.getNumOperands()))
        return error("oracle-virtual-function-limit");
      auto outputs = operands(returned.getOperands(), local);
      if (!outputs)
        return outputs.takeError();
      if (outputs->size() != op.getNumResults())
        return refuse();
      for (auto [value, id] : zip(op.getResults(), *outputs))
        environment[value] = id;
      return Error::success();
    }
    // Total-region terminators are copied inside their original owner. Calls
    // are interpreted above, so no generated helper can hide another body.
    if ((!mathematical::isTotal(&op) &&
         !op.hasTrait<OpTrait::IsTerminator>()) ||
        op.getNumSuccessors())
      return refuse();
    OracleVirtualInstruction item{&op, std::move(*inputs), {}, {}};
    for (auto &region : op.getRegions()) {
      if (!region.hasOneBlock())
        return refuse();
      auto nested = std::make_shared<OracleVirtualBlock>();
      Environment local(environment);
      if (!charge(region.front().getNumArguments()))
        return error("oracle-virtual-function-limit");
      for (auto argument : region.front().getArguments()) {
        unsigned id = next++;
        local[argument] = id;
        nested->arguments.push_back(id);
        nested->types.push_back(argument.getType());
      }
      for (auto &operation : region.front())
        if (auto e = instruction(operation, *nested, local, depth + 1))
          return e;
      item.regions.push_back(std::move(nested));
    }
    for (Value output : op.getResults()) {
      unsigned id = next++;
      environment[output] = id;
      item.outputs.push_back(id);
    }
    target.instructions.push_back(std::move(item));
    return Error::success();
  }
  // Attribute every nested definition to its outer instruction. Captures then
  // add dependencies on earlier outer instructions, while local region values
  // remain inside that one copied instruction.
  void owners(const OracleVirtualInstruction &item, unsigned owner,
              llvm::DenseMap<unsigned, unsigned> &definitions) {
    for (unsigned id : item.outputs)
      definitions[id] = owner;
    for (const auto &region : item.regions) {
      for (unsigned id : region->arguments)
        definitions[id] = owner;
      for (const auto &nested : region->instructions)
        owners(nested, owner, definitions);
    }
  }
  void dependencies(const OracleVirtualInstruction &item, IDs &pending) {
    append_range(pending, item.inputs);
    for (const auto &region : item.regions)
      for (const auto &nested : region->instructions)
        dependencies(nested, pending);
  }
  Expected<OracleVirtualBody> slice(Value value, ArrayRef<unsigned> arguments,
                                    TypeRange types) {
    auto mapped = operands(ValueRange(value), values);
    if (!mapped)
      return mapped.takeError();
    OracleVirtualBody body{{{arguments.begin(), arguments.end()},
                            {types.begin(), types.end()},
                            {}},
                           mapped->front(),
                           value.getType()};
    llvm::DenseMap<unsigned, unsigned> definitions;
    for (auto [i, item] : enumerate(expanded.instructions))
      owners(item, i, definitions);
    llvm::DenseSet<unsigned> formal(arguments.begin(), arguments.end()), needed;
    IDs pending{body.result};
    while (!pending.empty()) {
      if (!work.slots)
        return error("oracle-virtual-function-limit");
      --work.slots;
      auto id = pending.back();
      pending.pop_back();
      if (formal.contains(id))
        continue;
      auto found = definitions.find(id);
      if (found == definitions.end())
        return refuse();
      if (needed.insert(found->second).second)
        dependencies(expanded.instructions[found->second], pending);
    }
    for (auto [i, item] : enumerate(expanded.instructions))
      if (needed.contains(i))
        body.block.instructions.push_back(item);
    return body;
  }
  Expected<OracleVirtualRecipe> run() {
    auto &body = source.getBody().front();
    IDs arguments, answers;
    SmallVector<Type> types, answerTypes;
    if (!charge(body.getNumArguments()))
      return error("oracle-virtual-function-limit");
    for (auto argument :
         body.getArguments().drop_front(source.getNumSources())) {
      values[argument] = next;
      arguments.push_back(next++);
      types.push_back(argument.getType());
    }
    SmallVector<protocol_ir::OracleQueryOp> queries;
    for (auto &op : body.without_terminator()) {
      if (auto query = dyn_cast<protocol_ir::OracleQueryOp>(op)) {
        if (!charge(query.getNumOperands() + 1))
          return error("oracle-virtual-function-limit");
        queries.push_back(query);
        values[query.getAnswer()] = next;
        answers.push_back(next++);
        answerTypes.push_back(query.getAnswer().getType());
      } else if (auto e = instruction(op, expanded, values, 0))
        return std::move(e);
    }
    for (auto query : queries) {
      auto position = slice(query.getPosition(), arguments, types);
      if (!position)
        return position.takeError();
      result.queries.push_back(
          {cast<BlockArgument>(query.getHandle()).getArgNumber(),
           query.getSite().str(), query.getHandle().getType().getKind(),
           std::move(*position)});
    }
    append_range(arguments, answers);
    append_range(types, answerTypes);
    auto answer =
        slice(cast<protocol_ir::OracleYieldOp>(body.back()).getAnswer(),
              arguments, types);
    if (!answer)
      return answer.takeError();
    result.answer = std::move(*answer);
    return std::move(result);
  }
};
} // namespace
Expected<OracleVirtualRecipe>
planOracleVirtualFunctions(protocol_ir::OracleDefinitionOp source,
                           OracleVirtualFunctionWork &work) {
  if (!source || !source.getBody().hasOneBlock())
    return refuse();
  return Planner{source, work}.run();
}
} // namespace zkc::protocol
