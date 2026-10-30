#include "OracleVirtualFunctions.h"
#include "OracleVirtualRecipe.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Support/Refusal.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
Expected<OracleVirtualFunctions>
emitOracleVirtualFunctions(ModuleOp candidate,
                           protocol_ir::OracleDefinitionOp source,
                           OracleVirtualFunctionWork &work) {
  auto sourceUnit =
      source ? dyn_cast<protocol_ir::ProtocolModuleOp>(source->getParentOp())
             : protocol_ir::ProtocolModuleOp{};
  if (!candidate || !sourceUnit ||
      source.getContext() != candidate.getContext() ||
      sourceUnit.getProfile() != protocol_ir::Profile::Protocol ||
      failed(zkc::admitStage(sourceUnit)) ||
      failed(zkc::admitStage(candidate)) ||
      !hasSingleElement(candidate.getBody()->getOperations()))
    return error("oracle-virtual-functions");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol ||
      unit == sourceUnit)
    return error("oracle-virtual-functions");
  auto recipe = planOracleVirtualFunctions(source, work);
  if (!recipe)
    return recipe.takeError();
  auto emit = [&](StringRef suffix,
                  const OracleVirtualBody &body) -> Expected<func::FuncOp> {
    OpBuilder builder(candidate.getContext());
    std::string prefix =
        "_oracle_virtual_" + source.getSymName().str() + "_" + suffix.str();
    std::string name = prefix;
    for (unsigned n = 0; SymbolTable::lookupSymbolIn(unit, name); ++n)
      name = prefix + "_" + std::to_string(n);
    builder.setInsertionPointToEnd(&unit.getBody().front());
    auto helper = func::FuncOp::create(
        builder, source.getLoc(), name,
        builder.getFunctionType(body.block.types, body.resultType));
    helper.setPrivate();
    llvm::DenseMap<unsigned, Value> values;
    auto copy = [&](auto &&copy, const OracleVirtualBlock &plan, Block &block,
                    llvm::DenseMap<unsigned, Value> values)
        -> Expected<llvm::DenseMap<unsigned, Value>> {
      if (!work.operations || plan.arguments.size() > work.slots)
        return error("oracle-virtual-function-limit");
      --work.operations;
      work.slots -= plan.arguments.size();
      for (auto [id, type] : zip(plan.arguments, plan.types))
        values[id] = block.addArgument(type, source.getLoc());
      for (const auto &item : plan.instructions) {
        uint64_t cost = item.inputs.size() + item.outputs.size();
        if (!work.operations || cost > work.slots)
          return error("oracle-virtual-function-limit");
        --work.operations;
        work.slots -= cost;
        builder.setInsertionPointToEnd(&block);
        OperationState state(item.source->getLoc(), item.source->getName());
        state.addAttributes(item.source->getAttrs());
        state.addTypes(item.source->getResultTypes());
        for (unsigned id : item.inputs)
          state.addOperands(values.lookup(id));
        for (const auto &region : item.regions) {
          auto *nested = new Block;
          state.addRegion()->push_back(nested);
          auto copied = copy(copy, *region, *nested, values);
          if (!copied)
            return copied.takeError();
        }
        builder.setInsertionPointToEnd(&block);
        auto *op = builder.create(state);
        for (auto [id, value] : zip(item.outputs, op->getResults()))
          values[id] = value;
      }
      return values;
    };
    auto *block = new Block;
    helper.getBody().push_back(block);
    auto copied = copy(copy, body.block, *block, values);
    if (!copied)
      return copied.takeError();
    builder.setInsertionPointToEnd(block);
    func::ReturnOp::create(builder, source.getLoc(),
                           copied->lookup(body.result));
    return helper;
  };
  OracleVirtualFunctions result;
  for (auto [i, query] : enumerate(recipe->queries)) {
    auto function = emit("position_" + std::to_string(i), query.position);
    if (!function)
      return function.takeError();
    result.queries.push_back({query.source, query.site, query.kind, *function});
  }
  auto answer = emit("answer", recipe->answer);
  if (!answer)
    return answer.takeError();
  result.answer = *answer;
  if (failed(zkc::admitStage(candidate)))
    return error("oracle-virtual-functions");
  return result;
}
} // namespace zkc::protocol
