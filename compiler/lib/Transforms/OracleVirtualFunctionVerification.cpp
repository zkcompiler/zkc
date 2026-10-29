#include "OracleVerificationContext.h"
#include "OracleVirtualFunctions.h"
#include "OracleVirtualRecipe.h"
#include "zkc/Support/Refusal.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
Error checkOracleVirtualFunctions(ModuleOp candidate,
                                  protocol_ir::OracleDefinitionOp source,
                                  const OracleVirtualFunctions &actual) {
  auto original = source ? source->getParentOfType<ModuleOp>() : ModuleOp{};
  auto sourceContext = OracleVerificationContext::read(original);
  if (!sourceContext) {
    consumeError(sourceContext.takeError());
    return error("oracle-virtual-function-body");
  }
  auto targetContext = OracleVerificationContext::read(candidate);
  if (!targetContext) {
    consumeError(targetContext.takeError());
    return error("oracle-virtual-function-body");
  }
  return checkOracleVirtualFunctions(*targetContext, *sourceContext, source,
                                     actual);
}
Error checkOracleVirtualFunctions(
    const OracleVerificationContext &targetContext,
    const OracleVerificationContext &sourceContext,
    protocol_ir::OracleDefinitionOp source,
    const OracleVirtualFunctions &actual) {
  auto refuse = [] { return error("oracle-virtual-function-body"); };
  auto sourceUnit = sourceContext.getUnit(), unit = targetContext.getUnit();
  if (!source || source->getParentOp() != sourceUnit || sourceUnit == unit ||
      source.getContext() != unit.getContext())
    return refuse();
  OracleVirtualFunctionWork work;
  auto recipe = planOracleVirtualFunctions(source, work);
  if (!recipe) {
    consumeError(recipe.takeError());
    return refuse();
  }
  if (actual.queries.size() != recipe->queries.size())
    return refuse();
  auto compare = [&](func::FuncOp function, const OracleVirtualBody &body) {
    if (!function || function->getParentOp() != unit || !function.isPrivate() ||
        !function.getBody().hasOneBlock() || function->getAttrs().size() != 3 ||
        !equal(function.getArgumentTypes(), body.block.types) ||
        !equal(function.getResultTypes(), TypeRange(body.resultType)))
      return false;
    llvm::DenseMap<unsigned, Value> environment;
    auto block = [&](auto &&block, const OracleVirtualBlock &expected,
                     Block &actual, llvm::DenseMap<unsigned, Value> &values,
                     bool root) -> bool {
      if (!equal(actual.getArgumentTypes(), expected.types) ||
          actual.getOperations().size() !=
              expected.instructions.size() + unsigned(root))
        return false;
      for (auto [id, value] : zip(expected.arguments, actual.getArguments()))
        if (!values.try_emplace(id, value).second)
          return false;
      auto next = actual.begin();
      for (const auto &item : expected.instructions) {
        auto &op = *next++;
        if (op.getName() != item.source->getName() ||
            op.getAttrDictionary() != item.source->getAttrDictionary() ||
            !equal(op.getResultTypes(), item.source->getResultTypes()) ||
            op.getNumOperands() != item.inputs.size() ||
            op.getNumRegions() != item.regions.size() || op.getNumSuccessors())
          return false;
        for (auto [id, input] : zip(item.inputs, op.getOperands()))
          if (!values.contains(id) || values.lookup(id) != input)
            return false;
        for (auto [nested, region] : zip(item.regions, op.getRegions())) {
          auto local = values;
          if (!region.hasOneBlock() ||
              !block(block, *nested, region.front(), local, false))
            return false;
        }
        for (auto [id, value] : zip(item.outputs, op.getResults()))
          if (!values.try_emplace(id, value).second)
            return false;
      }
      return true;
    };
    if (!block(block, body.block, function.front(), environment, true))
      return false;
    auto returned = dyn_cast<func::ReturnOp>(function.front().back());
    return returned && returned->getAttrs().empty() &&
           returned.getNumOperands() == 1 &&
           environment.contains(body.result) &&
           returned.getOperand(0) == environment.lookup(body.result);
  };
  for (auto [expected, function] : zip(recipe->queries, actual.queries))
    if (function.source != expected.source || function.site != expected.site ||
        function.kind != expected.kind ||
        !compare(function.position, expected.position))
      return refuse();
  if (!compare(actual.answer, recipe->answer))
    return refuse();
  return Error::success();
}
} // namespace zkc::protocol
