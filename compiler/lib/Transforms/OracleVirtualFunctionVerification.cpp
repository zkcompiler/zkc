#include "OracleAccounting.h"
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
  OracleNativeWork rawWork;
  auto sourceContext = OracleVerificationContext::read(original, rawWork);
  if (!sourceContext) {
    return llvm::handleErrors(sourceContext.takeError(),
                              [&](const Refusal &failure) -> Error {
                                if (failure.code == "oracle-common-limit" ||
                                    failure.code == "common-control-capacity")
                                  return error(failure.code, failure.detail);
                                return error("oracle-virtual-function-body");
                              });
  }
  auto targetContext = OracleVerificationContext::read(candidate, rawWork);
  if (!targetContext) {
    return llvm::handleErrors(targetContext.takeError(),
                              [&](const Refusal &failure) -> Error {
                                if (failure.code == "oracle-common-limit" ||
                                    failure.code == "common-control-capacity")
                                  return error(failure.code, failure.detail);
                                return error("oracle-virtual-function-body");
                              });
  }
  return checkOracleVirtualFunctions(*targetContext, *sourceContext, source,
                                     actual);
}
Error checkOracleVirtualFunctions(
    const OracleVerificationContext &targetContext,
    const OracleVerificationContext &sourceContext,
    protocol_ir::OracleDefinitionOp source,
    const OracleVirtualFunctions &actual) {
  return oracleVerificationWithWork(targetContext.getWork(), [&]() -> Error {
    auto refuse = [] { return error("oracle-virtual-function-body"); };
    auto sourceUnit = sourceContext.getUnit(), unit = targetContext.getUnit();
    if (!source || source->getParentOp() != sourceUnit || sourceUnit == unit ||
        source.getContext() != unit.getContext())
      return refuse();
    Builder builder(unit.getContext());
    SmallVector<Attribute> parts;
    if (!targetContext.charge(2 + actual.queries.size()))
      return error("oracle-common-limit");
    auto symbol = [&](func::FuncOp function) -> Attribute {
      if (!function || function->getParentOp() != unit)
        return {};
      return FlatSymbolRefAttr::get(function);
    };
    auto answer = symbol(actual.answer);
    if (!answer)
      return refuse();
    parts.push_back(answer);
    for (const auto &query : actual.queries) {
      auto position = symbol(query.position);
      if (!position || !query.kind ||
          !targetContext.charge(5 + 2 * query.site.size()))
        return targetContext.getWork().exhausted ? error("oracle-common-limit")
                                                 : refuse();
      parts.push_back(builder.getI64IntegerAttr(query.source));
      parts.push_back(builder.getStringAttr(query.site));
      parts.push_back(query.kind);
      parts.push_back(position);
    }
    auto key = builder.getArrayAttr(parts);
    auto cached = targetContext.checkedVirtualFunctions.find(source);
    if (cached != targetContext.checkedVirtualFunctions.end() &&
        cached->second.contains(key))
      return Error::success();
    OracleVirtualFunctionWork work;
    work.common = &sourceContext.getWork();
    auto recipe = planOracleVirtualFunctions(source, work);
    if (!recipe) {
      consumeError(recipe.takeError());
      return refuse();
    }
    if (actual.queries.size() != recipe->queries.size())
      return refuse();
    auto compare = [&](func::FuncOp function, const OracleVirtualBody &body) {
      if (!function || function->getParentOp() != unit ||
          !function.isPrivate() || !function.getBody().hasOneBlock() ||
          function->getAttrs().size() != 3 ||
          !equal(function.getArgumentTypes(), body.block.types) ||
          !equal(function.getResultTypes(), TypeRange(body.resultType)))
        return false;
      llvm::DenseMap<unsigned, Value> environment;
      auto block = [&](auto &&block, const OracleVirtualBlock &expected,
                       Block &actual, llvm::DenseMap<unsigned, Value> &values,
                       bool root) -> bool {
        if (!targetContext.charge(1 + actual.getNumArguments() +
                                  values.size()) ||
            !equal(actual.getArgumentTypes(), expected.types) ||
            actual.getOperations().size() !=
                expected.instructions.size() + unsigned(root))
          return false;
        for (auto [id, value] : zip(expected.arguments, actual.getArguments()))
          if (!values.try_emplace(id, value).second)
            return false;
        auto next = actual.begin();
        for (const auto &item : expected.instructions) {
          auto &op = *next++;
          if (!targetContext.charge(1 + op.getNumOperands() +
                                    op.getNumResults() + op.getNumRegions()))
            return false;
          if (op.getName() != item.source->getName() ||
              op.getAttrDictionary() != item.source->getAttrDictionary() ||
              !equal(op.getResultTypes(), item.source->getResultTypes()) ||
              op.getNumOperands() != item.inputs.size() ||
              op.getNumRegions() != item.regions.size() ||
              op.getNumSuccessors())
            return false;
          for (auto [id, input] : zip(item.inputs, op.getOperands()))
            if (!values.contains(id) || values.lookup(id) != input)
              return false;
          for (auto [nested, region] : zip(item.regions, op.getRegions())) {
            if (!targetContext.charge(values.size()))
              return false;
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
      if (function.source != expected.source ||
          function.site != expected.site || function.kind != expected.kind ||
          !compare(function.position, expected.position))
        return refuse();
    if (!compare(actual.answer, recipe->answer))
      return refuse();
    if (!targetContext.charge())
      return error("oracle-common-limit");
    targetContext.checkedVirtualFunctions[source].insert(key);
    return Error::success();
  });
}
} // namespace zkc::protocol
