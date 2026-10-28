#include "MathematicalValues.h"
#include "OracleVerificationContext.h"
#include "OracleVirtualFunctions.h"
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
  auto &body = source.getBody().front();
  unsigned sources = source.getNumSources();
  SmallVector<protocol_ir::OracleQueryOp> queries(
      body.getOps<protocol_ir::OracleQueryOp>());
  if (actual.queries.size() != queries.size())
    return refuse();
  mathematical::ValueCorrespondence terms(source);
  auto original = terms.environment();
  SmallVector<mathematical::ValueCorrespondence::Term> parameters, answers;
  SmallVector<Type> types;
  for (Value argument : body.getArguments().drop_front(sources)) {
    auto anchor = terms.anchor(argument.getType());
    terms.bind(original, argument, anchor);
    parameters.push_back(anchor);
    types.push_back(argument.getType());
  }
  // Bind every occurrence independently, including unused or equal queries.
  // Actual helper calls are interpreted in their own symbol tables; names do
  // not substitute for body correspondence.
  for (auto query : queries) {
    auto anchor = terms.anchor(query.getAnswer().getType());
    terms.bind(original, query.getAnswer(), anchor);
    answers.push_back(anchor);
  }
  auto compare = [&](func::FuncOp function, Value expected,
                     ArrayRef<mathematical::ValueCorrespondence::Term> inputs,
                     TypeRange inputTypes) {
    if (!function || function->getParentOp() != unit || !function.isPrivate() ||
        !function.getBody().hasOneBlock() ||
        !equal(function.getArgumentTypes(), inputTypes) ||
        !equal(function.getResultTypes(), TypeRange(expected.getType())))
      return false;
    auto returned = dyn_cast<func::ReturnOp>(function.front().back());
    if (!returned || returned.getNumOperands() != 1)
      return false;
    auto target = terms.environment();
    for (auto [argument, input] : zip(function.getArguments(), inputs))
      terms.bind(target, argument, input);
    return terms.compare(original, expected, target, returned.getOperand(0));
  };
  for (auto [expected, function] : zip(queries, actual.queries)) {
    auto argument = cast<BlockArgument>(expected.getHandle());
    if (function.source != argument.getArgNumber() ||
        function.site != expected.getSite() ||
        function.kind != expected.getHandle().getType().getKind() ||
        !compare(function.position, expected.getPosition(), parameters, types))
      return refuse();
  }
  append_range(parameters, answers);
  for (auto query : queries)
    types.push_back(query.getAnswer().getType());
  if (!compare(actual.answer,
               cast<protocol_ir::OracleYieldOp>(body.back()).getAnswer(),
               parameters, types))
    return refuse();
  return Error::success();
}
} // namespace zkc::protocol
