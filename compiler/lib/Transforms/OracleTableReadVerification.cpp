#include "OracleTableRead.h"
#include "OracleVerificationContext.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
Error checkOracleTableRead(ModuleOp candidate, func::FuncOp actual,
                           protocol_ir::OracleKindAttr kind) {
  auto context = OracleVerificationContext::read(candidate);
  if (!context) {
    consumeError(context.takeError());
    return error("oracle-table-read-body");
  }
  return checkOracleTableRead(*context, actual, kind);
}
Error checkOracleTableRead(const OracleVerificationContext &context,
                           func::FuncOp actual,
                           protocol_ir::OracleKindAttr kind) {
  auto refuse = [] { return error("oracle-table-read-body"); };
  ModuleOp candidate = context.getModule();
  if (!actual || !kind || kind.getIdentity() != "table" ||
      failed(protocol_ir::OracleKindAttr::verify(
          [&]() { return emitError(candidate.getLoc()); }, kind.getIdentity(),
          kind.getArguments())))
    return refuse();
  auto unit = context.getUnit();
  if (actual->getParentOp() != unit)
    return refuse();
  auto index =
      IntegerType::get(candidate.getContext(), 64, IntegerType::Unsigned);
  SmallVector<Type> inputs{runtime::ScopeType::get(candidate.getContext()),
                           kind.getDataType(), index, index};
  auto outcome =
      exec::OutcomeType::get(candidate.getContext(), kind.getAnswerType());
  if (!equal(actual.getArgumentTypes(), inputs) ||
      !equal(actual.getResultTypes(), TypeRange(outcome)))
    return refuse();
  const auto &closure = context.getClosure();
  auto found = closure.bodies.find(actual.getSymName().str());
  if (found == closure.bodies.end() || found->second.size() != 4)
    return refuse();
  const auto &steps = found->second;
  auto call = [&](unsigned i, StringRef contract,
                  ArrayRef<std::string> arguments, ValueRange inputs,
                  TypeRange outputs, StringRef site) {
    const auto &step = steps[i];
    auto op = dyn_cast<exec::ApplyOp>(step.operation);
    if (!op || op.getSite() != site || !step.regions.empty() ||
        !equal(step.inputs, inputs) ||
        !equal(ValueRange(step.outputs).getTypes(), outputs) ||
        !op.getParameters().empty())
      return false;
    auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        op, op.getBindingAttr());
    if (!binding || binding.getContract() != contract ||
        !binding.getImplementation().empty() ||
        binding.getArguments().size() != arguments.size())
      return false;
    if (!bindingMatches(
            binding,
            {binding.getSymName().str(),
             {contract.str(),
              std::vector<std::string>(arguments.begin(), arguments.end()),
              {}}},
            false))
      return false;
    return true;
  };
  if (!call(0, "index.less", {}, {actual.getArgument(3), actual.getArgument(2)},
            IntegerType::get(candidate.getContext(), 1), "domain"))
    return refuse();
  auto answer = encodeBoundType(kind.getAnswerType(), false);
  if (!answer)
    return answer.takeError();
  std::string contract;
  std::vector<std::string> arguments;
  if (answer->kind == "field" || answer->kind == "group") {
    contract = answer->kind == "field" ? "vector.get" : "curve.get";
    arguments.push_back(answer->identity);
  } else if (answer->kind == "index")
    contract = "indices.at";
  else {
    contract = "sequence.at";
    arguments.push_back(answer->spelling());
  }
  if (!call(1, "control.require", {}, steps[0].outputs, {}, "admit") ||
      !call(2, contract, arguments,
            {actual.getArgument(1), actual.getArgument(3)},
            kind.getAnswerType(), "read") ||
      !isa<exec::ReturnOp>(steps[3].operation) || !steps[3].regions.empty() ||
      !equal(steps[3].inputs, steps[2].outputs))
    return refuse();
  return Error::success();
}
} // namespace zkc::protocol
