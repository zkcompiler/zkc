#include "OracleAnchorStorage.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
Error checkOracleAnchorAllocator(ModuleOp candidate, func::FuncOp actual,
                                 const OracleAnchorStorage &plan,
                                 unsigned constructor, unsigned role) {
  auto refuse = [] { return error("oracle-storage-allocation-body"); };
  if (!candidate || !actual || failed(verify(candidate)) ||
      !hasSingleElement(candidate.getBody()->getOperations()) ||
      constructor >= plan.constructors.size() ||
      role >= plan.constructors[constructor].roles.size())
    return refuse();
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol ||
      actual->getParentOp() != unit)
    return refuse();
  const auto &layout = plan.constructors[constructor];
  const auto &storage = layout.roles[role];
  auto reference = oracleReferenceType(layout.kind);
  if (!reference)
    return reference.takeError();
  auto record = encodeBoundType(storage.record, false);
  if (!record)
    return record.takeError();
  SmallVector<Type> arguments{runtime::ScopeType::get(candidate.getContext()),
                              storage.sequence};
  for (const auto &field : storage.fields)
    arguments.push_back(field.type);
  auto outcome = exec::OutcomeType::get(candidate.getContext(),
                                        {*reference, storage.sequence});
  if (!equal(actual.getArgumentTypes(), arguments) ||
      !equal(actual.getResultTypes(), TypeRange(outcome)))
    return refuse();
  auto closure = readSourceExecutionClosure(unit);
  if (!closure)
    return closure.takeError();
  auto found = closure->bodies.find(actual.getSymName().str());
  if (found == closure->bodies.end() || found->second.size() != 6)
    return refuse();
  const auto &steps = found->second;
  auto site = [](const SourceExecutionStep &step, StringRef name) {
    auto site = step.operation->getAttrOfType<StringAttr>("site");
    return site && site.getValue() == name && step.regions.empty();
  };
  auto call = [&](unsigned n, StringRef contract, ArrayRef<std::string> statics,
                  ValueRange inputs, Type output, StringRef name,
                  ArrayRef<std::string> parameters = {}) {
    const auto &step = steps[n];
    auto op = dyn_cast<exec::ApplyOp>(step.operation);
    if (!op || !site(step, name) || !equal(inputs, step.inputs) ||
        step.outputs.size() != 1 || step.outputs[0].getType() != output)
      return false;
    auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        op, op.getBindingAttr());
    if (!binding || binding.getContract() != contract ||
        !binding.getImplementation().empty() ||
        binding.getArguments().size() != statics.size() ||
        op.getParameters().size() != parameters.size())
      return false;
    for (auto [value, expected] : zip(binding.getArguments(), statics))
      if (dyn_cast<StringAttr>(value).getValue() != expected)
        return false;
    for (auto [value, expected] : zip(op.getParameters(), parameters))
      if (cast<StringAttr>(value).getValue() != expected)
        return false;
    return true;
  };
  auto pack = [&](unsigned n, Type type, ValueRange inputs, StringRef name) {
    const auto &step = steps[n];
    auto op = dyn_cast<exec::VariantOp>(step.operation);
    return op && op.getAlternative() == "Record" && site(step, name) &&
           equal(inputs, step.inputs) && step.outputs.size() == 1 &&
           step.outputs[0].getType() == type;
  };
  auto index =
      IntegerType::get(candidate.getContext(), 64, IntegerType::Unsigned);
  if (!call(0, "index.constant", {}, {}, index, "constructor",
            {std::to_string(constructor)}) ||
      !call(1, "sequence.length", {record->spelling()}, actual.getArgument(1),
            index, "length") ||
      !pack(2, storage.record, actual.getArguments().drop_front(2), "record"))
    return refuse();
  if (!call(3, "sequence.append", {record->spelling()},
            {actual.getArgument(1), steps[2].outputs[0]}, storage.sequence,
            "append") ||
      !pack(4, *reference, {steps[0].outputs[0], steps[1].outputs[0]},
            "reference") ||
      !isa<exec::ReturnOp>(steps[5].operation) || !steps[5].regions.empty() ||
      !equal(steps[5].inputs,
             SmallVector<Value>{steps[4].outputs[0], steps[3].outputs[0]}))
    return refuse();
  return Error::success();
}
Error checkOracleAnchorLookup(ModuleOp candidate, func::FuncOp actual,
                              const OracleAnchorStorage &plan,
                              unsigned constructor, unsigned role) {
  auto refuse = [] { return error("oracle-storage-lookup-body"); };
  if (!candidate || !actual || failed(verify(candidate)) ||
      !hasSingleElement(candidate.getBody()->getOperations()) ||
      constructor >= plan.constructors.size() ||
      role >= plan.constructors[constructor].roles.size())
    return refuse();
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol ||
      actual->getParentOp() != unit)
    return refuse();
  const auto &layout = plan.constructors[constructor];
  const auto &storage = layout.roles[role];
  auto reference = oracleReferenceType(layout.kind);
  if (!reference)
    return reference.takeError();
  auto record = encodeBoundType(storage.record, false);
  if (!record)
    return record.takeError();
  SmallVector<Type> fields;
  for (const auto &field : storage.fields)
    fields.push_back(field.type);
  auto index =
      IntegerType::get(candidate.getContext(), 64, IntegerType::Unsigned);
  auto outcome = exec::OutcomeType::get(candidate.getContext(), fields);
  auto signature = [&](func::FuncOp function, TypeRange inputs, bool region) {
    SmallVector<Type> types{runtime::ScopeType::get(candidate.getContext())};
    append_range(types, inputs);
    return function && equal(function.getArgumentTypes(), types) &&
           equal(function.getResultTypes(), TypeRange(outcome)) &&
           function->hasAttr("runtime.region") == region;
  };
  if (!signature(actual, TypeRange{*reference, storage.sequence}, false))
    return refuse();
  auto closure = readSourceExecutionClosure(unit);
  if (!closure)
    return closure.takeError();
  auto steps = [&](func::FuncOp function,
                   unsigned count) -> const std::vector<SourceExecutionStep> * {
    if (!function)
      return nullptr;
    auto found = closure->bodies.find(function.getSymName().str());
    return found != closure->bodies.end() && found->second.size() == count
               ? &found->second
               : nullptr;
  };
  auto match = [&](const SourceExecutionStep &step, StringRef site,
                   ValueRange inputs) {
    auto op = dyn_cast<exec::MatchOp>(step.operation);
    return op && op.getSite() == site && op.getAlternatives().size() == 1 &&
           cast<StringAttr>(op.getAlternatives()[0]).getValue() == "Record" &&
           equal(step.inputs, inputs) &&
           equal(ValueRange(step.outputs).getTypes(), fields) &&
           step.regions.size() == 1;
  };
  auto terminal = [](const SourceExecutionStep &step, ValueRange inputs,
                     bool region) {
    return (region ? isa<exec::CompleteOp>(step.operation)
                   : isa<exec::ReturnOp>(step.operation)) &&
           step.regions.empty() && equal(step.inputs, inputs);
  };
  auto root = steps(actual, 2);
  if (!root ||
      !match((*root)[0], "reference", actual.getArguments().drop_front()) ||
      !terminal((*root)[1], (*root)[0].outputs, false))
    return refuse();
  auto selected = (*root)[0].regions[0];
  if (!signature(selected, TypeRange{index, index, storage.sequence}, true))
    return refuse();
  auto body = steps(selected, 6);
  if (!body)
    return refuse();
  auto call = [&](unsigned i, StringRef contract,
                  ArrayRef<std::string> arguments, TypeRange outputs,
                  ValueRange inputs, StringRef site,
                  ArrayRef<std::string> parameters = {}) {
    const auto &step = (*body)[i];
    auto op = dyn_cast<exec::ApplyOp>(step.operation);
    if (!op || op.getSite() != site || !step.regions.empty() ||
        !equal(step.inputs, inputs) ||
        !equal(ValueRange(step.outputs).getTypes(), outputs) ||
        op.getParameters().size() != parameters.size())
      return false;
    auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        op, op.getBindingAttr());
    if (!binding || binding.getContract() != contract ||
        !binding.getImplementation().empty() ||
        binding.getArguments().size() != arguments.size())
      return false;
    for (auto [value, expected] : zip(binding.getArguments(), arguments))
      if (cast<StringAttr>(value).getValue() != expected)
        return false;
    for (auto [value, expected] : zip(op.getParameters(), parameters))
      if (cast<StringAttr>(value).getValue() != expected)
        return false;
    return true;
  };
  if (!call(0, "index.constant", {}, index, {}, "constructor",
            {std::to_string(constructor)}))
    return refuse();
  if (!call(1, "index.equal", {}, IntegerType::get(candidate.getContext(), 1),
            {selected.getArgument(1), (*body)[0].outputs[0]}, "belongs_to") ||
      !call(2, "control.require", {}, {}, (*body)[1].outputs,
            "admit_reference") ||
      !call(3, "sequence.at", {record->spelling()}, storage.record,
            {selected.getArgument(3), selected.getArgument(2)}, "lookup"))
    return refuse();
  if (!match((*body)[4], "record", (*body)[3].outputs) ||
      !terminal((*body)[5], (*body)[4].outputs, true))
    return refuse();
  auto unpacked = (*body)[4].regions[0];
  auto unpack = steps(unpacked, 1);
  if (!signature(unpacked, fields, true) || !unpack ||
      !terminal((*unpack)[0], unpacked.getArguments().drop_front(), true))
    return refuse();
  return Error::success();
}
} // namespace zkc::protocol
