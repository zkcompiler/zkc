#include "ExecutionAttributes.h"
#include "ExecutionDefinitions.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/ControlCursor.h"
#include "zkc/Dialect/Exec/ExecutionModel.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Runtime/Execution.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Program/Admission.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Support/TimeProfiler.h"
#include <map>

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
// Record-directed comparison of actual SSA. Do not reconstruct an expected
// program with readLocalExecution or replay the emission implementation here.
bool attrs(Operation *op, ArrayRef<StringRef> names = {}) {
  return exec::detail::hasOnlyExecutionAttributes(op, names);
}
bool strings(ArrayAttr actual, ArrayRef<std::string> expected) {
  if (!actual || actual.size() != expected.size())
    return false;
  for (auto [a, e] : zip(actual, expected))
    if (!isa<StringAttr>(a) || cast<StringAttr>(a).getValue() != e)
      return false;
  return true;
}
bool returns(Operation *operation, Value value) {
  auto returned = dyn_cast_or_null<func::ReturnOp>(operation);
  return returned && attrs(returned) &&
         returned.getOperands() == ValueRange{value};
}
class Comparison;
class BodyComparison {
  Comparison &owner;
  func::FuncOp function;
  Value scope;
  exec::ControlCursor control;
  llvm::DenseSet<Value> bound;
  llvm::StringMap<Value> names;
  bool enter(Block *block) { return control.enter(block); }
  Operation *take() { return control.take(); }
  bool end() const { return control.atEnd(); }
  bool inputs(ValueRange, ArrayRef<std::string>) const;
  bool bind(ValueRange, ArrayRef<std::string>);
  bool stop(Block *block) { return control.failure(block); }
  bool dispatch(Value value, SmallVectorImpl<Value> &payload,
                Block *failed = nullptr) {
    return control.dispatch(value, payload, failed);
  }
  std::optional<SmallVector<Value>> values(ArrayRef<std::string>) const;
  bool conditional(const program::Instruction &, const program::Conditional &);
  bool match(const program::Instruction &, const program::Match &);
  bool loop(const program::Instruction &, const program::For &);

public:
  BodyComparison(Comparison &owner, func::FuncOp function, unsigned &remaining)
      : owner(owner), function(function), control(function, remaining) {}
  bool run(const program::Body &, ArrayRef<std::string> arguments);
};
class Comparison {
  Operation *module;
  bool physical, source;
  unsigned remaining = 1000000;
  llvm::DenseSet<Operation *> active, visited;
  std::map<std::string, BoundOperation> bindings;

public:
  Comparison(Operation *module, bool physical, bool source = false)
      : module(module), physical(physical), source(source) {}
  bool isSource() const { return source; }
  bool helper(func::CallOp call, const program::LocalApply &record) {
    if (!source || call.getCallee() != record.callee ||
        call.getNumResults() != 1 ||
        !isa<exec::OutcomeType>(call.getResult(0).getType()))
      return false;
    auto function = dyn_cast_or_null<func::FuncOp>(
        SymbolTable::lookupSymbolIn(module, call.getCallee()));
    return function && !function.isExternal() &&
           !function->hasAttr("runtime.region") &&
           function->hasAttr("runtime.origin");
  }
  bool charge() { return remaining && (--remaining, true); }
  bool type(Type actual, StringRef expected = {}) const {
    auto bound = encodeBoundType(actual, physical);
    if (!bound) {
      consumeError(bound.takeError());
      return false;
    }
    return expected.empty() || bound->spelling() == expected;
  }
  bool application(exec::ApplyOp call, const program::Operation &record) {
    auto found = bindings.find(record.callee);
    if (found == bindings.end())
      return false;
    const auto &expected = found->second;
    auto outputs = call.getOutcome().getType().getPayload();
    if (call.getInputs().size() != expected.inputs.size() ||
        outputs.size() != expected.outputs.size())
      return false;
    for (auto [actual, port] :
         zip(call.getInputs().getTypes(), expected.inputs))
      if (!type(actual, port.spelling()))
        return false;
    for (auto [actual, port] : zip(outputs, expected.outputs))
      if (!type(actual, port.spelling()))
        return false;
    auto declaration = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        call, call.getBindingAttr());
    return declaration && call.getBinding() == record.callee &&
           invocationParametersMatch(
               declaration.getContract(), declaration.getArgumentsAttr(),
               call.getParametersAttr(), record.attributes,
               physical ? ParameterStage::Physical : ParameterStage::Logical);
  }
  bool body(func::FuncOp function, const program::Body &expected,
            ArrayRef<std::string> arguments, bool outlined) {
    if (!function || function.isExternal() || !function.getNoInline() ||
        function.getNumArguments() != arguments.size() + 1 ||
        !isa<runtime::ScopeType>(function.getArgument(0).getType()) ||
        function.getFunctionType().getNumResults() != 1 ||
        !isa<exec::OutcomeType>(function.getResultTypes().front()) ||
        !attrs(function, {"sym_name", "sym_visibility", "function_type",
                          "no_inline", "runtime.origin", "runtime.region"}) ||
        (outlined ? !function.isPrivate() ||
                        !function->getAttrOfType<UnitAttr>("runtime.region") ||
                        function->hasAttr("runtime.origin")
                  : function->hasAttr("runtime.region")) ||
        active.size() >= 64 || !active.insert(function).second)
      return false;
    visited.insert(function);
    bool valid = succeeded(runtime::verifyScopeOwnership(function));
    for (TypeRange ports :
         {TypeRange(function.getArgumentTypes().drop_front()),
          TypeRange(cast<exec::OutcomeType>(function.getResultTypes().front())
                        .getPayload())})
      for (Type port : ports)
        valid &= type(port);
    if (valid)
      valid =
          BodyComparison(*this, function, remaining).run(expected, arguments);
    active.erase(function);
    return valid;
  }
  bool call(func::CallOp call, const program::Body &expected,
            ArrayRef<std::string> arguments) {
    return body(dyn_cast_or_null<func::FuncOp>(
                    SymbolTable::lookupSymbolIn(module, call.getCallee())),
                expected, arguments, true);
  }
  bool run(const program::LocalDefinitions &expected, bool mixed = false);
};
std::optional<SmallVector<Value>>
BodyComparison::values(ArrayRef<std::string> expected) const {
  SmallVector<Value> result;
  for (const auto &name : expected) {
    auto found = names.find(name);
    if (found == names.end())
      return std::nullopt;
    result.push_back(found->second);
  }
  return result;
}
bool BodyComparison::inputs(ValueRange actual,
                            ArrayRef<std::string> expected) const {
  auto selected = values(expected);
  return selected && actual == ValueRange(*selected);
}
bool BodyComparison::bind(ValueRange actual, ArrayRef<std::string> expected) {
  if (actual.size() != expected.size())
    return false;
  for (auto [value, name] : zip(actual, expected))
    if (!owner.type(value.getType()) || !bound.insert(value).second ||
        !names.try_emplace(name, value).second)
      return false;
  return true;
}
bool BodyComparison::conditional(const program::Instruction &instruction,
                                 const program::Conditional &record) {
  auto condition = values({record.condition}),
       captures = values(record.captures);
  SmallVector<Value> outputs;
  return condition && captures &&
         control.conditional(
             condition->front(), *captures, instruction.site,
             [&](func::CallOp call, unsigned arm) {
               return owner.call(call, arm ? record.elseBody : record.thenBody,
                                 record.captures);
             },
             outputs) &&
         bind(outputs, record.outputs);
}
bool BodyComparison::match(const program::Instruction &instruction,
                           const program::Match &record) {
  auto input = values({record.input}), captures = values(record.captures);
  SmallVector<std::string> alternatives;
  for (const auto &arm : record.arms)
    alternatives.push_back(arm.alternative);
  SmallVector<Value> outputs;
  return input && captures &&
         control.match(
             input->front(), *captures, alternatives, instruction.site,
             [&](func::CallOp call, unsigned arm) {
               program::Names arguments = record.arms[arm].payload;
               append_range(arguments, record.captures);
               return owner.call(call, record.arms[arm].body, arguments);
             },
             outputs) &&
         bind(outputs, record.outputs);
}
bool BodyComparison::loop(const program::Instruction &instruction,
                          const program::For &record) {
  program::Names seedNames, arguments{record.induction};
  for (const auto &[name, seed] : record.carried) {
    seedNames.push_back(seed);
    arguments.push_back(name);
  }
  append_range(arguments, record.captures);
  auto bounds = values({record.lower, record.upper}), seeds = values(seedNames),
       captures = values(record.captures);
  SmallVector<Value> outputs;
  return bounds && seeds && captures &&
         control.loop((*bounds)[0], (*bounds)[1], *seeds, *captures,
                      record.conditional, instruction.site,
                      [&](func::CallOp call, unsigned) {
                        return owner.call(call, record.body, arguments);
                      },
                      outputs) &&
         bind(outputs, record.outputs);
}
bool BodyComparison::run(const program::Body &expected,
                         ArrayRef<std::string> arguments) {
  scope = function.getArgument(0);
  if (!enter(&function.front()) ||
      !bind(function.getArguments().drop_front(), arguments))
    return false;
  for (const auto &instruction : expected) {
    if (auto record = instruction.get<program::Conditional>()) {
      if (!conditional(instruction, *record))
        return false;
    } else if (auto record = instruction.get<program::Match>()) {
      if (!match(instruction, *record))
        return false;
    } else if (auto record = instruction.get<program::For>()) {
      if (!loop(instruction, *record))
        return false;
    } else if (auto record = instruction.get<program::Operation>()) {
      auto call = dyn_cast_or_null<exec::ApplyOp>(take());
      SmallVector<Value> outputs;
      if (!call || !attrs(call, {"binding", "parameters", "site"}) ||
          call.getScope() != scope || call.getSite() != instruction.site ||
          !inputs(call.getInputs(), record->inputs) ||
          !owner.application(call, *record) ||
          !dispatch(call.getOutcome(), outputs) ||
          !bind(outputs, record->outputs))
        return false;
    } else if (auto record = instruction.get<program::LocalApply>()) {
      auto call = dyn_cast_or_null<func::CallOp>(take());
      SmallVector<Value> outputs;
      if (!call || !attrs(call, {"callee", "runtime.site"}) ||
          !owner.helper(call, *record) ||
          call->getAttrOfType<StringAttr>("runtime.site") !=
              StringAttr::get(function.getContext(), instruction.site) ||
          call.getNumOperands() == 0 || call.getOperand(0) != scope ||
          !inputs(call.getOperands().drop_front(), record->inputs) ||
          !dispatch(call.getResult(0), outputs) ||
          !bind(outputs, record->outputs))
        return false;
    } else if (auto record = instruction.get<program::BooleanConstant>()) {
      auto value = dyn_cast_or_null<exec::BooleanOp>(take());
      SmallVector<Value> outputs;
      if (!value || !attrs(value, {"value", "site"}) ||
          value.getScope() != scope || value.getValue() != record->value ||
          value.getSite() != instruction.site ||
          !dispatch(value.getOutcome(), outputs) ||
          !bind(outputs, {record->output}))
        return false;
    } else if (auto record = instruction.get<program::VariantConstruct>()) {
      auto value = dyn_cast_or_null<exec::VariantOp>(take());
      SmallVector<Value> outputs;
      if (!value || !attrs(value, {"alternative", "site"}) ||
          value.getScope() != scope ||
          value.getAlternative() != record->alternative ||
          value.getSite() != instruction.site ||
          !inputs(value.getPayload(), record->payload) ||
          !owner.type(value.getOutcome().getType().getPayload().front(),
                      record->type) ||
          !dispatch(value.getOutcome(), outputs) ||
          !bind(outputs, {record->output}))
        return false;
    } else if (auto record = instruction.get<program::Release>()) {
      auto release = dyn_cast_or_null<runtime::ReleaseBindingsOp>(take());
      if (!release || !attrs(release) || release.getScope() != scope ||
          !inputs(release.getValues(), record->values))
        return false;
    } else if (auto record = instruction.get<program::Stop>()) {
      auto reject = dyn_cast_or_null<exec::RejectOp>(take());
      auto branch = dyn_cast_or_null<cf::BranchOp>(take());
      if (!reject || !attrs(reject, {"site", "reason"}) ||
          reject.getScope() != scope || reject.getReason() != record->reason ||
          reject.getSite() != instruction.site || !branch || !attrs(branch) ||
          branch.getDestOperands() != ValueRange{reject.getStop()} || !end() ||
          !stop(branch.getDest()))
        return false;
    } else if (instruction.get<program::Return>() ||
               instruction.get<program::Yield>()) {
      const auto &expectedValues =
          instruction.get<program::Return>()
              ? instruction.get<program::Return>()->values
              : instruction.get<program::Yield>()->values;
      if (owner.isSource() && instruction.get<program::Return>()) {
        auto returnedValue = dyn_cast_or_null<exec::ReturnOp>(take());
        if (!returnedValue || !attrs(returnedValue) ||
            !inputs(returnedValue.getValues(), expectedValues) ||
            !returns(take(), returnedValue.getOutcome()) || !end())
          return false;
      } else {
        auto complete = dyn_cast_or_null<exec::CompleteOp>(take());
        if (!complete || !attrs(complete) || complete.getScope() != scope ||
            !inputs(complete.getValues(), expectedValues) ||
            !returns(take(), complete.getOutcome()) || !end())
          return false;
      }
    } else
      return false;
  }
  return control.complete();
}
bool Comparison::run(const program::LocalDefinitions &expected, bool mixed) {
  llvm::TimeTraceScope timing("zkc.execution-comparison");
  for (const auto &binding : expected.bindings) {
    auto signature = resolveBinding(binding.application, physical);
    if (!signature) {
      consumeError(signature.takeError());
      return false;
    }
    bindings.emplace(binding.name, std::move(*signature));
  }
  unsigned binding = 0, root = 0, definitions = 0;
  for (Operation &op : module->getRegion(0).front()) {
    if (!charge() ||
        (isa<func::FuncOp, data::DomainOp>(op) &&
         !(isa<func::FuncOp>(op) && op.hasAttr("runtime.region")) &&
         ++definitions > 4096))
      return false;
    if (auto declaration = dyn_cast<runtime::BindingOp>(op)) {
      if (binding >= 4096 || binding == expected.bindings.size() ||
          !attrs(declaration,
                 {"sym_name", "contract", "arguments", "implementation",
                  "function_type", "arg_attrs", "res_attrs"}))
        return false;
      const auto &record = expected.bindings[binding++];
      if (!bindingMatches(declaration, record, physical))
        return false;
      continue;
    }
    auto function = dyn_cast<func::FuncOp>(op);
    if (!function) {
      if (mixed)
        continue;
      return false;
    }
    if (source && !isScopedExecutionFunction(function))
      continue;
    if (function->getAttrOfType<UnitAttr>("runtime.region"))
      continue;
    if (root == expected.functions.size())
      return false;
    const auto &record = expected.functions[root++];
    auto origin = function->getAttrOfType<ArrayAttr>("runtime.origin");
    if (function.getSymName() != record.name || !record.origin || !origin ||
        origin.size() != 2 || !isa<StringAttr>(origin[0]) ||
        cast<StringAttr>(origin[0]).getValue() != record.origin->definition ||
        !isa<ArrayAttr>(origin[1]) ||
        cast<ArrayAttr>(origin[1]).size() != record.origin->arguments.size() ||
        function.getNumArguments() != record.arguments.size() + 1 ||
        function.getFunctionType().getNumResults() != 1)
      return false;
    for (auto [actual, pair] :
         zip(cast<ArrayAttr>(origin[1]), record.origin->arguments)) {
      auto row = dyn_cast<ArrayAttr>(actual);
      if (!row || !strings(row, {pair.first, pair.second}))
        return false;
    }
    auto result =
        dyn_cast<exec::OutcomeType>(function.getResultTypes().front());
    if (!result || result.getPayload().size() != record.results.size())
      return false;
    program::Names arguments;
    for (auto [actual, port] :
         zip(function.getArgumentTypes().drop_front(), record.arguments)) {
      if (!type(actual, port.type))
        return false;
      arguments.push_back(port.name);
    }
    for (auto [actual, port] : zip(result.getPayload(), record.results))
      if (!type(actual, port))
        return false;
    if (!body(function, record.body, arguments, false))
      return false;
  }
  if (binding != expected.bindings.size() || root != expected.functions.size())
    return false;
  for (auto function : module->getRegion(0).front().getOps<func::FuncOp>())
    if ((!source || isScopedExecutionFunction(function)) &&
        !visited.contains(function))
      return false;
  return true;
}
} // namespace
Error verifyLocalExecution(ModuleOp module,
                           const program::LocalDefinitions &expected,
                           bool physical) {
  if (!module || failed(verify(module)) || !module->getAttrs().empty())
    return error("execution-correspondence-subject");
  if (auto e = admitExecutionDefinitions(expected, physical))
    return e;
  Comparison checker(module, physical);
  if (!checker.run(expected))
    return error("execution-correspondence");
  return Error::success();
}
Error verifyExecutionDefinitions(Operation *symbolTable,
                                 const program::LocalDefinitions &expected,
                                 bool physical) {
  if (failed(detail::verifyExecutionDefinitionScope(symbolTable)))
    return error("execution-correspondence-subject");
  if (auto e = admitExecutionDefinitions(expected, physical))
    return e;
  Comparison checker(symbolTable, physical);
  if (!checker.run(expected, /*mixed=*/true))
    return error("execution-correspondence");
  return Error::success();
}
Error verifySourceExecutionDefinitions(
    Operation *symbolTable, const program::LocalDefinitions &expected) {
  if (failed(detail::verifyExecutionDefinitionScope(symbolTable,
                                                    /*source=*/true)))
    return error("execution-correspondence-subject");
  if (auto e = admitNativeLocalDefinitions(expected))
    return e;
  Comparison checker(symbolTable, /*physical=*/false, /*source=*/true);
  if (!checker.run(expected, /*mixed=*/true))
    return error("execution-correspondence");
  return Error::success();
}
} // namespace zkc::protocol
