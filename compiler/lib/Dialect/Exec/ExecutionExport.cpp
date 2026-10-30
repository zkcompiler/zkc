#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/ExecutionModel.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Program/Admission.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
// The sole native-view to LocalDefinitions adapter. It does not read CFG or
// establish native validity. Reconstruction uses an already admitted immutable
// association; the independent Program reader owns the resulting byte grammar.
class DefinitionExporter {
  const SourceExecutionClosure &closure;
  bool physical;
  unsigned next = 0, remaining = 1000000;
  llvm::DenseMap<Type, std::string> types;
  std::string problem;
  using Environment = llvm::DenseMap<Value, std::string>;

  bool fail(StringRef detail) {
    if (problem.empty())
      problem = detail.str();
    return false;
  }
  bool charge() {
    return remaining ? (--remaining, true) : fail("export work limit");
  }
  std::string fresh() { return "v" + std::to_string(next++); }
  std::string type(Type value) {
    auto found = types.find(value);
    if (found != types.end())
      return found->second;
    auto encoded = encodeBoundType(value, physical);
    if (!encoded) {
      consumeError(encoded.takeError());
      fail("type outside byte grammar");
      return {};
    }
    return types.try_emplace(value, encoded->spelling()).first->second;
  }
  program::Names names(ValueRange values, const Environment &environment) {
    program::Names result;
    for (Value value : values) {
      auto found = environment.find(value);
      if (!charge() || found == environment.end()) {
        fail("unassociated data value");
        return {};
      }
      result.push_back(found->second);
    }
    return result;
  }
  program::Names outputs(ValueRange values, Environment &environment) {
    program::Names result;
    for (Value value : values) {
      if (!charge() || environment.contains(value)) {
        fail("duplicate exported value");
        return {};
      }
      auto name = fresh();
      environment[value] = name;
      result.push_back(std::move(name));
    }
    return result;
  }
  program::Body body(func::FuncOp function, ArrayRef<std::string> arguments,
                     unsigned depth = 0) {
    program::Body result;
    if (depth >= 64 || function.getNumArguments() != arguments.size() + 1) {
      fail("region interface or depth");
      return {};
    }
    auto found = closure.bodies.find(function.getSymName().str());
    if (found == closure.bodies.end()) {
      fail("missing native body association");
      return {};
    }
    Environment environment;
    for (auto [value, name] :
         zip(function.getArguments().drop_front(), arguments))
      environment[value] = name;
    for (const auto &step : found->second) {
      if (!charge())
        return {};
      Operation *op = step.operation;
      auto inputs = names(step.inputs, environment);
      auto results = outputs(step.outputs, environment);
      if (!problem.empty())
        return {};
      auto site = op->getAttrOfType<StringAttr>(
          isa<func::CallOp>(op) ? "runtime.site" : "site");
      program::Instruction instruction;
      instruction.site = site ? site.str() : "";
      if (auto apply = dyn_cast<exec::ApplyOp>(op)) {
        auto parameters = encodeInvocationParameters(apply);
        if (!parameters) {
          consumeError(parameters.takeError());
          fail("invocation parameters outside byte grammar");
          return {};
        }
        instruction.value =
            program::Operation{apply.getBinding().str(), std::move(*parameters),
                               std::move(inputs), std::move(results)};
      } else if (auto call = dyn_cast<func::CallOp>(op)) {
        instruction.value = program::LocalApply{
            call.getCallee().str(), std::move(inputs), std::move(results)};
      } else if (auto literal = dyn_cast<exec::BooleanOp>(op)) {
        instruction.value =
            program::BooleanConstant{results.front(), literal.getValue()};
      } else if (isa<exec::TestOp>(op)) {
        program::Conditional branch;
        branch.condition = inputs.front();
        auto captures = ArrayRef(inputs).drop_front();
        append_range(branch.captures, captures);
        branch.thenBody = body(step.regions[0], captures, depth + 1);
        branch.elseBody = body(step.regions[1], captures, depth + 1);
        branch.outputs = std::move(results);
        instruction.value = std::move(branch);
      } else if (auto variant = dyn_cast<exec::VariantOp>(op)) {
        instruction.value = program::VariantConstruct{
            type(step.outputs.front().getType()),
            variant.getAlternative().str(), std::move(inputs), results.front()};
      } else if (auto match = dyn_cast<exec::MatchOp>(op)) {
        program::Match selected;
        selected.input = inputs.front();
        auto captures = ArrayRef(inputs).drop_front();
        append_range(selected.captures, captures);
        for (auto [i, selectedRegion] : enumerate(step.regions)) {
          auto region = selectedRegion;
          program::MatchArm arm;
          arm.alternative = cast<StringAttr>(match.getAlternatives()[i]).str();
          unsigned payload = region.getNumArguments() - 1 - captures.size();
          for (unsigned j = 0; j < payload; ++j)
            arm.payload.push_back(fresh());
          program::Names formals = arm.payload;
          append_range(formals, captures);
          arm.body = body(region, formals, depth + 1);
          selected.arms.push_back(std::move(arm));
        }
        selected.outputs = std::move(results);
        instruction.value = std::move(selected);
      } else if (isa<exec::RangeOp>(op)) {
        program::For loop;
        loop.lower = inputs[0];
        loop.upper = inputs[1];
        loop.induction = fresh();
        loop.conditional = step.conditional;
        program::Names formals{loop.induction};
        for (const auto &initial : ArrayRef(inputs).slice(2, results.size())) {
          auto name = fresh();
          loop.carried.emplace_back(name, initial);
          formals.push_back(std::move(name));
        }
        auto captures = ArrayRef(inputs).drop_front(2 + results.size());
        append_range(loop.captures, captures);
        append_range(formals, captures);
        loop.body = body(step.regions.front(), formals, depth + 1);
        loop.outputs = std::move(results);
        instruction.value = std::move(loop);
      } else if (isa<runtime::ReleaseBindingsOp>(op)) {
        instruction.value = program::Release{std::move(inputs)};
      } else if (isa<exec::ReturnOp, exec::CompleteOp>(op)) {
        if (function->hasAttr("runtime.region"))
          instruction.value = program::Yield{std::move(inputs)};
        else
          instruction.value = program::Return{std::move(inputs)};
      } else if (auto reject = dyn_cast<exec::RejectOp>(op)) {
        instruction.value = program::Stop{reject.getReason().str()};
      } else {
        fail("unresolved request outside byte grammar");
      }
      if (!problem.empty())
        return {};
      result.push_back(std::move(instruction));
    }
    return result;
  }

public:
  DefinitionExporter(const SourceExecutionClosure &closure, bool physical)
      : closure(closure), physical(physical) {}
  Expected<program::LocalDefinitions> run(Operation *owner, bool source) {
    program::LocalDefinitions result;
    for (Operation &op : owner->getRegion(0).front()) {
      if (auto binding = dyn_cast<runtime::BindingOp>(op)) {
        auto encoded = readBinding(binding);
        if (!encoded)
          return encoded.takeError();
        result.bindings.push_back(std::move(*encoded));
        continue;
      }
      auto function = dyn_cast<func::FuncOp>(op);
      if (!function || !isScopedExecutionFunction(function) ||
          function->hasAttr("runtime.region"))
        continue;
      program::Function record;
      record.name = function.getSymName().str();
      auto origin = function->getAttrOfType<ArrayAttr>("runtime.origin");
      record.origin =
          program::LogicalOrigin{cast<StringAttr>(origin[0]).str(), {}};
      for (Attribute value : cast<ArrayAttr>(origin[1])) {
        auto pair = cast<ArrayAttr>(value);
        record.origin->arguments.emplace_back(cast<StringAttr>(pair[0]).str(),
                                              cast<StringAttr>(pair[1]).str());
      }
      program::Names arguments;
      for (Value value : function.getArguments().drop_front()) {
        arguments.push_back(fresh());
        record.arguments.push_back({arguments.back(), type(value.getType())});
      }
      auto signature = scopedDataSignature(function);
      for (Type value : signature.getResults())
        record.results.push_back(type(value));
      record.body = body(function, arguments);
      if (!problem.empty())
        return error("execution-cfg", problem);
      result.functions.push_back(std::move(record));
    }
    if (auto e = source ? admitNativeLocalDefinitions(result)
                        : admitExecutionDefinitions(result, physical))
      return std::move(e);
    return result;
  }
};
} // namespace
Expected<program::LocalDefinitions> readLocalExecution(ModuleOp module,
                                                       bool physical) {
  if (!module || failed(verify(module)) || !module->getAttrs().empty() ||
      any_of(module.getBody()->getOperations(), [](Operation &op) {
        return !isa<runtime::BindingOp, func::FuncOp>(op);
      }))
    return error("execution-cfg", "expected a verified local execution module");
  return readExecutionDefinitions(module, physical);
}
Expected<program::LocalDefinitions> readExecutionDefinitions(Operation *owner,
                                                             bool physical) {
  auto view = readExecutionClosure(owner, physical);
  if (!view)
    return view.takeError();
  return DefinitionExporter(*view, physical).run(owner, false);
}
Expected<program::LocalDefinitions>
readSourceExecutionDefinitions(Operation *owner) {
  auto view = readSourceExecutionClosure(owner);
  if (!view)
    return view.takeError();
  if (!view->computations.empty())
    return error("execution-cfg", "unresolved computations cannot be exported");
  return DefinitionExporter(*view, false).run(owner, true);
}
Expected<program::LocalDefinitions>
readScheduledExecutionDefinitions(Operation *owner) {
  auto view = readScheduledExecutionClosure(owner);
  if (!view)
    return view.takeError();
  return DefinitionExporter(*view, false).run(owner, true);
}
} // namespace zkc::protocol
