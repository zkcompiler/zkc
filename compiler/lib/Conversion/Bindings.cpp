#include "Bindings.h"
#include "../Target/ExecutionPorts.h"
#include "../Target/PhysicalPlan.h"
#include "Storage.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Refusal.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
static Error applyPhysical(ModuleOp module, const target::PhysicalPlan &plan) {
  auto admitted = target::ExecutionPorts::read(module);
  if (!admitted)
    return admitted.takeError();
  const auto &flow = *admitted;
  auto work = target::physicalPlanOperations(module);
  if (work.size() != plan.operations.size())
    return error("binding-plan-coverage");
  auto root =
      cast<zkc::protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  OpBuilder builder(module.getContext());
  for (const auto &decision : plan.bindings) {
    const auto &binding = decision.binding;
    if (decision.purpose == target::BindingPurpose::Original) {
      auto declaration = cast<runtime::BindingOp>(work[*decision.declaration]);
      declaration.setArgumentsAttr(
          builder.getArrayAttr(binding.application.arguments));
      declaration.setImplementation(binding.application.implementation);
      declaration.setFunctionType(
          executableBindingSignature(binding.application.valueType));
    } else {
      builder.setInsertionPointToStart(&root.getBody().front());
      runtime::BindingOp::create(
          builder, work[decision.location]->getLoc(), binding.name,
          binding.application.contract,
          builder.getArrayAttr(binding.application.arguments),
          binding.application.implementation,
          executableBindingSignature(binding.application.valueType),
          ArrayAttr{}, ArrayAttr{});
    }
  }

  // Retain the complete admitted bodies while constructing their replacements.
  // The port index borrows these actual values; no mutation invalidates it.
  OwningOpRef<ModuleOp> retired(ModuleOp::create(module.getLoc()));
  llvm::DenseMap<Operation *, func::FuncOp> functions;
  IRMapping mapping;
  std::map<target::StorageValue, Value> stored;
  std::map<target::StoragePoint, SmallVector<const target::StorageRelease *>>
      releases;
  for (const auto &release : plan.releases)
    releases[release.point].push_back(&release);
  for (auto [index, op] : enumerate(work)) {
    const auto &choice = plan.operations[index];
    if (auto function = dyn_cast<func::FuncOp>(op)) {
      SmallVector<Type> inputs{runtime::ScopeType::get(module.getContext())};
      append_range(inputs, choice.functionType.getInputs());
      auto output = exec::OutcomeType::get(
          module.getContext(),
          SmallVector<Type>(choice.functionType.getResults()));
      auto type = builder.getFunctionType(inputs, output);
      builder.setInsertionPoint(function);
      auto replacement = func::FuncOp::create(builder, function.getLoc(),
                                              function.getSymName(), type);
      replacement->setAttrs(function->getAttrs());
      replacement.setType(type);
      replacement.addEntryBlock();
      functions[function] = replacement;
      for (auto [port, values] :
           enumerate(zip(function.getArguments().drop_front(),
                         replacement.getArguments().drop_front()))) {
        mapping.map(std::get<0>(values), std::get<1>(values));
        stored[{target::StorageValue::BlockArgument, index, unsigned(port),
                0}] = std::get<1>(values);
      }
      function->moveBefore(retired->getBody(), retired->getBody()->end());
      continue;
    }
    if (op->getParentOfType<func::FuncOp>())
      continue;
    // Participant transport remains protocol-owned. Its selected data ports
    // have no scope/outcome administrative values and retain their actual SSA.
    if (choice.functionType)
      op->setAttr("function_type", TypeAttr::get(choice.functionType));
    for (auto [value, type] : zip(flow.outputs(op), choice.outputs))
      value.setType(type);
    unsigned block = 0;
    for (auto *entry : flow.get(op).bodies) {
      const auto &body = flow.body(entry);
      if (body.owner == op) {
        for (auto [value, type] :
             zip(body.arguments, choice.blockArguments[block++]))
          Value(value).setType(type);
      }
    }
    if (!choice.conversions.empty() || choice.binding)
      return error("binding-materialization-context");
  }
  llvm::DenseMap<Operation *, unsigned> indices;
  for (auto [index, op] : enumerate(work))
    indices[op] = index;
  for (auto *op : work) {
    auto source = dyn_cast<func::FuncOp>(op);
    if (!source)
      continue;
    auto function = functions.lookup(source);
    builder.setInsertionPointToEnd(&function.front());
    exec::ScopedExecutionBuilder native(builder, function);
    auto release = [&](target::StoragePoint point) -> Error {
      auto found = releases.find(point);
      if (found == releases.end())
        return Error::success();
      for (auto *chunk : found->second) {
        SmallVector<Value> values;
        for (const auto &coordinate : chunk->values) {
          auto value = stored.find(coordinate);
          if (value == stored.end())
            return error("storage-schedule-coordinate");
          values.push_back(value->second);
        }
        native.release(values);
      }
      releases.erase(found);
      return Error::success();
    };
    if (auto e = release(
            {target::StoragePoint::BlockEntry, indices.lookup(source), 0}))
      return e;
    for (auto *instruction : flow.body(&source.front()).instructions) {
      auto index = indices.lookup(instruction);
      const auto &node = flow.get(instruction);
      const auto &choice = plan.operations[index];
      SmallVector<Value> inputs;
      for (auto input : node.inputs) {
        auto mapped = mapping.lookupOrNull(input);
        if (!mapped)
          return error("binding-materialization-coordinate");
        inputs.push_back(mapped);
      }
      auto invoke = [&](const target::NativeBindingChoice &binding,
                        TypeRange outputs, ValueRange inputs, StringRef site,
                        ArrayAttr parameters) {
        return native.invoke(
            "exec.apply", outputs, native.scoped(inputs),
            {builder.getNamedAttr(
                 "binding",
                 FlatSymbolRefAttr::get(module.getContext(), binding.name)),
             builder.getNamedAttr("parameters", parameters),
             builder.getNamedAttr("site", builder.getStringAttr(site))});
      };
      for (auto [crossing, conversion] : enumerate(choice.conversions)) {
        auto converted =
            invoke(plan.bindings[conversion.binding].binding,
                   TypeRange{conversion.to}, inputs[conversion.operand],
                   conversion.site, builder.getArrayAttr({}));
        inputs[conversion.operand] = converted.front();
        stored[{target::StorageValue::ConversionResult, index,
                unsigned(crossing)}] = converted.front();
        if (auto e = release({target::StoragePoint::AfterConversion, index,
                              unsigned(crossing)}))
          return e;
      }
      SmallVector<Value> outputs;
      auto site = instruction->getAttrOfType<StringAttr>("site");
      auto body = [&](unsigned arm) {
        return functions.lookup(flow.body(node.bodies[arm]).owner);
      };
      if (choice.binding) {
        outputs = invoke(plan.bindings[*choice.binding].binding, choice.outputs,
                         inputs, site.getValue(),
                         instruction->getAttrOfType<ArrayAttr>("parameters"));
      } else if (isa<exec::BooleanOp, exec::VariantOp>(instruction)) {
        outputs =
            native.invoke(instruction->getName().getStringRef(), choice.outputs,
                          native.scoped(inputs), instruction->getAttrs());
      } else if (isa<exec::TestOp>(instruction)) {
        outputs =
            native.conditional(inputs.front(), ArrayRef(inputs).drop_front(),
                               choice.outputs, site.getValue(), body);
      } else if (auto match = dyn_cast<exec::MatchOp>(instruction)) {
        SmallVector<std::string> alternatives;
        for (auto alternative : match.getAlternatives())
          alternatives.push_back(cast<StringAttr>(alternative).str());
        outputs =
            native.match(inputs.front(), ArrayRef(inputs).drop_front(),
                         choice.outputs, alternatives, site.getValue(), body);
      } else if (isa<exec::RangeOp>(instruction)) {
        auto state = ArrayRef(inputs).slice(2, choice.outputs.size());
        auto captures = ArrayRef(inputs).drop_front(2 + choice.outputs.size());
        outputs =
            native.loop(inputs[0], inputs[1], state, captures, choice.outputs,
                        node.step->conditional, site.getValue(), body);
      } else if (isa<runtime::ReleaseBindingsOp>(instruction)) {
        native.release(inputs);
      } else if (isa<exec::ReturnOp, exec::CompleteOp>(instruction)) {
        // Source helper packaging has already been substituted. At the native
        // publication boundary this root now performs its charged completion.
        native.complete(inputs);
      } else if (auto reject = dyn_cast<exec::RejectOp>(instruction)) {
        native.reject(reject.getReason(), reject.getSite());
      } else {
        return error("binding-materialization-context");
      }
      if (outputs.size() != node.outputs.size())
        return error("binding-materialization-coordinate");
      for (auto [port, pair] : enumerate(zip(node.outputs, outputs))) {
        mapping.map(std::get<0>(pair), std::get<1>(pair));
        stored[{target::StorageValue::OperationResult, index, unsigned(port)}] =
            std::get<1>(pair);
      }
      if (auto e = release({target::StoragePoint::AfterOperation, index}))
        return e;
    }
  }
  if (!releases.empty())
    return error("storage-schedule-coordinate");
  root.setProfile(zkc::protocol_ir::Profile::Physical);
  return Error::success();
}

// Check the complete compact carrier after applying the actual bindings and
// conversions. Body-string bounds alone miss escaping and repeated calls.
static Expected<SmallVector<target::OperationIndex>>
checkProgramCapacity(ModuleOp candidate, const target::PhysicalPlan &plan) {
  // The planner owns and charges this private clone before invoking us.
  if (auto e = applyPhysical(candidate, plan))
    return e;
  auto model = readExecutionModel(candidate);
  Error refusal = model ? program::checkStructure(*model) : model.takeError();
  if (!refusal)
    return SmallVector<target::OperationIndex>{};
  bool capacity = false;
  refusal =
      handleErrors(std::move(refusal), [&](const Refusal &error) -> Error {
        if (error.code == "source-limit") {
          capacity = true;
          return Error::success();
        }
        return zkc::error(error.code, error.detail);
      });
  if (refusal)
    return std::move(refusal);
  if (!capacity)
    return error("source-limit");
  SmallVector<target::OperationIndex> expressions;
  for (auto [index, operation] : enumerate(plan.operations)) {
    if (!operation.conversions.empty()) {
      expressions.push_back(index);
      continue;
    }
    if (!operation.binding)
      continue;
    const auto &contract =
        plan.bindings[*operation.binding].binding.application.contract;
    if (contract == "numerical.map" || contract == "numerical.sum" ||
        contract == "numerical.product")
      expressions.push_back(index);
  }
  if (expressions.empty())
    return error("source-limit");
  return expressions;
}

Error materializePhysical(ModuleOp module,
                          const target::CheckedPhysicalPlan &checked) {
  auto candidate = checked.cloneSelectedSubject(module);
  if (!candidate)
    return candidate.takeError();
  if (auto e = applyPhysical(**candidate, checked.choices()))
    return e;
  if (auto e = verifyPhysicalMaterialization(module, **candidate, checked))
    return e;
  module.getBodyRegion().takeBody((*candidate)->getBodyRegion());
  return Error::success();
}
LogicalResult lowerBoundPhysical(
    ModuleOp original, ArrayRef<std::pair<std::string, std::string>> selections,
    bool linearContractions, LinearContractionStats *stats, bool releaseStorage,
    ArrayRef<target::FunctionPortSelection> functionPorts,
    MathematicalSelectionPolicy numericalPolicy,
    const target::CpuTarget &cpuTarget) {
  // One plan binds the original input with numerical requests through both
  // checked edges. Materialization owns the candidate and publishes only after
  // all admission, physical correspondence and projection checks succeed.
  Location failureLocation = original->getLoc();
  target::PhysicalPlanOptions options;
  options.cpuTarget = cpuTarget;
  options.linearContractions = linearContractions;
  options.numericalPolicy = numericalPolicy;
  options.releaseStorage = releaseStorage;
  options.programCapacity = checkProgramCapacity;
  options.functionPorts.assign(functionPorts.begin(), functionPorts.end());
  auto proposal =
      target::proposePhysical(original, target::installedCandidates(),
                              selections, options, &failureLocation);
  if (!proposal) {
    diagnostics::emit(emitError(failureLocation), proposal.takeError());
    return failure();
  }
  auto checked = target::validatePhysical(
      original, *proposal, target::installedCandidates(), &failureLocation);
  if (!checked) {
    diagnostics::emit(emitError(failureLocation), checked.takeError());
    return failure();
  }
  if (auto e = materializePhysical(original, *checked)) {
    diagnostics::emit(original.emitError(), std::move(e));
    return failure();
  }
  if (stats)
    *stats = checked->stats();
  return success();
}
} // namespace zkc::protocol
