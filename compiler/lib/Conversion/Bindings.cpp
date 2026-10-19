#include "Bindings.h"
#include "../Target/PhysicalPlan.h"
#include "Storage.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Refusal.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
static Error applyPhysical(ModuleOp module, const target::PhysicalPlan &plan) {
  auto work = target::physicalPlanOperations(module);
  SmallVector<SmallVector<Value>, 0> conversions;
  if (!plan.releases.empty())
    conversions.resize(work.size());
  auto root =
      cast<zkc::protocol_ir::ProtocolModuleOp>(&module.getBody()->front());
  OpBuilder builder(module.getContext());
  // All choices, including names and ports, have been checked on this exact
  // selected Local payload. Application contains no numerical producer,
  // selection/default/adapter policy or catalog query.
  for (const auto &decision : plan.bindings) {
    if (decision.purpose == target::BindingPurpose::Original) {
      cast<zkc::local::OperationBindingOp>(work[*decision.declaration])
          .setImplementation(decision.binding.application.implementation);
      continue;
    }
    builder.setInsertionPointToStart(&root.getBody().front());
    const auto &binding = decision.binding;
    SmallVector<Attribute> arguments;
    for (const auto &argument : binding.application.arguments)
      arguments.push_back(builder.getStringAttr(argument));
    zkc::local::OperationBindingOp::create(
        builder, work[decision.location]->getLoc(), binding.name,
        binding.application.contract, builder.getArrayAttr(arguments),
        binding.application.implementation);
  }
  // Apply interface ports without changing operation order. Bound operations
  // get their selected result ports when replaced below.
  for (auto [op, decision] : zip(work, plan.operations)) {
    size_t blockIndex = 0;
    for (auto &region : op->getRegions())
      for (auto &block : region) {
        for (auto [argument, type] :
             zip(block.getArguments(), decision.blockArguments[blockIndex]))
          argument.setType(type);
        ++blockIndex;
      }
    if (decision.functionType)
      op->setAttr("function_type", TypeAttr::get(decision.functionType));
    if (!decision.binding)
      for (auto [result, type] : zip(op->getResults(), decision.outputs))
        result.setType(type);
  }
  for (auto [index, decision] : enumerate(plan.operations)) {
    auto *op = work[index];
    if (auto literal = dyn_cast<zkc::local::BoolConstantOp>(op)) {
      if (decision.outputs.size() != 1 || decision.binding ||
          !decision.conversions.empty())
        return createStringError("native-boolean-physical-plan");
      builder.setInsertionPoint(op);
      auto physical = zkc::plan::BoolConstantOp::create(
          builder, op->getLoc(), decision.outputs.front(),
          literal.getValueAttr(), literal.getSiteAttr());
      op->replaceAllUsesWith(physical->getResults());
      op->erase();
      work[index] = physical;
      continue;
    }
    if (!decision.binding && decision.conversions.empty())
      continue;
    builder.setInsertionPoint(op);
    SmallVector<Value> operands(op->getOperands());
    for (const auto &conversion : decision.conversions) {
      const auto &binding = plan.bindings[conversion.binding].binding;
      // One instruction per crossing, immediately before this consumer in
      // operand order. The runtime charges and may stop this instruction.
      auto converted = zkc::plan::ApplyOp::create(
          builder, op->getLoc(), TypeRange{conversion.to},
          ValueRange{operands[conversion.operand]}, conversion.site,
          binding.application.implementation, builder.getArrayAttr({}),
          FlatSymbolRefAttr::get(module.getContext(), binding.name));
      operands[conversion.operand] = converted.getResult(0);
      if (!plan.releases.empty())
        conversions[index].push_back(converted.getResult(0));
    }
    if (!decision.binding) {
      op->setOperands(operands);
      continue;
    }
    const auto &binding = plan.bindings[*decision.binding].binding;
    auto physical = zkc::plan::ApplyOp::create(
        builder, op->getLoc(), decision.outputs, operands,
        op->getAttrOfType<StringAttr>("site"),
        builder.getStringAttr(binding.application.implementation),
        op->getAttrOfType<ArrayAttr>("parameters"),
        FlatSymbolRefAttr::get(module.getContext(), binding.name));
    op->replaceAllUsesWith(physical->getResults());
    op->erase();
    work[index] = physical;
  }
  if (auto e = applyStorage(module, plan.releases, work, conversions))
    return e;
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
LogicalResult
lowerBoundPhysical(ModuleOp original,
                   ArrayRef<std::pair<std::string, std::string>> selections,
                   bool linearContractions, LinearContractionStats *stats,
                   bool releaseStorage) {
  // One plan binds the original Kernel-bearing input through both checked
  // edges. Materialization owns the candidate and publishes only after all
  // admission, physical correspondence and projection checks succeed.
  Location failureLocation = original->getLoc();
  auto proposal = target::proposePhysical(
      original, target::installedCandidates(), selections,
      {linearContractions, releaseStorage, checkProgramCapacity},
      &failureLocation);
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
