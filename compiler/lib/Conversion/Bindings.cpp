#include "Bindings.h"
#include "../Target/PhysicalPlan.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Transforms/Mathematical.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
static Error applyPhysical(ModuleOp module, const target::PhysicalPlan &plan) {
  auto work = target::physicalPlanOperations(module);
  auto root =
      cast<zkc::protocol_ir::ProtocolModuleOp>(&module.getBody()->front());
  OpBuilder builder(module.getContext());
  // All choices, including names and ports, have been checked on this exact
  // logical input. Application contains no selection/default/adapter policy.
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
  // Apply interface ports without changing operation order. Kernel definitions
  // get their own selected result ports when replaced below.
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
  for (auto [op, decision] : zip(work, plan.operations)) {
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
      auto converted = zkc::plan::ExecuteKernelOp::create(
          builder, op->getLoc(), TypeRange{conversion.to},
          ValueRange{operands[conversion.operand]}, conversion.site,
          binding.application.implementation, builder.getArrayAttr({}),
          FlatSymbolRefAttr::get(module.getContext(), binding.name));
      operands[conversion.operand] = converted.getResult(0);
    }
    if (!decision.binding) {
      op->setOperands(operands);
      continue;
    }
    const auto &binding = plan.bindings[*decision.binding].binding;
    auto physical = zkc::plan::ExecuteKernelOp::create(
        builder, op->getLoc(), decision.outputs, operands,
        op->getAttrOfType<StringAttr>("site"),
        builder.getStringAttr(binding.application.implementation),
        op->getAttrOfType<ArrayAttr>("parameters"),
        FlatSymbolRefAttr::get(module.getContext(), binding.name));
    op->replaceAllUsesWith(physical->getResults());
    op->erase();
  }
  root.setProfile(zkc::protocol_ir::Profile::Physical);
  return Error::success();
}

Error materializePhysical(ModuleOp module,
                          const target::CheckedPhysicalPlan &checked) {
  if (auto e = checked.checkInput(module))
    return e;
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(module->clone()));
  if (auto e = applyPhysical(*candidate, checked.choices()))
    return e;
  if (auto e = verifyPhysicalMaterialization(module, *candidate, checked))
    return e;
  module.getBodyRegion().takeBody(candidate->getBodyRegion());
  return Error::success();
}
LogicalResult
lowerBoundPhysical(ModuleOp original,
                   ArrayRef<std::pair<std::string, std::string>> selections,
                   bool linearContractions, LinearContractionStats *stats) {
  // Preserve the original transaction: publish only a verified owned clone.
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(original->clone()));
  Location failureLocation = candidate->getLoc();
  auto proposal =
      target::proposePhysical(*candidate, target::installedCandidates(),
                              selections, linearContractions, &failureLocation);
  if (!proposal) {
    diagnostics::emit(emitError(failureLocation), proposal.takeError());
    return failure();
  }
  auto checked = target::validatePhysical(
      *candidate, *proposal, target::installedCandidates(), &failureLocation);
  if (!checked) {
    diagnostics::emit(emitError(failureLocation), checked.takeError());
    return failure();
  }
  if (auto e = materializePhysical(*candidate, *checked)) {
    diagnostics::emit(candidate->emitError(), std::move(e));
    return failure();
  }
  if (failed(verify(*candidate)))
    return failure();
  if (failed(mathematical::verifyProjectionPreserved(original, *candidate)))
    return failure();
  original.getBodyRegion().takeBody(candidate->getBodyRegion());
  if (stats)
    *stats = checked->stats();
  return success();
}
} // namespace zkc::protocol
