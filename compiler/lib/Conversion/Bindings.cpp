#include "Bindings.h"
#include "../Target/PhysicalPlan.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
namespace {
// The last algebra consumer sees inline regions. Outlining is a realization
// step: the new calls need the checked pure-call folding relation to recover
// the inline open meaning. Actual helper bodies remain in the candidate.
Error outlinePureRegions(ModuleOp module) {
  auto root = cast<ProtocolModuleOp>(&module.getBody()->front());
  SmallVector<PureRegionOp> regions;
  module.walk([&](PureRegionOp region) { regions.push_back(region); });
  SymbolTable symbols(root);
  OpBuilder builder(module.getContext());
  unsigned next = 0;
  for (auto region : regions) {
    auto participant = region->getParentOfType<ParticipantOp>();
    if (!participant || region.getRoleAttr())
      return error("interactive-pure-context");
    std::string origin = "pure";
    for (StringRef part :
         {participant.getInstance(), participant.getRole(), region.getSite()})
      origin += "_" + std::to_string(part.size()) + "_" + part.str();
    if (origin.size() > 128)
      return error("interactive-pure-origin-limit");
    std::string name;
    do {
      name = "pure_region_" + std::to_string(next++);
    } while (symbols.lookup(name));
    builder.setInsertionPointToEnd(&root.getBody().front());
    auto function =
        func::FuncOp::create(builder, region.getLoc(), name,
                             builder.getFunctionType(region.getOperandTypes(),
                                                     region.getResultTypes()));
    symbols.insert(function);
    function->setAttr("logical_origin",
                      builder.getArrayAttr({builder.getStringAttr(origin),
                                            builder.getArrayAttr({})}));
    auto *block = function.addEntryBlock();
    IRMapping values;
    values.map(region.getBody().front().getArguments(), block->getArguments());
    builder.setInsertionPointToEnd(block);
    for (auto &op : region.getBody().front().without_terminator())
      builder.clone(op, values);
    SmallVector<Value> results;
    for (auto value : region.getBody().front().back().getOperands())
      results.push_back(values.lookup(value));
    func::ReturnOp::create(builder, region.getLoc(), results);
    builder.setInsertionPoint(region);
    auto call = LocalCallOp::create(
        builder, region.getLoc(), region.getResultTypes(), region.getInputs(),
        function.getSymName(), region.getSite(), StringAttr());
    region->replaceAllUsesWith(call->getResults());
    region->erase();
  }
  // Re-admit the actual result before physical choices. No caller-supplied
  // function name or marker can bypass ordinary local-body admission.
  auto candidate = exportSource(module);
  if (!candidate)
    return candidate.takeError();
  return admit(*candidate, true);
}
} // namespace
Error materializePhysical(ModuleOp module,
                          const target::CheckedPhysicalPlan &checked) {
  if (auto e = checked.checkInput(module))
    return e;
  const auto &plan = checked.choices();
  auto work = target::physicalPlanOperations(module);
  auto root = cast<ProtocolModuleOp>(&module.getBody()->front());
  OpBuilder builder(module.getContext());
  // All choices, including names and ports, have been checked on this exact
  // logical input. Application contains no selection/default/adapter policy.
  for (const auto &decision : plan.bindings) {
    if (decision.purpose == target::BindingPurpose::Original) {
      cast<OperationBindingOp>(work[*decision.declaration])
          .setImplementation(decision.binding.application.implementation);
      continue;
    }
    builder.setInsertionPointToStart(&root.getBody().front());
    const auto &binding = decision.binding;
    SmallVector<Attribute> arguments;
    for (const auto &argument : binding.application.arguments)
      arguments.push_back(builder.getStringAttr(argument));
    OperationBindingOp::create(builder, work[decision.location]->getLoc(),
                               binding.name, binding.application.contract,
                               builder.getArrayAttr(arguments),
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
    if (!decision.binding && decision.conversions.empty())
      continue;
    builder.setInsertionPoint(op);
    SmallVector<Value> operands(op->getOperands());
    for (const auto &conversion : decision.conversions) {
      const auto &binding = plan.bindings[conversion.binding].binding;
      // One instruction per crossing, immediately before this consumer in
      // operand order. The runtime charges and may stop this instruction.
      auto converted = ExecuteKernelOp::create(
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
    auto physical = ExecuteKernelOp::create(
        builder, op->getLoc(), decision.outputs, operands,
        op->getAttrOfType<StringAttr>("site"),
        builder.getStringAttr(binding.application.implementation),
        op->getAttrOfType<ArrayAttr>("parameters"),
        FlatSymbolRefAttr::get(module.getContext(), binding.name));
    op->replaceAllUsesWith(physical->getResults());
    op->erase();
  }
  root.setStage("physical");
  return Error::success();
}

LogicalResult
lowerBoundPhysical(ModuleOp original,
                   ArrayRef<std::pair<std::string, std::string>> selections,
                   bool linearContractions, LinearContractionStats *stats) {
  // Preserve the original transaction: publish only a verified owned clone.
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(original->clone()));
  if (auto e = realizeRoots(*candidate)) {
    diagnostics::emit(candidate->emitError(), std::move(e));
    return failure();
  }
  if (auto e = outlinePureRegions(*candidate)) {
    diagnostics::emit(candidate->emitError(), std::move(e));
    return failure();
  }
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
  original.getBodyRegion().takeBody(candidate->getBodyRegion());
  if (stats)
    *stats = checked->stats();
  return success();
}
} // namespace zkc::protocol
