#include "MathematicalSupport.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
LogicalResult verifyMathRealizationsPreserved(ModuleOp original,
                                              ModuleOp candidate) {
  if (failed(verify(original)) || failed(verify(candidate)))
    return failure();
  auto refuse = [&](StringRef reason) {
    return diagnostics::emit(candidate.emitError(),
                             "local-realization-correspondence", reason);
  };
  if (original->getAttrDictionary() != candidate->getAttrDictionary() ||
      !hasSingleElement(*original.getBody()) ||
      !hasSingleElement(*candidate.getBody()))
    return refuse("module shape");
  auto before =
      dyn_cast<protocol_ir::ProtocolModuleOp>(original.getBody()->front());
  auto after =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!before || !after ||
      before.getProfile() != protocol_ir::Profile::Protocol ||
      before->getAttrDictionary() != after->getAttrDictionary())
    return refuse("profile");
  SymbolTable symbols(after);
  llvm::DenseSet<Operation *> retained, bindings;
  uint64_t remaining = 1000000;
  NativeTypePolicies types(after);
  for (auto &op : before.getBody().front()) {
    auto name = SymbolTable::getSymbolName(&op);
    auto *replacement = name ? symbols.lookup(name.getValue()) : nullptr;
    if (!replacement)
      return refuse("missing declaration");
    retained.insert(replacement);
    auto realization = dyn_cast<local::RealizeOp>(op);
    if (!realization) {
      if (!OperationEquivalence::isEquivalentTo(
              &op, replacement, OperationEquivalence::IgnoreLocations))
        return refuse("changed retained declaration");
      continue;
    }
    auto function = dyn_cast<local::FuncOp>(replacement);
    if (!function ||
        function.getFunctionType() != realization.getFunctionType() ||
        function->getAttrs().size() != 3)
      return refuse("realization interface");
    auto origin = function->getAttrOfType<ArrayAttr>("logical_origin");
    if (!origin || origin.size() != 2 ||
        origin[0] !=
            StringAttr::get(original.getContext(), realization.getHelper()) ||
        origin[1] != ArrayAttr::get(original.getContext(), {}))
      return refuse("realization origin");
    auto result = function.walk([&](Operation *nested) -> WalkResult {
      if (!remaining--)
        return WalkResult::interrupt();
      auto data = [&](Type type) {
        auto policy = types.get(type);
        return policy && policy->total && !policy->affine &&
               !isa<poly::PolynomialType>(type);
      };
      if (!all_of(nested->getOperandTypes(), data) ||
          !all_of(nested->getResultTypes(), data))
        return WalkResult::interrupt();
      for (auto &region : nested->getRegions())
        for (auto &block : region)
          if (!all_of(block.getArgumentTypes(), data))
            return WalkResult::interrupt();
      if (isa<local::FuncOp, local::ReturnOp, local::LocalIfOp,
              local::LocalMatchOp, local::VariantInjectOp, local::LocalYieldOp,
              local::BoolConstantOp>(nested))
        return WalkResult::advance();
      auto ref = nested->getAttrOfType<FlatSymbolRefAttr>("binding");
      auto binding =
          ref ? symbols.lookup<local::OperationBindingOp>(ref.getValue())
              : local::OperationBindingOp();
      if (!binding || !binding.getImplementation().empty() ||
          !isCalculationContract(binding.getContract()))
        return WalkResult::interrupt();
      bindings.insert(binding);
      return WalkResult::advance();
    });
    if (result.wasInterrupted())
      return refuse("unexpected realization action or work limit");
  }
  for (auto &op : after.getBody().front())
    if (!retained.contains(&op) && !bindings.contains(&op))
      return refuse("unexpected declaration");
  return success();
}

LogicalResult expandMathRealizations(ModuleOp module) {
  if (failed(verify(module)) || !hasSingleElement(*module.getBody()))
    return failure();
  auto original =
      dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  if (!original || original.getProfile() != protocol_ir::Profile::Protocol)
    return diagnostics::emit(module.emitError(), "local-realization-context");
  if (original.getBody().front().getOps<local::RealizeOp>().empty())
    return success();
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(module->clone()));
  auto unit =
      cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
  SmallVector<local::FuncOp> functions;
  unsigned remainingHelpers = realizedHelperOperationLimit;
  uint64_t helperIndices = 1000000, polynomialWork = 100000;
  for (auto realization : make_early_inc_range(
           unit.getBody().front().getOps<local::RealizeOp>())) {
    OpBuilder builder(realization);
    auto location = realization.getLoc();
    auto name = realization.getSymNameAttr();
    auto helper = realization.getHelperAttr();
    auto signature = realization.getFunctionType();
    builder.setInsertionPointAfter(realization);
    realization.erase();
    auto function = local::FuncOp::create(builder, location, name, signature);
    function->setAttr(
        "logical_origin",
        builder.getArrayAttr({builder.getStringAttr(helper.getValue()),
                              builder.getArrayAttr({})}));
    auto *block = function.addEntryBlock();
    builder.setInsertionPointToEnd(block);
    auto call =
        func::CallOp::create(builder, location, helper.getValue(),
                             function.getResultTypes(), block->getArguments());
    local::ReturnOp::create(builder, location, call.getResults());
    functions.push_back(function);
  }
  // Build the symbol cache only after every declaration has been replaced.
  SymbolTableCollection symbols;
  for (auto function : functions) {
    auto *block = &function.getBody().front();
    OpBuilder builder(function);
    if (failed(inlineHelpers(function, remainingHelpers, helperIndices,
                             symbols)) ||
        failed(poly::eliminatePolynomials(*block, polynomialWork)))
      return failure();
    // A static dimension observes a type, not its producer's runtime value.
    // Resolve it before liveness so its producer cannot become dead execution.
    for (auto dim : llvm::make_early_inc_range(block->getOps<data::DimOp>())) {
      auto type = dim.getInput().getType();
      auto axis = dim.getAxisAttr().getInt();
      if (type.isDynamicDim(axis))
        continue;
      builder.setInsertionPoint(dim);
      auto index = data::IndexOp::create(
          builder, dim.getLoc(), dim.getOutput().getType(),
          builder.getStringAttr(std::to_string(type.getDimSize(axis))));
      dim.getOutput().replaceAllUsesWith(index.getOutput());
      dim.erase();
    }
    // Elimination has checked every observation, including unused ones. Only
    // now may dead total expressions be removed before ordering runtime work.
    for (auto &op : llvm::make_early_inc_range(llvm::reverse(*block)))
      if (isTotal(&op) && op.use_empty())
        op.erase();
    unsigned occurrence = 0;
    for (auto &op : block->without_terminator())
      op.setAttr("site", builder.getStringAttr("value_" +
                                               std::to_string(occurrence++)));
  }
  if (failed(lowerCalculations(unit, functions)) ||
      failed(verifyMathRealizationsPreserved(module, *candidate)))
    return diagnostics::emit(
        module.emitError(), "local-realization-lowering",
        "realized body failed recipe or executable admission");
  module.getBodyRegion().takeBody(candidate->getBodyRegion());
  return success();
}
} // namespace zkc::mathematical
