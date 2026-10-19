#include "CheckedCandidate.h"
#include "HelperNormalization.h"
#include "Kernel/Support.h"
#include "MathematicalSupport.h"
#include "RealizationTrace.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
LogicalResult checkRealizations(ModuleOp original, ModuleOp candidate) {
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
  SymbolTable source(before), target(after);
  SymbolTableCollection symbols;
  llvm::DenseSet<Operation *> retained, units;
  for (auto &declaration : before.getBody().front()) {
    auto name = SymbolTable::getSymbolName(&declaration);
    auto *replacement = name ? target.lookup(name.getValue()) : nullptr;
    if (!replacement)
      return refuse("missing declaration");
    retained.insert(replacement);
    auto realization = dyn_cast<local::RealizeOp>(declaration);
    if (!realization) {
      if (!OperationEquivalence::isEquivalentTo(
              &declaration, replacement, OperationEquivalence::IgnoreLocations))
        return refuse("changed retained declaration");
      continue;
    }
    auto wrapper = dyn_cast<local::FuncOp>(replacement);
    auto helper = source.lookup<func::FuncOp>(realization.getHelper());
    if (!wrapper || !helper ||
        wrapper.getFunctionType() != realization.getFunctionType() ||
        wrapper->getAttrs().size() != 3 || !wrapper.getBody().hasOneBlock() ||
        wrapper.getBody().front().getOperations().size() != 2)
      return refuse("realization wrapper interface");
    Builder builder(original.getContext());
    auto origin =
        builder.getArrayAttr({builder.getStringAttr(realization.getHelper()),
                              builder.getArrayAttr({})});
    if (wrapper->getAttr("logical_origin") != origin)
      return refuse("realization origin");
    auto call = dyn_cast<kernel::CallOp>(wrapper.getBody().front().front());
    auto returned = dyn_cast<local::ReturnOp>(wrapper.getBody().front().back());
    auto entry = call ? kernel::resolve(call, symbols) : func::FuncOp();
    auto unit = entry ? cast<kernel::ModuleOp>(entry->getParentOp())
                      : kernel::ModuleOp();
    if (!entry || !returned || call.getSite() != "kernel" ||
        call.getInputs() != wrapper.getArguments() ||
        returned.getInputs() != call.getResults() ||
        !units.insert(unit).second ||
        failed(kernel::verifyKernelClosure(before, helper, unit)))
      return refuse("original helper/domain closure and actual unit differ");
  }
  for (auto &declaration : after.getBody().front())
    if (!retained.contains(&declaration) && !units.contains(&declaration))
      return refuse("unexpected declaration");
  return success();
}

} // namespace
LogicalResult verifyMathRealizationsPreserved(ModuleOp original,
                                              ModuleOp candidate) {
  return checkRealizations(original, candidate);
}

LogicalResult expandMathRealizations(ModuleOp module,
                                     MathematicalSelectionPolicy policy,
                                     RealizationWork *work,
                                     RealizationTrace *trace) {
  RealizationWork standalone;
  auto &stageWork = work ? *work : standalone;
  RealizationScope scope(trace, "math-realizations", module, policy,
                         &stageWork);
  if (failed(verify(module)) || !hasSingleElement(*module.getBody()))
    return failure();
  auto original =
      dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  if (!original || original.getProfile() != protocol_ir::Profile::Protocol)
    return diagnostics::emit(module.emitError(), "local-realization-context");
  if (original.getBody().front().getOps<local::RealizeOp>().empty()) {
    scope.complete(CompletionKind::Unchanged);
    return success();
  }
  scope.propose(policy);
  mathematical::CheckedCandidate candidate(module);
  auto unit =
      cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
  SmallVector<local::FuncOp> functions;
  SymbolTable sourceSymbols(original);
  auto &cloneOperations = stageWork.helperOperations;
  auto &cloneSlots = stageWork.helperSlots;
  for (auto realization : make_early_inc_range(
           unit.getBody().front().getOps<local::RealizeOp>())) {
    auto helper = sourceSymbols.lookup<func::FuncOp>(realization.getHelper());
    if (!helper)
      return failure();
    auto normalized = helper;
    // Formation copies original mathematics; each retained copy costs work.
    OptimizationOutcome outcome;
    if (!normalized ||
        failed(chargeHelperOperations(normalized, cloneOperations, cloneSlots,
                                      nullptr, &outcome))) {
      scope.failure(
          RequiredFailure{"realization helper expansion", outcome.capacity});
      return failure();
    }
    OpBuilder builder(realization);
    auto location = realization.getLoc();
    auto name = realization.getSymNameAttr();
    auto signature = realization.getFunctionType();
    builder.setInsertionPointAfter(realization);
    realization.erase();
    auto function = local::FuncOp::create(builder, location, name, signature);
    function->setAttr(
        "logical_origin",
        builder.getArrayAttr({builder.getStringAttr(helper.getSymName()),
                              builder.getArrayAttr({})}));
    auto *block = function.addEntryBlock();
    builder.setInsertionPointToEnd(block);
    IRMapping mapping;
    mapping.map(normalized.getArguments(), block->getArguments());
    for (auto &op : normalized.front().without_terminator()) {
      builder.clone(op, mapping);
    }
    SmallVector<Value> results;
    for (auto value : normalized.front().back().getOperands())
      results.push_back(mapping.lookup(value));
    local::ReturnOp::create(builder, location, results);
    functions.push_back(function);
  }
  for (auto function : functions) {
    if (failed(kernel::formCalculation(function, original, policy)))
      return failure();
    auto call = cast<kernel::CallOp>(function.getBody().front().front());
    SymbolTableCollection symbols;
    auto entry = kernel::resolve(call, symbols);
    auto origin = function->getAttrOfType<ArrayAttr>("logical_origin");
    auto helper = sourceSymbols.lookup<func::FuncOp>(
        cast<StringAttr>(origin[0]).getValue());
    for (auto attribute : helper->getAttrs())
      if (attribute.getName() != "sym_name" &&
          attribute.getName() != "sym_visibility")
        entry->setAttr(attribute.getName(), attribute.getValue());
  }
  if (failed(candidate.publish(checkRealizations)))
    return diagnostics::emit(module.emitError(), "local-realization-lowering",
                             "realized numerical closure failed correspondence "
                             "or logical admission");
  scope.publish();
  return success();
}
} // namespace zkc::mathematical
