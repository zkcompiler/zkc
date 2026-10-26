#include "NumericalLowering.h"
#include "AlgorithmSupport.h"
#include "ComputationSelection.h"
#include "RealizationEmission.h"
#include "RealizationSubject.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Transforms/Algorithms.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
Expected<std::string> mapPayloadSite(algebra::MapRealizeOp map,
                                     StringRef callSite, unsigned index,
                                     uint64_t &bytes) {
  protocol::Assignments path{{callSite.str(), map.getHelper().str()}};
  return protocol::algorithmSite(path, "map_" + std::to_string(index), bytes);
}

LogicalResult prepareRetainedMaps(ModuleOp source, PreparedMaps &prepared,
                                  NumericalSelection &selection,
                                  MathematicalSelectionPolicy policy) {
  auto root = cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  llvm::DenseSet<Operation *> helpers;
  uint64_t expanded = 0;
  if (failed(algebra::collectMapHelpers(root, helpers, expanded)))
    return failure();
  if (!selection.chargeCatalog(expanded))
    return diagnostics::emit(source.emitError(), "mathematical-analysis-limit");
  for (auto *helper : helpers)
    prepared.helpers.insert(
        SymbolTable::getSymbolName(helper).getValue().str());
  for (auto map : root.getBody().front().getOps<algebra::MapRealizeOp>()) {
    auto formula = prepareMapFormula(map, selection.work);
    if (failed(formula))
      return failure();
    auto product = selectMapProduct((*formula)->front(), map.getRowwise());
    bool dot = product && selectMapSum(*product, mathematicalRecipes());
    prepared.formulas.emplace(map.getSymName().str(),
                              PreparedMaps::Formula{std::move(*formula), dot});
  }
  SymbolTable symbols(root);
  selection.enterInvocation({});
  auto discovered = root.walk([&](local::ApplyOp call) {
    auto map = symbols.lookup<algebra::MapRealizeOp>(call.getCallee());
    auto found = prepared.formulas.find(call.getCallee().str());
    if (!map || found == prepared.formulas.end())
      return WalkResult::interrupt();
    bool fusion =
        bool(eligibleMapSum(call, symbols, mapSelectionPolicy(map, policy)));
    auto occurrence = selection.discoverMap(realizationSubject(call),
                                            fusion && found->second.dot, fusion,
                                            policy.numericalExpressions);
    if (!occurrence) {
      diagnostics::emit(call.emitOpError(), occurrence.takeError());
      return WalkResult::interrupt();
    }
    return WalkResult::advance();
  });
  if (discovered.wasInterrupted())
    return failure();
  return success();
}

LogicalResult materializeRetainedMaps(ModuleOp candidate,
                                      const PreparedMaps &prepared,
                                      NumericalSelection &selection,
                                      MathematicalSelectionPolicy policy,
                                      VerificationDecision &outcome,
                                      bool optionalConstruction) {
  auto root = cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  SymbolTable symbols(root);
  RealizationEmitter emitter(root, "_map_binding_");
  SmallVector<local::ApplyOp> calls;
  root.walk([&](local::ApplyOp call) { calls.push_back(call); });
  // Numerical calls use their actual invocation identity. Retained maps have
  // complete Local coordinates and a separate fixed qualification in this same
  // session.
  selection.enterInvocation({});
  for (auto call : calls) {
    unsigned depth = 0;
    for (auto *parent = call->getParentOp();
         parent && !isa<local::FuncOp>(parent); parent = parent->getParentOp())
      ++depth;
    if (depth >= 64)
      return diagnostics::emit(call.emitOpError(), "algorithm-expansion-limit");
    auto map = symbols.lookup<algebra::MapRealizeOp>(call.getCallee());
    auto found = prepared.formulas.find(call.getCallee().str());
    if (!map || found == prepared.formulas.end())
      return diagnostics::emit(call.emitOpError(), "native-local-policy",
                               "expected an admitted retained map call");
    auto subject = realizationSubject(call);
    bool fusion =
        bool(eligibleMapSum(call, symbols, mapSelectionPolicy(map, policy)));
    auto occurrence =
        selection.discoverMap(subject, fusion && found->second.dot, fusion,
                              policy.numericalExpressions);
    if (!occurrence)
      return diagnostics::emit(call.emitOpError(), occurrence.takeError());
    auto choice = selection.alternative(*occurrence);
    MapPayloadForm form = choice == NumericalAlternative::Specialized
                              ? MapPayloadForm::Dot
                          : choice == NumericalAlternative::Expression
                              ? MapPayloadForm::NumericalSum
                          : choice == NumericalAlternative::MapExpression
                              ? MapPayloadForm::NumericalMap
                              : MapPayloadForm::VectorMap;
    bool optional = form != MapPayloadForm::VectorMap;
    auto &constructionWork = optional ? selection.work.optionalMapConstruction
                                      : selection.work.requiredMapConstruction;
    auto &formula = found->second.scalar.get().front();
    uint64_t formulaCost =
        formula.getNumArguments() + formula.getOperations().size();
    if (formulaCost > constructionWork) {
      auto available = constructionWork;
      constructionWork = 0;
      outcome = {optional ? VerificationObservation::OptionalCapacity
                          : VerificationObservation::RequiredCapacity,
                 "map formula construction capacity",
                 CapacityCause{WorkOwner::Lanes, formulaCost, available},
                 subject};
      return failure();
    }
    constructionWork -= formulaCost;
    bool capacity = false;
    std::optional<CapacityCause> capacityCause;
    unsigned nextSite = 0;
    OpBuilder builder(call);
    auto result = emitMapPayload(
        map, found->second.scalar.get().front(), call.getInputs(), form,
        [&](const protocol::BindingApplication &application, ValueRange inputs,
            TypeRange outputs,
            ArrayRef<std::string> parameters) -> Operation * {
          if (capacity || any_of(inputs, [](Value v) { return !v; }))
            return nullptr;
          uint64_t cost = 2 + inputs.size() + outputs.size();
          if (cost > selection.remainingCopy) {
            capacity = true;
            capacityCause = CapacityCause{WorkOwner::AlgorithmExpansion, cost,
                                          selection.remainingCopy};
            return nullptr;
          }
          selection.remainingCopy -= cost;
          auto site = mapPayloadSite(map, call.getSite(), nextSite++,
                                     selection.remainingSiteBytes);
          if (!site) {
            consumeError(site.takeError());
            capacity = true;
            capacityCause = CapacityCause{WorkOwner::AlgorithmOriginBytes};
            return nullptr;
          }
          auto *op = emitter.emit(builder, call.getLoc(), *site, application,
                                  inputs, outputs, parameters);
          selection.record(op, *occurrence);
          auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
          selection.record(SymbolTable::lookupSymbolIn(root, reference),
                           *occurrence);
          return op;
        });
    if (capacity ||
        (result && result->status == LaneRealizationStatus::Capacity)) {
      outcome = {optional || (capacity && optionalConstruction)
                     ? VerificationObservation::OptionalCapacity
                     : VerificationObservation::RequiredCapacity,
                 "map construction capacity", capacityCause, subject,
                 RealizationSubject{}};
      if (!result)
        consumeError(result.takeError());
      return failure();
    }
    if (!result)
      return diagnostics::emit(call.emitOpError(), result.takeError());
    if (result->status != LaneRealizationStatus::Realized)
      return diagnostics::emit(call.emitOpError(), "algebra-map-lowering",
                               result->reason);
    if (form == MapPayloadForm::Dot || form == MapPayloadForm::NumericalSum) {
      auto *sum = call->getNextNode();
      sum->getResult(0).replaceAllUsesWith(result->value);
      sum->erase();
    } else
      call.getResult(0).replaceAllUsesWith(result->value);
    call.erase();
  }
  // The original complete closure was admitted even if no call reaches it.
  // Logical Exec admits these scalar siblings only as the retained map closure.
  for (auto &op : make_early_inc_range(root.getBody().front()))
    if (isa<algebra::MapRealizeOp>(op) ||
        (isa<func::FuncOp>(op) &&
         prepared.helpers.count(
             SymbolTable::getSymbolName(&op).getValue().str())))
      op.erase();
  // Identity maps can make previously distinct control captures alias. Rewrite
  // their region ports only after all retained calls have been materialized.
  return protocol::detail::canonicalizeCaptures(root);
}
} // namespace zkc::mathematical
