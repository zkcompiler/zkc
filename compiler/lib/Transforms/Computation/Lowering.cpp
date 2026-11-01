#include "../CheckedCandidate.h"
#include "../MathematicalPassOptions.h"
#include "../RealizationSubject.h"
#include "../RealizationTrace.h"
#include "../ScopedSubstitution.h"
#include "Support.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/Linalg/IR/Linalg.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataDialect.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecDialect.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/raw_ostream.h"

using namespace mlir;
using namespace llvm;
namespace zkc::computation {
namespace {
void registerRealizationDialects(DialectRegistry &registry) {
  registry.insert<runtime::RuntimeDialect, algebra::AlgebraDialect,
                  data::DataDialect, exec::ExecDialect, func::FuncDialect,
                  scf::SCFDialect, arith::ArithDialect, cf::ControlFlowDialect,
                  tensor::TensorDialect, linalg::LinalgDialect>();
}
void loadRealizationDialects(MLIRContext &context) {
  DialectRegistry dependencies;
  registerRealizationDialects(dependencies);
  auto names = dependencies.getRegisteredDialectNames();
  // Pass-manager entry loads these before concurrent execution. Direct API
  // entry needs the same inventory, without loading unrelated registered
  // dialects.
  if (llvm::all_of(names, [&](StringRef name) {
        return context.getLoadedDialect(name) != nullptr;
      }))
    return;
  context.appendDialectRegistry(dependencies);
  for (StringRef name : names)
    context.getOrLoadDialect(name);
}
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "computation-realization",
                           detail);
}
LogicalResult materialize(protocol_ir::ProtocolModuleOp owner,
                          MathematicalSelectionPolicy fallback,
                          mathematical::RealizationTrace *trace,
                          mathematical::NumericalSelection &selection,
                          mathematical::VerificationDecision *outcome,
                          bool optionalConstruction) {
  SmallVector<exec::ComputeOp> calls;
  owner.walk([&](exec::ComputeOp call) { calls.push_back(call); });
  SymbolTable outer(owner);
  unsigned nextBinding = 0, nextFunction = 0;
  llvm::DenseMap<DictionaryAttr, std::string> importedBindings;
  llvm::DenseMap<Operation *, func::FuncOp> substitutions;
  auto &remaining = selection.remainingCopy;
  auto &remainingBytes = selection.remainingSiteBytes;
  auto &work = selection.work;
  auto capacity = [&](StringRef detail) {
    if (outcome)
      *outcome = {optionalConstruction
                      ? mathematical::VerificationObservation::OptionalCapacity
                      : mathematical::VerificationObservation::RequiredCapacity,
                  detail.str(), CapacityCause{WorkOwner::AlgorithmExpansion}};
    return failure();
  };
  for (auto call : calls) {
    auto invocation = mathematical::realizationSubject(call);
    selection.enterInvocation(invocation);
    SymbolTableCollection symbols;
    auto entry = call.resolveCallee(symbols);
    auto policy = effectiveSelectionPolicy(call, fallback);
    if (!entry || failed(policy) ||
        !mathematical::isComputationUnit(entry->getParentOp()))
      return refuse(call, "invalid normalized numerical closure or policy");
    auto scratch =
        realizeEntry(cast<mlir::ModuleOp>(entry->getParentOp()), call.getSite(),
                     *policy, work, remaining, remainingBytes, {}, trace,
                     &selection, outcome, optionalConstruction);
    if (!scratch) {
      if (outcome) {
        outcome->invocation = invocation;
        return failure();
      }
      return refuse(call, "numerical recipes refused the actual closure");
    }
    auto clearScratchOrigins = llvm::scope_exit([&] {
      scratch->walk([&](Operation *op) { selection.origins.erase(op); });
    });
    auto output =
        cast<protocol_ir::ProtocolModuleOp>(scratch->getBody()->front());
    auto function =
        SymbolTable(output).lookup<func::FuncOp>(entry.getSymName());
    if (!function)
      return refuse(call, "missing scoped numerical entry");
    llvm::StringSet<> reserved;
    for (auto &definition : output.getBody().front())
      reserved.insert(SymbolTable::getSymbolName(&definition).getValue());
    StringMap<std::string> renamed;
    llvm::DenseSet<Operation *> omitted;
    for (auto &definition : output.getBody().front()) {
      auto name = SymbolTable::getSymbolName(&definition);
      if (auto binding = dyn_cast<runtime::BindingOp>(definition)) {
        NamedAttrList signature(binding->getAttrs());
        signature.erase("sym_name");
        auto key = signature.getDictionary(owner.getContext());
        if (auto found = importedBindings.find(key);
            found != importedBindings.end()) {
          renamed[name.getValue()] = found->second;
          omitted.insert(&definition);
          continue;
        }
        std::string fresh;
        do {
          fresh = "_numerical_binding_" + std::to_string(nextBinding++);
        } while (outer.lookup(fresh) || !reserved.insert(fresh).second);
        importedBindings.try_emplace(key, fresh);
        renamed[name.getValue()] = fresh;
      } else if (isa<func::FuncOp>(definition)) {
        std::string fresh;
        do {
          fresh = "_numerical_body_" + std::to_string(nextFunction++);
        } while (outer.lookup(fresh) || !reserved.insert(fresh).second);
        renamed[name.getValue()] = fresh;
      } else
        return refuse(call, "unresolved numerical declaration");
    }
    // A reused outer binding may have the old name of a scratch function.
    // Rename uses in two phases so one substitution cannot rewrite references
    // introduced by another. Definitions retain their original names until
    // copy.
    for (const auto &entry : renamed)
      reserved.insert(entry.second);
    SmallVector<std::pair<StringAttr, StringAttr>> finalNames;
    unsigned nextTemporary = 0;
    for (auto &definition : output.getBody().front()) {
      auto old = SymbolTable::getSymbolName(&definition);
      std::string temporary;
      do {
        temporary = "_numerical_import_" + std::to_string(nextTemporary++);
      } while (!reserved.insert(temporary).second);
      auto intermediate = StringAttr::get(owner.getContext(), temporary);
      if (failed(SymbolTable::replaceAllSymbolUses(old, intermediate, output)))
        return refuse(call, "numerical symbol import refused");
      finalNames.emplace_back(
          intermediate,
          StringAttr::get(owner.getContext(), renamed.lookup(old.getValue())));
    }
    for (auto [temporary, final] : finalNames)
      if (failed(SymbolTable::replaceAllSymbolUses(temporary, final, output)))
        return refuse(call, "numerical symbol import refused");
    OpBuilder builder(owner.getContext());
    builder.setInsertionPointToEnd(&owner.getBody().front());
    for (auto &definition : output.getBody().front()) {
      auto old = SymbolTable::getSymbolName(&definition);
      if (omitted.contains(&definition)) {
        auto *binding = outer.lookup(renamed.lookup(old.getValue()));
        for (auto occurrence : selection.owners(call))
          selection.record(binding, occurrence);
        for (auto occurrence : selection.owners(&definition))
          selection.record(binding, occurrence);
        continue;
      }
      if (!chargeCopy(&definition, remaining))
        return capacity("numerical declaration import capacity");
      IRMapping mapping;
      auto *copy = builder.clone(definition, mapping);
      SymbolTable::setSymbolName(copy, renamed.lookup(old.getValue()));
      outer.insert(copy);
      definition.walk([&](Operation *nested) {
        for (auto occurrence : selection.owners(call))
          selection.record(nested == &definition ? copy
                                                 : mapping.lookup(nested),
                           occurrence);
        for (auto occurrence : selection.owners(nested))
          selection.record(nested == &definition ? copy
                                                 : mapping.lookup(nested),
                           occurrence);
      });
      if (&definition == function.getOperation())
        substitutions[call] = cast<func::FuncOp>(copy);
    }
  }
  auto module = owner->getParentOfType<mlir::ModuleOp>();
  std::optional<CapacityCause> substitutionCapacity;
  auto result = mathematical::substituteScopedComputations(
      module, substitutions, selection, &substitutionCapacity);
  if (!result) {
    if (substitutionCapacity) {
      std::string detail;
      llvm::raw_string_ostream description(detail);
      description << "scoped numerical substitution capacity: "
                  << mathematical::decisionName(substitutionCapacity->owner);
      if (substitutionCapacity->requested)
        description << " requested=" << *substitutionCapacity->requested;
      if (substitutionCapacity->available)
        description << " available=" << *substitutionCapacity->available;
      if (outcome)
        *outcome = {
            optionalConstruction && (substitutionCapacity->owner ==
                                         WorkOwner::AlgorithmExpansion ||
                                     substitutionCapacity->owner ==
                                         WorkOwner::AlgorithmOriginBytes)
                ? mathematical::VerificationObservation::OptionalCapacity
                : mathematical::VerificationObservation::RequiredCapacity,
            detail, substitutionCapacity};
      else
        return refuse(owner, detail);
      return failure();
    }
    return refuse(owner, "scoped numerical substitution refused");
  }
  // Remove original mathematical declarations only after their complete source
  // closure has been admitted and every selected invocation substituted.
  auto target = cast<protocol_ir::ProtocolModuleOp>(result->getBody()->front());
  bool finite = false;
  target.walk(
      [&](Operation *op) { finite |= isa<exec::FoldOp, exec::CollectOp>(op); });
  for (auto &definition : make_early_inc_range(target.getBody().front()))
    if (isa<mlir::ModuleOp>(definition) ||
        (!finite && (isa<data::DomainOp>(definition) ||
                     (isa<func::FuncOp>(definition) &&
                      !protocol::isScopedExecutionFunction(
                          cast<func::FuncOp>(definition))))))
      definition.erase();
  module.walk([&](Operation *op) { selection.origins.erase(op); });
  module.getBodyRegion().takeBody(result->getBodyRegion());
  return success();
}
} // namespace
LogicalResult
discoverComputations(mlir::ModuleOp module,
                     MathematicalSelectionPolicy fallback,
                     mathematical::NumericalSelection &selection) {
  SmallVector<exec::ComputeOp> calls;
  module.walk([&](exec::ComputeOp call) { calls.push_back(call); });
  SymbolTableCollection symbols;
  for (auto call : calls) {
    auto invocation = mathematical::realizationSubject(call);
    selection.enterInvocation(invocation);
    auto entry = call.resolveCallee(symbols);
    auto policy = effectiveSelectionPolicy(call, fallback);
    if (!entry || failed(policy))
      return refuse(call, "invalid numerical closure or policy");
    for (auto &op : entry.front().without_terminator()) {
      if (!selection.chargeCatalog())
        return refuse(call, "numerical occurrence discovery capacity");
      if (!finite::isComputation(&op))
        continue;
      auto occurrence =
          selection.discover(mathematical::realizationSubject(&op),
                             policy->finiteBulk, policy->numericalExpressions);
      if (!occurrence)
        return diagnostics::emit(call.emitOpError(), occurrence.takeError());
    }
  }
  return success();
}
LogicalResult materializeComputations(
    mlir::ModuleOp candidate, MathematicalSelectionPolicy policy,
    mathematical::RealizationTrace *trace,
    mathematical::NumericalSelection &selection,
    mathematical::VerificationDecision *outcome, bool optionalConstruction) {
  return materialize(
      cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front()), policy,
      trace, selection, outcome, optionalConstruction);
}
OwningOpRef<mlir::ModuleOp> proposeComputationRealization(
    mlir::ModuleOp source, MathematicalSelectionPolicy policy,
    mathematical::RealizationTrace *trace,
    mathematical::NumericalSelection *selection, mlir::ModuleOp prepared) {
  loadRealizationDialects(*source.getContext());
  if (failed(zkc::admitStage(source)) || !hasSingleElement(*source.getBody()))
    return {};
  auto owner =
      dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  if (!owner || owner.getProfile() != protocol_ir::Profile::Exec) {
    (void)refuse(source, "expected the exec profile");
    return {};
  }
  mathematical::RealizationScope scope(trace, "propose-computation-realization",
                                       source, policy);
  scope.propose(policy);
  mathematical::NumericalSelection standalone;
  if (!selection)
    selection = &standalone;
  selection->origins.clear();
  OwningOpRef<mlir::ModuleOp> normalized;
  if (!prepared) {
    normalized = prepareComputationRealization(source, selection->remainingCopy,
                                               selection->work);
    if (normalized)
      prepared = *normalized;
  }
  OwningOpRef<mlir::ModuleOp> candidate;
  bool retained = false;
  auto clearRefusedOrigins = llvm::scope_exit([&] {
    if (!retained)
      selection->origins.clear();
  });
  if (prepared && chargeCopy(prepared, selection->remainingCopy))
    candidate = cast<mlir::ModuleOp>(prepared->clone());
  if (!candidate) {
    (void)refuse(source, "checked normalization or concrete frontier refused");
    return {};
  }
  if (failed(discoverComputations(*candidate, policy, *selection)))
    return {};
  if (failed(materializeComputations(*candidate, policy, trace, *selection)) ||
      failed(zkc::admitStage(*candidate)))
    return {};
  scope.publish(mathematical::PublicationBoundary::ReturnedCandidate);
  retained = true;
  return candidate;
}
LogicalResult realizeComputations(mlir::ModuleOp source,
                                  MathematicalSelectionPolicy policy,
                                  mathematical::RealizationTrace *trace) {
  mathematical::RealizationScope scope(trace, "realize-computations", source,
                                       policy);
  scope.propose(policy);
  auto proposal = proposeComputationRealization(source, policy, trace);
  if (!proposal)
    return failure();
  mathematical::CheckedCandidate candidate(source, std::move(proposal));
  if (failed(
          candidate.publish([&](mlir::ModuleOp before, mlir::ModuleOp after) {
            return verifyComputationRealization(before, after, policy);
          })))
    return failure();
  scope.publish(mathematical::PublicationBoundary::PublishedToCaller);
  return success();
}
namespace {
struct RealizeComputationsPass
    : PassWrapper<RealizeComputationsPass, OperationPass<mlir::ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(RealizeComputationsPass)
  MathematicalPassOptions selection{*this};
  mathematical::RealizationTrace *trace = nullptr;
  RealizeComputationsPass() = default;
  RealizeComputationsPass(MathematicalSelectionPolicy policy,
                          mathematical::RealizationTrace *trace)
      : selection(*this, policy), trace(trace) {}
  RealizeComputationsPass(const RealizeComputationsPass &other)
      : PassWrapper(other), selection(*this, other.selection.get()),
        trace(other.trace) {}
  void getDependentDialects(DialectRegistry &registry) const final {
    registerRealizationDialects(registry);
  }
  StringRef getArgument() const final { return "zkc-realize-computations"; }
  StringRef getDescription() const final {
    return "Independently check mathematical realization into scoped execution";
  }
  void runOnOperation() final {
    auto policy = selection.get();
    if (failed(computation::realizeComputations(getOperation(), policy, trace)))
      signalPassFailure();
  }
};
} // namespace
std::unique_ptr<mlir::Pass>
createRealizeComputationsPass(MathematicalSelectionPolicy policy,
                              mathematical::RealizationTrace *trace) {
  return std::make_unique<RealizeComputationsPass>(policy, trace);
}
} // namespace zkc::computation
