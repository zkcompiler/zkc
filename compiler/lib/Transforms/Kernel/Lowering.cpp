#include "../CheckedCandidate.h"
#include "../RealizationSubject.h"
#include "../RealizationTrace.h"
#include "../ScopedSubstitution.h"
#include "Support.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecDialect.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::kernel {
namespace {
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "kernel-lowering", detail);
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
    for (auto &definition : output.getBody().front()) {
      auto old = SymbolTable::getSymbolName(&definition);
      if (failed(SymbolTable::replaceAllSymbolUses(
              old,
              StringAttr::get(owner.getContext(),
                              renamed.lookup(old.getValue())),
              output)))
        return refuse(call, "numerical symbol import refused");
    }
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
      if (outcome)
        *outcome = {
            optionalConstruction
                ? mathematical::VerificationObservation::OptionalCapacity
                : mathematical::VerificationObservation::RequiredCapacity,
            "scoped numerical substitution capacity", substitutionCapacity};
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
LogicalResult discoverKernelCalls(mlir::ModuleOp module,
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
LogicalResult materializeKernelCalls(
    mlir::ModuleOp candidate, MathematicalSelectionPolicy policy,
    mathematical::RealizationTrace *trace,
    mathematical::NumericalSelection &selection,
    mathematical::VerificationDecision *outcome, bool optionalConstruction) {
  return materialize(
      cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front()), policy,
      trace, selection, outcome, optionalConstruction);
}
OwningOpRef<mlir::ModuleOp>
proposeKernelLowering(mlir::ModuleOp source, MathematicalSelectionPolicy policy,
                      mathematical::RealizationTrace *trace,
                      mathematical::NumericalSelection *selection,
                      mlir::ModuleOp prepared) {
  source.getContext()->getOrLoadDialect<algebra::AlgebraDialect>();
  source.getContext()->getOrLoadDialect<exec::ExecDialect>();
  source.getContext()->getOrLoadDialect<runtime::RuntimeDialect>();
  if (failed(verify(source)) || !hasSingleElement(*source.getBody()))
    return {};
  auto owner =
      dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  if (!owner || owner.getProfile() != protocol_ir::Profile::Exec) {
    (void)refuse(source, "expected the exec profile");
    return {};
  }
  mathematical::RealizationScope scope(trace, "propose-kernel-lowering", source,
                                       policy);
  scope.propose(policy);
  mathematical::NumericalSelection standalone;
  if (!selection)
    selection = &standalone;
  selection->origins.clear();
  OwningOpRef<mlir::ModuleOp> normalized;
  if (!prepared) {
    normalized = prepareKernelLowering(source, &selection->remainingCopy);
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
  if (failed(discoverKernelCalls(*candidate, policy, *selection)))
    return {};
  if (failed(materializeKernelCalls(*candidate, policy, trace, *selection)) ||
      failed(verify(*candidate)))
    return {};
  scope.publish(mathematical::PublicationBoundary::ReturnedCandidate);
  retained = true;
  return candidate;
}
LogicalResult lowerKernels(mlir::ModuleOp source,
                           MathematicalSelectionPolicy policy,
                           mathematical::RealizationTrace *trace) {
  mathematical::RealizationScope scope(trace, "lower-kernels", source, policy);
  scope.propose(policy);
  auto proposal = proposeKernelLowering(source, policy, trace);
  if (!proposal)
    return failure();
  mathematical::CheckedCandidate candidate(source, std::move(proposal));
  if (failed(
          candidate.publish([&](mlir::ModuleOp before, mlir::ModuleOp after) {
            return verifyKernelLowering(before, after, policy);
          })))
    return failure();
  scope.publish(mathematical::PublicationBoundary::PublishedToCaller);
  return success();
}
namespace {
struct LowerKernelsPass
    : PassWrapper<LowerKernelsPass, OperationPass<mlir::ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(LowerKernelsPass)
  Option<bool> finiteBulk{*this, "optimize-finite", llvm::cl::init(true)};
  Option<bool> vectorReductionFusion{*this, "fuse-vector-reductions",
                                     llvm::cl::init(false)};
  Option<bool> collectFoldFusion{*this, "fuse-collect-fold",
                                 llvm::cl::init(false)};
  mathematical::RealizationTrace *trace = nullptr;
  MathematicalSelectionPolicy fallbackPolicy;
  LowerKernelsPass() = default;
  LowerKernelsPass(MathematicalSelectionPolicy policy,
                   mathematical::RealizationTrace *trace)
      : trace(trace), fallbackPolicy(policy) {
    finiteBulk = policy.finiteBulk;
    vectorReductionFusion = policy.vectorReductionFusion;
    collectFoldFusion = policy.collectFoldFusion;
  }
  LowerKernelsPass(const LowerKernelsPass &other)
      : PassWrapper(other), trace(other.trace),
        fallbackPolicy(other.fallbackPolicy) {}
  void getDependentDialects(DialectRegistry &registry) const final {
    registry.insert<runtime::RuntimeDialect, algebra::AlgebraDialect,
                    exec::ExecDialect, func::FuncDialect, scf::SCFDialect,
                    arith::ArithDialect, cf::ControlFlowDialect>();
  }
  StringRef getArgument() const final { return "zkc-lower-kernels"; }
  StringRef getDescription() const final {
    return "Independently check mathematical realization into scoped execution";
  }
  void runOnOperation() final {
    auto policy = fallbackPolicy;
    policy.finiteBulk = finiteBulk;
    policy.vectorReductionFusion = vectorReductionFusion;
    policy.collectFoldFusion = collectFoldFusion;
    if (failed(kernel::lowerKernels(getOperation(), policy, trace)))
      signalPassFailure();
  }
};
} // namespace
std::unique_ptr<mlir::Pass>
createLowerKernelsPass(MathematicalSelectionPolicy policy,
                       mathematical::RealizationTrace *trace) {
  return std::make_unique<LowerKernelsPass>(policy, trace);
}
} // namespace zkc::kernel
