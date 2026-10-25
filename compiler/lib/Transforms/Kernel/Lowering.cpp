#include "../AlgorithmSupport.h"
#include "../CheckedCandidate.h"
#include "../RealizationSubject.h"
#include "../RealizationTrace.h"
#include "Support.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecDialect.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringMap.h"

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
  SmallVector<CallOp> calls;
  owner.walk([&](CallOp call) { calls.push_back(call); });
  SymbolTable outer(owner);
  unsigned nextBinding = 0;
  llvm::DenseMap<DictionaryAttr, std::string> importedBindings;
  auto &remaining = selection.remainingCopy;
  auto &remainingBytes = selection.remainingSiteBytes;
  auto &work = selection.work;
  for (auto [invocation, call] : enumerate(calls)) {
    selection.enterInvocation(invocation);
    SymbolTableCollection symbols;
    auto entry = resolve(call, symbols);
    auto policy = effectiveSelectionPolicy(call, fallback);
    if (!entry || failed(policy))
      return refuse(call, "invalid numerical closure or policy");
    auto unit = cast<mlir::ModuleOp>(entry->getParentOp());
    auto scratch = realizeEntry(unit, call.getSite(), *policy, work, remaining,
                                remainingBytes, {}, trace, &selection, outcome,
                                optionalConstruction);
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
        SymbolTable(output).lookup<local::FuncOp>(entry.getSymName());
    // Import declarations under fresh outer identities. References are renamed
    // only in this private workspace; nominal domains and source units remain
    // unchanged. Original fixed bindings are never reused or modified.
    StringMap<std::string> renamed;
    SmallVector<local::OperationBindingOp> bindings;
    for (auto binding :
         output.getBody().front().getOps<local::OperationBindingOp>()) {
      NamedAttrList signature(binding->getAttrs());
      signature.erase("sym_name");
      auto key = signature.getDictionary(owner.getContext());
      auto found = importedBindings.find(key);
      if (found != importedBindings.end()) {
        renamed[binding.getSymName()] = found->second;
        continue;
      }
      std::string name;
      do {
        name = "_kernel_binding_" + std::to_string(nextBinding++);
      } while (outer.lookup(name));
      importedBindings.try_emplace(key, name);
      renamed[binding.getSymName()] = name;
      bindings.push_back(binding);
    }
    scratch->walk([&](Operation *op) {
      if (auto binding = op->getAttrOfType<FlatSymbolRefAttr>("binding")) {
        auto found = renamed.find(binding.getValue());
        if (found != renamed.end())
          op->setAttr("binding",
                      FlatSymbolRefAttr::get(op->getContext(), found->second));
      }
    });
    OpBuilder builder(owner.getContext());
    builder.setInsertionPointToStart(&owner.getBody().front());
    for (auto binding : bindings) {
      std::optional<CapacityCause> capacity;
      if (!chargeCopy(binding, remaining, &capacity)) {
        if (outcome)
          *outcome = {
              optionalConstruction
                  ? mathematical::VerificationObservation::OptionalCapacity
                  : mathematical::VerificationObservation::RequiredCapacity,
              "Kernel binding import capacity", capacity};
        return failure();
      }
      auto *copy = builder.clone(*binding.getOperation());
      SymbolTable::setSymbolName(copy, renamed.lookup(binding.getSymName()));
      outer.insert(copy);
    }
    builder.setInsertionPoint(call);
    IRMapping values;
    values.map(function.getArguments(), call.getInputs());
    for (auto &op : function.getBody().front().without_terminator()) {
      auto walk = op.walk([&](Operation *nested) {
        uint64_t cost = 1 + nested->getNumOperands() + nested->getNumResults();
        if (cost > remaining) {
          if (outcome)
            *outcome = {
                optionalConstruction
                    ? mathematical::VerificationObservation::OptionalCapacity
                    : mathematical::VerificationObservation::RequiredCapacity,
                "Kernel inline copy capacity",
                CapacityCause{WorkOwner::AlgorithmExpansion, cost, remaining}};
          return WalkResult::interrupt();
        }
        remaining -= cost;
        return WalkResult::advance();
      });
      if (walk.wasInterrupted())
        return outcome ? failure() : refuse(call, "inlining work limit");
      builder.clone(op, values);
      op.walk([&](Operation *nested) {
        auto owners = selection.owners(nested);
        for (auto occurrence : owners)
          selection.record(values.lookup(nested), occurrence);
      });
    }
    auto returned = cast<local::ReturnOp>(function.getBody().front().back());
    if (returned.getNumOperands() != call.getNumResults())
      return refuse(call, "recipe return interface changed");
    for (auto [output, value] : zip(call.getResults(), returned.getInputs()))
      output.replaceAllUsesWith(values.lookup(value));
    call.erase();
  }
  // Identity recipes can alias captures that were distinct before inlining.
  // Rewrite their ports together before physical scheduling sees the module.
  if (failed(protocol::detail::canonicalizeCaptures(owner)))
    return refuse(owner, "capture normalization refused");
  // Formation already checked dormant definitions. They create no executable
  // work but still cannot remain in physical input, even when there are no
  // calls.
  for (auto unit :
       make_early_inc_range(owner.getBody().front().getOps<mlir::ModuleOp>()))
    unit.erase();
  return success();
}
} // namespace
LogicalResult discoverKernelCalls(mlir::ModuleOp module,
                                  MathematicalSelectionPolicy fallback,
                                  mathematical::NumericalSelection &selection) {
  SmallVector<CallOp> calls;
  module.walk([&](CallOp call) { calls.push_back(call); });
  SymbolTableCollection symbols;
  for (auto [invocation, call] : enumerate(calls)) {
    selection.enterInvocation(invocation);
    auto entry = resolve(call, symbols);
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
  source.getContext()->getOrLoadDialect<local::LocalDialect>();
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
    registry.insert<local::LocalDialect, algebra::AlgebraDialect,
                    kernel::KernelDialect, exec::ExecDialect, func::FuncDialect,
                    scf::SCFDialect, arith::ArithDialect>();
  }
  StringRef getArgument() const final { return "zkc-lower-kernels"; }
  StringRef getDescription() const final {
    return "Independently check logical Kernel realization into existing Local "
           "execution";
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
