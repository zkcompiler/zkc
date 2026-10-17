#include "../CheckedCandidate.h"
#include "../RealizationTrace.h"
#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Transforms/Passes.h"
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
                          mathematical::RealizationTrace *trace) {
  SmallVector<CallOp> calls;
  owner.walk([&](CallOp call) { calls.push_back(call); });
  SymbolTable outer(owner);
  unsigned nextBinding = 0;
  llvm::DenseMap<DictionaryAttr, std::string> importedBindings;
  uint64_t remaining = 1000000, remainingBytes = 16 * 1024 * 1024;
  mathematical::RealizationWork work;
  for (auto call : calls) {
    SymbolTableCollection symbols;
    auto entry = resolve(call, symbols);
    auto policy = selectionPolicy(call, fallback);
    if (!entry || failed(policy))
      return refuse(call, "invalid numerical closure or policy");
    auto unit = cast<ModuleOp>(entry->getParentOp());
    auto scratch = realizeEntry(unit, call.getSite(), *policy, work, remaining,
                                remainingBytes, {}, trace);
    if (!scratch)
      return refuse(call, "numerical recipes refused the actual closure");
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
        if (cost > remaining)
          return WalkResult::interrupt();
        remaining -= cost;
        return WalkResult::advance();
      });
      if (walk.wasInterrupted())
        return refuse(call, "inlining work limit");
      builder.clone(op, values);
    }
    auto returned = cast<local::ReturnOp>(function.getBody().front().back());
    if (returned.getNumOperands() != call.getNumResults())
      return refuse(call, "recipe return interface changed");
    for (auto [output, value] : zip(call.getResults(), returned.getInputs()))
      output.replaceAllUsesWith(values.lookup(value));
    call.erase();
  }
  // Formation already checked dormant definitions. They create no executable
  // work but still cannot remain in physical input, even when there are no
  // calls.
  for (auto unit :
       make_early_inc_range(owner.getBody().front().getOps<ModuleOp>()))
    unit.erase();
  return success();
}
} // namespace
LogicalResult lowerKernels(mlir::ModuleOp source,
                           MathematicalSelectionPolicy policy,
                           mathematical::RealizationTrace *trace) {
  source.getContext()->getOrLoadDialect<algebra::AlgebraDialect>();
  source.getContext()->getOrLoadDialect<local::LocalDialect>();
  if (failed(verify(source)) || !hasSingleElement(*source.getBody()))
    return failure();
  auto owner =
      dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  if (!owner || owner.getProfile() != protocol_ir::Profile::Exec)
    return refuse(source, "expected the exec profile");
  mathematical::RealizationScope scope(trace, "lower-kernels", source, policy);
  scope.propose(policy);
  auto prepared = prepareKernelLowering(source);
  if (!prepared)
    return refuse(source, "checked normalization or concrete frontier refused");
  mathematical::CheckedCandidate candidate(source, std::move(prepared));
  auto proposed =
      cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
  if (failed(materialize(proposed, policy, trace)) ||
      failed(
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
  MathematicalSelectionPolicy policy;
  mathematical::RealizationTrace *trace = nullptr;
  LowerKernelsPass() = default;
  LowerKernelsPass(MathematicalSelectionPolicy policy,
                   mathematical::RealizationTrace *trace)
      : policy(policy), trace(trace) {}
  void getDependentDialects(DialectRegistry &registry) const final {
    registry.insert<local::LocalDialect, algebra::AlgebraDialect,
                    kernel::KernelDialect, func::FuncDialect>();
  }
  StringRef getArgument() const final { return "zkc-lower-kernels"; }
  StringRef getDescription() const final {
    return "Independently check logical Kernel realization into existing Local "
           "execution";
  }
  void runOnOperation() final {
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
