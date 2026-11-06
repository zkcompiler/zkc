#ifndef ZKC_TRANSFORMS_ORACLEVERIFICATIONCONTEXT_H
#define ZKC_TRANSFORMS_ORACLEVERIFICATIONCONTEXT_H
#include "OracleAccounting.h"
#include "OracleCheckedReader.h"
#include "OracleCommonPlan.h"
#include "OracleMerkle.h"
#include "OracleQueryController.h"
#include "zkc/Dialect/Exec/Execution.h"
namespace zkc::protocol {
// Private immutable borrow for one correspondence check. Read formation and
// the source-execution closure once, then check every actual body against it.
// Any mutation invalidates the entire borrow. Never retain it across emission,
// mutation tests or publication; it grants no realization or stage authority.
class OracleVerificationContext {
  friend llvm::Error checkOracleRealizationModel(
      const OracleVerificationContext &, const OracleVerificationContext &,
      llvm::ArrayRef<OracleCommonEntryRealization>,
      llvm::ArrayRef<OracleRootSelection>, OracleAuthentication,
      OracleRealizationFacts *, OracleNativeWork *,
      const OracleNativeSourcePreflight *, const OracleNativeSourcePreflight *,
      std::vector<OracleCommonAnalysis> *);
  friend llvm::Error checkOracleVirtualFunctions(
      const OracleVerificationContext &, const OracleVerificationContext &,
      protocol_ir::OracleDefinitionOp, const OracleVirtualFunctions &);
  friend struct OracleControllerReader;
  friend llvm::Error checkOracleAnchorLookup(const OracleVerificationContext &,
                                             mlir::func::FuncOp,
                                             const OracleAnchorStorage &,
                                             unsigned, unsigned);
  friend llvm::Error checkOracleTableRead(const OracleVerificationContext &,
                                          mlir::func::FuncOp,
                                          protocol_ir::OracleKindAttr);
  // Successful exact virtual-body correspondences for these immutable reader
  // contexts only. Keys include all supplied model fields and live functions.
  mutable llvm::DenseMap<mlir::Operation *, llvm::DenseSet<mlir::ArrayAttr>>
      checkedVirtualFunctions;
  // Only the independent readers can record a successful full body check.
  // Complete expected signatures and source-derived model fields form the
  // keys; these facts end with this exact immutable candidate borrow.
  mutable llvm::DenseSet<mlir::ArrayAttr> checkedControllerCounts;
  mutable llvm::DenseSet<mlir::ArrayAttr> checkedAnchorLookups;
  mutable llvm::DenseSet<mlir::ArrayAttr> checkedTableReads;
  mlir::ModuleOp module;
  protocol_ir::ProtocolModuleOp unit;
  std::shared_ptr<const SourceExecutionClosure> closure;
  mutable llvm::DenseSet<mlir::DictionaryAttr> checkedBindings;
  // Raw readers retain their own allowance/preflight. Composed readers borrow
  // the caller's exact immutable preflight for the entire check.
  std::shared_ptr<OracleNativeWork> ownedWork;
  std::shared_ptr<OracleNativeSourcePreflight> ownedPreflight;
  OracleNativeWork *work = nullptr;
  const OracleNativeSourcePreflight *preflight = nullptr;
  OracleVerificationContext(
      mlir::ModuleOp module, protocol_ir::ProtocolModuleOp unit,
      std::shared_ptr<const SourceExecutionClosure> closure,
      OracleNativeWork &work, const OracleNativeSourcePreflight &preflight)
      : module(module), unit(unit), closure(std::move(closure)), work(&work),
        preflight(&preflight) {}
  llvm::Expected<llvm::SmallVector<CommonControlRequirement>>
  complete(protocol_ir::ProtocolModuleOp original,
           llvm::ArrayRef<zkc::detail::OracleRepeatCount>, facts::Work &) const;

public:
  static llvm::Expected<OracleVerificationContext> read(mlir::ModuleOp);
  static llvm::Expected<OracleVerificationContext> read(mlir::ModuleOp,
                                                        OracleNativeWork &);
  static llvm::Expected<OracleVerificationContext>
  readCandidate(mlir::ModuleOp, OracleNativeWork &);
  static llvm::Expected<OracleVerificationContext>
  read(mlir::ModuleOp, OracleNativeWork &, const OracleNativeSourcePreflight &);
  // Private implementation borrow, with no stage-admission authority. Only a
  // complete independent paired model check can finish this candidate.
  static llvm::Expected<OracleVerificationContext>
      readCandidate(mlir::ModuleOp);
  static llvm::Expected<OracleVerificationContext>
  readCandidate(mlir::ModuleOp, OracleNativeWork &,
                const OracleNativeSourcePreflight &);
  bool charge(uint64_t amount = 1) const { return work->charge(amount); }
  OracleNativeWork &getWork() const { return *work; }
  mlir::SymbolTableCollection &getSymbols() const {
    return preflight->getSymbols();
  }
  bool matchesBinding(runtime::BindingOp binding,
                      const NativeBindingApplication &expected) const {
    if (!charge(1 + expected.contract.size() + expected.implementation.size() +
                expected.arguments.size()) ||
        !binding || binding->getParentOp() != unit ||
        binding.getContract() != expected.contract ||
        binding.getImplementation() != expected.implementation ||
        !llvm::equal(binding.getArguments(), expected.arguments))
      return false;
    auto attributes = binding->getAttrDictionary();
    if (checkedBindings.contains(attributes))
      return true;
    auto silent = [&] {
      auto diagnostic = binding.emitOpError();
      diagnostic.abandon();
      return diagnostic;
    };
    if (mlir::failed(readNativeBinding(silent, binding, false)) || !charge())
      return false;
    checkedBindings.insert(attributes);
    return true;
  }
  bool reserveRead(mlir::Operation *root) const {
    return preflight->reserveTraversal(root);
  }
  mlir::ModuleOp getModule() const { return module; }
  protocol_ir::ProtocolModuleOp getUnit() const { return unit; }
  const SourceExecutionClosure &getClosure() const { return *closure; }
};
llvm::Error checkOracleAnchorAllocator(const OracleVerificationContext &,
                                       mlir::func::FuncOp,
                                       const OracleAnchorStorage &,
                                       unsigned constructor, unsigned role);
llvm::Error checkOracleAnchorLookup(const OracleVerificationContext &,
                                    mlir::func::FuncOp,
                                    const OracleAnchorStorage &,
                                    unsigned constructor, unsigned role);
llvm::Error checkOracleMerkle(const OracleVerificationContext &,
                              const OracleMerkleFunctions &,
                              protocol_ir::OracleKindAttr,
                              llvm::StringRef scheme, OracleLeafGrouping,
                              OracleLeafOrder);
llvm::Error checkOracleTableRead(const OracleVerificationContext &,
                                 mlir::func::FuncOp,
                                 protocol_ir::OracleKindAttr);
llvm::Error
checkOracleVirtualFunctions(const OracleVerificationContext &candidate,
                            const OracleVerificationContext &source,
                            protocol_ir::OracleDefinitionOp,
                            const OracleVirtualFunctions &);
llvm::Error checkOracleQueryController(
    const OracleVerificationContext &candidate,
    const OracleVerificationContext &source, const OracleAnchorStorage &,
    llvm::StringRef role, protocol_ir::OracleKindAttr root,
    OracleQuerySize capacity, const OracleQueryController &,
    OracleControllerAccess);
llvm::Error checkOracleQueryDemand(const OracleVerificationContext &,
                                   const OracleVerificationContext &,
                                   const OracleAnchorStorage &,
                                   const OracleQueryController &,
                                   protocol_ir::OracleKindAttr,
                                   const OracleQueryDemand &,
                                   const OracleCheckedController &);
llvm::Error checkOracleQueryWindow(const OracleVerificationContext &,
                                   const OracleQueryController &,
                                   const OracleQueryDemand &,
                                   const OracleQueryExchange &,
                                   const OracleQueryResponse &,
                                   const OracleQueryWindow &,
                                   const OracleCheckedResponse &);
} // namespace zkc::protocol
#endif
