#ifndef ZKC_TRANSFORMS_ORACLEVERIFICATIONCONTEXT_H
#define ZKC_TRANSFORMS_ORACLEVERIFICATIONCONTEXT_H
#include "OracleMerkle.h"
#include "OracleQueryController.h"
#include "zkc/Dialect/Exec/Execution.h"
namespace zkc::protocol {
// Private immutable borrow for one correspondence check. Read formation and
// the source-execution closure once, then check every actual body against it.
// Any mutation invalidates the entire borrow. Never retain it across emission,
// mutation tests or publication; it grants no realization or stage authority.
class OracleVerificationContext {
  mlir::ModuleOp module;
  protocol_ir::ProtocolModuleOp unit;
  SourceExecutionClosure closure;
  OracleVerificationContext(mlir::ModuleOp module,
                            protocol_ir::ProtocolModuleOp unit,
                            SourceExecutionClosure closure)
      : module(module), unit(unit), closure(std::move(closure)) {}

public:
  static llvm::Expected<OracleVerificationContext> read(mlir::ModuleOp);
  mlir::ModuleOp getModule() const { return module; }
  protocol_ir::ProtocolModuleOp getUnit() const { return unit; }
  const SourceExecutionClosure &getClosure() const { return closure; }
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
} // namespace zkc::protocol
#endif
