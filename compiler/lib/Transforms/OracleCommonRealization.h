#ifndef ZKC_TRANSFORMS_ORACLECOMMONREALIZATION_H
#define ZKC_TRANSFORMS_ORACLECOMMONREALIZATION_H
#include "OracleQueryController.h"
namespace zkc::protocol {
struct OracleCommonController {
  std::string role;
  protocol_ir::OracleKindAttr kind;
  OracleControllerAccess access;
  OracleQueryController body;
};
struct OracleCommonRealization {
  mlir::OwningOpRef<mlir::ModuleOp> module;
  std::vector<OracleCommonController> controllers;
  std::vector<std::vector<mlir::func::FuncOp>> allocators;
  std::vector<mlir::func::FuncOp> locals;
};
// Private common-stage integration. The source is an already prepared, closed
// single-entry protocol. This entry point currently realizes ideal tables;
// unsupported interfaces and operations refuse, without changing the original.
// No checked-stage authority or native publication is granted by emission.
llvm::Expected<OracleCommonRealization>
emitIdealOracleRealization(mlir::ModuleOp prepared, llvm::StringRef entry);
// Re-derive layouts, capacities and the common recipe from the frozen original,
// then read the actual common SSA and every generated helper body. The reader
// never invokes emission. This is native correspondence, not a Lean simulation.
llvm::Error checkIdealOracleRealization(mlir::ModuleOp prepared,
                                        llvm::StringRef entry,
                                        const OracleCommonRealization &actual);
} // namespace zkc::protocol
#endif
