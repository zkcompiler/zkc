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
struct OracleCommonEntryRealization {
  std::string entry;
  std::vector<OracleCommonController> controllers;
  std::vector<std::vector<mlir::func::FuncOp>> allocators;
  std::vector<mlir::func::FuncOp> locals;
};
struct OracleCommonRealization {
  mlir::OwningOpRef<mlir::ModuleOp> module;
  std::vector<OracleCommonEntryRealization> entries;
};
// Private common-stage integration of every oracle-bearing prepared entry.
// Ordinary siblings retain their exact bodies. This currently realizes ideal
// tables; unsupported interfaces refuse without changing the original.
// No checked-stage authority or native publication is granted by emission.
llvm::Expected<OracleCommonRealization>
emitIdealOracleRealization(mlir::ModuleOp prepared);
// Re-derive layouts, capacities and the common recipe from the frozen original,
// then read the actual common SSA and every generated helper body. The reader
// never invokes emission. This is native correspondence, not a Lean simulation.
llvm::Error checkIdealOracleRealization(mlir::ModuleOp prepared,
                                        const OracleCommonRealization &actual);
} // namespace zkc::protocol
#endif
