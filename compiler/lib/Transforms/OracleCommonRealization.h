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
// Representation support is separate from authored results. Original result
// positions stay fixed; role-specific immutable stores follow them once each.
struct OracleResultStore {
  // Role indexes the selected constructor's role inventory; port indexes the
  // complete native result tuple, before participant projection.
  unsigned constructor, role, port;
  bool operator==(const OracleResultStore &other) const {
    return constructor == other.constructor && role == other.role &&
           port == other.port;
  }
};
struct OracleResultReference {
  // The original result position is also its native reference position.
  unsigned result;
  std::string role;
  std::vector<unsigned> storePorts;
  bool operator==(const OracleResultReference &other) const {
    return result == other.result && role == other.role &&
           storePorts == other.storePorts;
  }
};
struct OracleCommonEntryRealization {
  std::string entry;
  std::vector<OracleCommonController> controllers;
  std::vector<std::vector<mlir::func::FuncOp>> allocators;
  std::vector<mlir::func::FuncOp> locals;
  std::vector<OracleResultStore> resultStores;
  std::vector<OracleResultReference> resultReferences;
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
llvm::Expected<std::string>
serializeIdealOracleRealization(mlir::ModuleOp prepared,
                                const OracleCommonRealization &actual);
llvm::Error checkIdealOracleRealization(mlir::ModuleOp prepared,
                                        mlir::ModuleOp candidate,
                                        llvm::StringRef record);
} // namespace zkc::protocol
#endif
