#ifndef ZKC_TRANSFORMS_ORACLECOMMONREALIZATION_H
#define ZKC_TRANSFORMS_ORACLECOMMONREALIZATION_H
#include "OracleMerkle.h"
#include "OracleQueryBatch.h"
#include "OracleQueryController.h"
#include "OracleQueryPacket.h"
#include "OracleRealizationSelection.h"
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
// Dynamic root inputs append one explicit shape port per logical anchor. The
// original input positions remain fixed; no expected shape is read from a root.
struct OracleInputShape {
  unsigned anchor, port;
  bool operator==(const OracleInputShape &other) const {
    return anchor == other.anchor && port == other.port;
  }
};
// Private helpers are installed once per source-derived receiver controller.
// The exact source schedule and independently read helper bodies bind these
// handles; the record alone grants no authority.
struct OracleCommonRemote {
  unsigned receiver, holder;
  OracleQueryDemand demand;
  OracleQueryResponse response;
  mlir::func::FuncOp open;
  OracleQueryPacket packet;
  OracleQueryWindow window;
};
struct OracleCommonBatch {
  // Ordered indexes into the entry's remote inventory. Source coordinates and
  // capacity are rederived, never supplied as acceptance assumptions.
  std::vector<unsigned> remotes;
  OracleQueryBatch body;
};
struct OracleCommonEntryRealization {
  std::string entry;
  std::vector<OracleMerkleFunctions> merkle;
  std::vector<OracleInputShape> inputShapes;
  std::vector<OracleCommonController> controllers;
  std::vector<std::vector<mlir::func::FuncOp>> allocators;
  std::vector<mlir::func::FuncOp> locals;
  std::vector<OracleCommonRemote> remotes;
  std::vector<OracleCommonBatch> batches;
  std::vector<OracleResultStore> resultStores;
  std::vector<OracleResultReference> resultReferences;
};
struct OracleCommonRealization {
  mlir::OwningOpRef<mlir::ModuleOp> module;
  std::vector<OracleCommonEntryRealization> entries;
};
// Private common-stage integration of every oracle-bearing prepared entry.
// Ordinary siblings retain their exact bodies. Requested choices are normalized
// against actual roots; unsupported interfaces refuse without changing the
// original. No checked-stage authority or native publication is granted by
// emission.
llvm::Expected<OracleCommonRealization>
emitOracleRealization(mlir::ModuleOp prepared,
                      const OracleRealizationPolicy &policy = {});
// Re-derive layouts, capacities and the common recipe from the frozen original,
// then read the actual common SSA and every generated helper body. The reader
// never invokes emission. This is native correspondence, not a Lean simulation.
llvm::Expected<std::string>
serializeOracleRealization(mlir::ModuleOp prepared,
                           const OracleCommonRealization &actual,
                           const OracleRealizationPolicy &policy = {});
llvm::Error checkOracleRealization(mlir::ModuleOp prepared,
                                   mlir::ModuleOp candidate,
                                   llvm::StringRef record,
                                   const OracleRealizationPolicy &policy = {});
} // namespace zkc::protocol
#endif
