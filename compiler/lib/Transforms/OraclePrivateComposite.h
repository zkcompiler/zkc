#ifndef ZKC_TRANSFORMS_ORACLEPRIVATECOMPOSITE_H
#define ZKC_TRANSFORMS_ORACLEPRIVATECOMPOSITE_H

#include "OracleMerkle.h"
#include "OracleQueryBatch.h"
#include "OracleQueryResponse.h"
#include "mlir/IR/BuiltinOps.h"
#include <memory>

namespace zkc::protocol {
class OracleEmissionSession;

// Owns a mutable candidate for one composed private generation. Its only
// mutation interface is the closed set of producers below. The candidate and
// its shared allowance leave this scope only after an independent final read.
// Raw public producers remain independently admitted on every invocation.
class OraclePrivateComposite {
  mlir::OwningOpRef<mlir::ModuleOp> candidate, source;
  OracleVirtualFunctionWork work;
  std::unique_ptr<OracleNativeSourcePreflight> sourcePreflight;
  std::unique_ptr<OracleEmissionSession> emission;

  OraclePrivateComposite(mlir::OwningOpRef<mlir::ModuleOp> candidate,
                         OracleVirtualFunctionWork work);
  static llvm::Expected<std::unique_ptr<OraclePrivateComposite>>
  begin(mlir::OwningOpRef<mlir::ModuleOp> candidate, mlir::ModuleOp prepared,
        OracleVirtualFunctionWork work);

public:
  struct Finished {
    mlir::OwningOpRef<mlir::ModuleOp> candidate;
    OracleVirtualFunctionWork work;
  };
  static llvm::Expected<std::unique_ptr<OraclePrivateComposite>>
  create(mlir::OwningOpRef<mlir::ModuleOp> candidate, mlir::ModuleOp prepared,
         OracleVirtualFunctionWork work = {});
  ~OraclePrivateComposite();
  OraclePrivateComposite(const OraclePrivateComposite &) = delete;
  OraclePrivateComposite &operator=(const OraclePrivateComposite &) = delete;

  llvm::Expected<OracleQueryController>
  controller(const OracleAnchorStorage &, llvm::StringRef role,
             protocol_ir::OracleKindAttr root, OracleQuerySize capacity,
             OracleControllerAccess access = OracleControllerAccess::Available);
  llvm::Expected<OracleMerkleFunctions> merkle(protocol_ir::OracleKindAttr kind,
                                               llvm::StringRef scheme,
                                               OracleLeafGrouping grouping,
                                               OracleLeafOrder order);
  llvm::Expected<OracleQueryResponse>
  response(const OracleQueryExchange &exchange);
  llvm::Expected<OracleQueryDemand> demand(const OracleAnchorStorage &,
                                           const OracleQueryController &,
                                           protocol_ir::OracleKindAttr root);
  llvm::Expected<OracleQueryWindow> window(const OracleQueryController &,
                                           const OracleQueryDemand &,
                                           const OracleQueryExchange &,
                                           const OracleQueryResponse &,
                                           uint64_t capacity);
  llvm::Expected<OracleQueryBatch>
  batch(llvm::ArrayRef<OracleQueryBatchRoot> roots);
  std::pair<unsigned, uint64_t> primitiveCapacity() const {
    return {work.operations, work.slots};
  }
  llvm::Expected<Finished> finish();
};
} // namespace zkc::protocol
#endif
