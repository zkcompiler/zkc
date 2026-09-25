#ifndef ZKC_COMPILER_CONSTRUCTION_H
#define ZKC_COMPILER_CONSTRUCTION_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Source/Model.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"

namespace zkc::protocol {

/// The caller-provided MLIR context must outlive the owned module.
struct ConstructionResult {
  mlir::OwningOpRef<mlir::ModuleOp> module;
  llvm::json::Value certificate;
};

/// Construct from the original source and descriptor snapshots. Structural and
/// semantic admission, source-relative dependency/resource analysis, and MLIR
/// verification remain mandatory for programmatically built records. The JSON
/// certificate includes the common source. The owned module is that same
/// source after checked import; callers need not decode or import it again.
llvm::Expected<ConstructionResult> construct(const source::Module &,
                                             const source::Construction &,
                                             mlir::MLIRContext &);
llvm::Error checkConstruction(const source::Module &,
                              const source::Construction &,
                              const llvm::json::Value &candidate,
                              mlir::MLIRContext &);

} // namespace zkc::protocol
#endif
