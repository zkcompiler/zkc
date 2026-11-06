#ifndef ZKC_TRANSFORMS_ORACLEREALIZATIONSELECTION_H
#define ZKC_TRANSFORMS_ORACLEREALIZATIONSELECTION_H
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Transforms/OracleSelection.h"
#include "llvm/Support/Error.h"
namespace zkc::protocol {
struct OracleNativeWork;
class OracleNativeSourcePreflight;
// Normalize against the frozen prepared program, in original declaration and
// occurrence order. Virtual declarations and rebindings are not commit roots.
llvm::Expected<std::vector<OracleRootSelection>>
resolveOracleRealizationSelection(mlir::ModuleOp prepared,
                                  const OracleRealizationPolicy &);
llvm::Expected<std::vector<OracleRootSelection>>
resolveOracleRealizationSelectionWithWork(mlir::ModuleOp,
                                          const OracleRealizationPolicy &,
                                          OracleNativeWork &,
                                          const OracleNativeSourcePreflight &);
} // namespace zkc::protocol
#endif
