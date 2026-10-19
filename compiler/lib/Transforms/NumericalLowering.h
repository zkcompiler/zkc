#ifndef ZKC_TRANSFORMS_NUMERICALLOWERING_H
#define ZKC_TRANSFORMS_NUMERICALLOWERING_H

#include "MapOccurrence.h"
#include "NumericalSelection.h"
#include <map>
#include <set>

namespace zkc::mathematical {
/// Transient producer cache over a single immutable prepared source. This is
/// not retained by a physical plan and is never supplied to correspondence.
struct PreparedMaps {
  struct Formula {
    mlir::OwningOpRef<mlir::func::FuncOp> scalar;
    bool dot = false;
  };
  std::map<std::string, Formula> formulas;
  std::set<std::string> helpers;
};
mlir::LogicalResult prepareRetainedMaps(mlir::ModuleOp, PreparedMaps &,
                                        NumericalSelection &,
                                        MathematicalSelectionPolicy);
/// Consume maps in an already private complete candidate. Kernel emission
/// shares the same session; neither worker clones the containing module.
/// optionalConstruction classifies the enclosing copy/site envelope only;
/// required formula work and semantic/replacement obligations stay required.
mlir::LogicalResult materializeRetainedMaps(mlir::ModuleOp,
                                            const PreparedMaps &,
                                            NumericalSelection &,
                                            MathematicalSelectionPolicy,
                                            VerificationDecision &,
                                            bool optionalConstruction = false);

/// Naming only, shared by producer and reader. The path extends the concrete
/// retained source site by its exact helper identity. The ordinary algorithm
/// encoder owns depth, byte bounds and deterministic long-site hashing.
llvm::Expected<std::string> mapPayloadSite(algebra::MapRealizeOp,
                                           llvm::StringRef callSite,
                                           unsigned index, uint64_t &bytes);
} // namespace zkc::mathematical
#endif
