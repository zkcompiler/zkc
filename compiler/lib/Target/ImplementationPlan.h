#ifndef ZKC_TARGET_IMPLEMENTATION_PLAN_H
#define ZKC_TARGET_IMPLEMENTATION_PLAN_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Contracts/Binding.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include "llvm/Support/Error.h"

namespace zkc::target {
class CandidateCatalog;
class PhysicalPlan;
class CheckedPhysicalPlan;
struct PhysicalPlanOptions;
/// The retained meaning-to-implementation edge, independent of physical port,
/// storage and binding decisions. Current realizations are Local/provider
/// programs. This does not promise a foreign ABI or a generated-code backend.
/// Construction records source identity; independent validation reads the
/// actual retained realization. Neither recipes nor policy flags are evidence.
class ImplementationPlan {
  mlir::ModuleOp source;
  std::string contents;
  llvm::SmallVector<const void *> addresses;
  protocol::Assignments requests;
  MathematicalSelectionPolicy policy;
  mlir::OwningOpRef<mlir::ModuleOp> realization;

  friend class PhysicalPlan;
  friend llvm::Expected<PhysicalPlan>
  proposePhysical(mlir::ModuleOp, const CandidateCatalog &,
                  llvm::ArrayRef<std::pair<std::string, std::string>>,
                  PhysicalPlanOptions, mlir::Location *);
  friend llvm::Expected<CheckedPhysicalPlan>
  validatePhysical(mlir::ModuleOp, const PhysicalPlan &,
                   const CandidateCatalog &, mlir::Location *);
  /// Borrow the retained realization or original source after checking input.
  mlir::ModuleOp subject() const;

public:
  ImplementationPlan(mlir::ModuleOp,
                     llvm::ArrayRef<std::pair<std::string, std::string>>,
                     MathematicalSelectionPolicy);
  const protocol::Assignments &selections() const { return requests; }
  llvm::Error checkInput(mlir::ModuleOp) const;
  llvm::Error verifyRealization(mlir::ModuleOp) const;
};
} // namespace zkc::target
#endif
