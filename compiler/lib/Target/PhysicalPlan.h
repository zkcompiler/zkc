#ifndef ZKC_TARGET_PHYSICAL_PLAN_H
#define ZKC_TARGET_PHYSICAL_PLAN_H

#include "StorageSchedule.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Program/Model.h"
#include "zkc/Target/Catalog.h"
#include "zkc/Transforms/LinearContraction.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include "zkc/Transforms/MathematicalWork.h"
#include <functional>
#include <memory>

namespace zkc::target {
class CheckedPhysicalPlan;
}
namespace zkc::protocol {
llvm::Error verifyPhysicalMaterialization(mlir::ModuleOp, mlir::ModuleOp,
                                          const target::CheckedPhysicalPlan &);
}
namespace zkc::target {
class ImplementationPlan;
class PhysicalPlan;
using OperationIndex = size_t;
using BindingIndex = size_t;
/// Original declarations include bindings generated in the selected Local
/// payload; they need not have existed in the original Kernel source.
enum class BindingPurpose { Original, Contraction, Conversion };
struct BindingDecision {
  protocol::OperationBinding binding;
  BindingPurpose purpose = BindingPurpose::Original;
  std::optional<OperationIndex> declaration;
  bool fixed = false;
  OperationIndex location = 0;
};
struct UseConversion {
  unsigned operand;
  BindingIndex binding;
  mlir::Type from, to;
  std::string site;
};
/// Preorder indices in the selected Local subject, never borrowed
/// operation/value pointers. With Kernel input this is the retained numerical
/// payload, not the original source; otherwise it is the unchanged source.
/// Binding declaration/location and contraction indices use the same subject.
/// Ports belong to individual definitions and uses, not a global logical map.
struct OperationDecision {
  OperationIndex operation;
  std::optional<BindingIndex> binding;
  llvm::SmallVector<mlir::Type> inputs, outputs;
  llvm::SmallVector<llvm::SmallVector<mlir::Type>> blockArguments;
  mlir::FunctionType functionType;
  llvm::SmallVector<UseConversion> conversions;
};
struct ContractionDecision {
  OperationIndex producer;
  llvm::SmallVector<OperationIndex> consumers;
};
enum class PhysicalFailureKind {
  Terminal,
  ImplementationUnavailable,
  ConversionUnavailable,
  OptionalProgramCapacity
};
/// Attribution uses the current retained Local index space, never pointers
/// into a candidate that can be discarded. Conversion reports both endpoints.
struct PhysicalFailure {
  PhysicalFailureKind kind = PhysicalFailureKind::Terminal;
  llvm::SmallVector<OperationIndex> operations;
  llvm::SmallVector<BindingIndex> bindings;
  std::optional<unsigned> operand;
  mlir::Type from, to;
};
struct PhysicalPlanOptions {
  bool linearContractions = false;
  // Propose earliest legal releases; validation also accepts safe alternatives.
  bool releaseStorage = false;
  /// Optional final escaped-program preflight. Receives a charged private
  /// clone; the caller applies the supplied choices and uses the ordinary
  /// program reader. The clone is borrowed only for the callback's duration.
  /// A success result is empty; only an attributable optional capacity refusal
  /// may report operation indices. All other errors remain terminal. This
  /// callback cannot publish or search. Conversion owns physical application.
  std::function<llvm::Expected<llvm::SmallVector<OperationIndex>>(
      mlir::ModuleOp, const PhysicalPlan &)>
      programCapacity = {};
  /// Optional caller-owned existing work account. Every return settles actual
  /// debits, including failed physical attempts; no retry replenishes it.
  mathematical::RealizationWork *numericalWork = nullptr;
  uint64_t *numericalCopy = nullptr;
  uint64_t *numericalSiteBytes = nullptr;
  MathematicalSelectionPolicy numericalPolicy = {};
};
class PhysicalPlan {
  // Share the source-bound implementation independently of physical bindings.
  // It owns original identity and the selected executable realization.
  // Copies share private immutable state; no
  // public MLIR handle can mutate the retained payload. The original module
  // and its MLIR context must remain live when checking or materializing.
  std::shared_ptr<const ImplementationPlan> implementation;
  bool linearContractions = false;
  friend llvm::Expected<PhysicalPlan>
  proposePhysical(mlir::ModuleOp, const CandidateCatalog &,
                  llvm::ArrayRef<std::pair<std::string, std::string>>,
                  PhysicalPlanOptions, mlir::Location *);
  friend llvm::Expected<CheckedPhysicalPlan>
  validatePhysical(mlir::ModuleOp, const PhysicalPlan &,
                   const CandidateCatalog &, mlir::Location *);
  friend class CheckedPhysicalPlan;
  friend llvm::Error
  protocol::verifyPhysicalMaterialization(mlir::ModuleOp, mlir::ModuleOp,
                                          const CheckedPhysicalPlan &);
  // Only the independent reader borrows the retained subject. All external
  // inspection receives a clone, so callers cannot edit checked plan state.
  llvm::Expected<mlir::ModuleOp> selectedSubject(mlir::ModuleOp source) const;

public:
  llvm::SmallVector<BindingDecision> bindings;
  llvm::SmallVector<OperationDecision, 0> operations;
  llvm::SmallVector<ContractionDecision> contractions;
  llvm::SmallVector<StorageRelease> releases;
  /// Freshness-check source and return an independently owned inspection copy
  /// of the selected Local subject (a source clone for the no-Kernel path).
  /// Its preorder corresponds to all decision indices. Editing or destroying
  /// the copy cannot change this proposal or any checked plan derived from it.
  llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
  cloneSelectedSubject(mlir::ModuleOp source) const;
};
/// The only constructor is private to independent validation. Own a copy so a
/// caller cannot mutate a once-checked proposal through an alias.
class CheckedPhysicalPlan {
  PhysicalPlan plan;
  LinearContractionStats statistics;
  CheckedPhysicalPlan(const PhysicalPlan &plan,
                      LinearContractionStats statistics)
      : plan(plan), statistics(statistics) {}
  friend llvm::Expected<CheckedPhysicalPlan>
  validatePhysical(mlir::ModuleOp, const PhysicalPlan &,
                   const CandidateCatalog &, mlir::Location *);

public:
  const PhysicalPlan &choices() const { return plan; }
  const LinearContractionStats &stats() const { return statistics; }
  llvm::Error checkInput(mlir::ModuleOp) const;
  /// Return only a safe owned copy, including through choices().
  llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
  cloneSelectedSubject(mlir::ModuleOp source) const {
    return plan.cloneSelectedSubject(source);
  }
};

/// Optional diagnostic location is copied from the source or selected subject,
/// without parsing or changing the structured error. A Location remains valid
/// after a refused temporary candidate is destroyed (while its context lives).
llvm::Expected<PhysicalPlan> proposePhysical(
    mlir::ModuleOp, const CandidateCatalog & = installedCandidates(),
    llvm::ArrayRef<std::pair<std::string, std::string>> selections = {},
    PhysicalPlanOptions options = {},
    mlir::Location *failureLocation = nullptr);
llvm::Expected<CheckedPhysicalPlan>
validatePhysical(mlir::ModuleOp, const PhysicalPlan &,
                 const CandidateCatalog & = installedCandidates(),
                 mlir::Location *failureLocation = nullptr);
/// Preorder of the supplied module. For Kernel plans use cloneSelectedSubject
/// to obtain the selected index space; the original source has different
/// indices. Materialization uses the corresponding retained-subject clone.
llvm::SmallVector<mlir::Operation *> physicalPlanOperations(mlir::ModuleOp);
} // namespace zkc::target
#endif
