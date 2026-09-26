#ifndef ZKC_TARGET_PHYSICAL_PLAN_H
#define ZKC_TARGET_PHYSICAL_PLAN_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Source/Model.h"
#include "zkc/Target/Catalog.h"
#include "zkc/Transforms/LinearContraction.h"
#include <memory>

namespace zkc::target {
struct InputSnapshot;
using OperationIndex = size_t;
using BindingIndex = size_t;
enum class BindingPurpose { Original, Contraction, Conversion };
struct BindingDecision {
  source::OperationBinding binding;
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
/// Original preorder indices, never borrowed operation/value pointers. Ports
/// belong to individual definitions and uses, not to a global logical type map.
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
class CheckedPhysicalPlan;
class PhysicalPlan {
  std::shared_ptr<const InputSnapshot> input;
  friend llvm::Expected<PhysicalPlan>
  proposePhysical(mlir::ModuleOp, const CandidateCatalog &,
                  llvm::ArrayRef<std::pair<std::string, std::string>>, bool,
                  mlir::Location *);
  friend llvm::Expected<CheckedPhysicalPlan>
  validatePhysical(mlir::ModuleOp, const PhysicalPlan &,
                   const CandidateCatalog &, mlir::Location *);
  friend class CheckedPhysicalPlan;

public:
  llvm::SmallVector<BindingDecision> bindings;
  llvm::SmallVector<OperationDecision, 0> operations;
  llvm::SmallVector<ContractionDecision> contractions;
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
};

/// Optional diagnostic location is set from the live declaration/operation,
/// without parsing or changing the structured error.
llvm::Expected<PhysicalPlan> proposePhysical(
    mlir::ModuleOp, const CandidateCatalog & = installedCandidates(),
    llvm::ArrayRef<std::pair<std::string, std::string>> selections = {},
    bool linearContractions = false, mlir::Location *failureLocation = nullptr);
llvm::Expected<CheckedPhysicalPlan>
validatePhysical(mlir::ModuleOp, const PhysicalPlan &,
                 const CandidateCatalog & = installedCandidates(),
                 mlir::Location *failureLocation = nullptr);
/// Original root preorder, also used after freshness checking by
/// materialization.
llvm::SmallVector<mlir::Operation *> physicalPlanOperations(mlir::ModuleOp);
} // namespace zkc::target
#endif
