#ifndef ZKC_DIALECT_ADMISSION_PRIVATE_H
#define ZKC_DIALECT_ADMISSION_PRIVATE_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Analysis/CommonControl.h"
#include <utility>

namespace zkc::protocol {
class OracleVerificationContext;
struct SourceExecutionClosure;
} // namespace zkc::protocol
namespace zkc::detail {
// Scratch observations from the independent reader. These are not equations
// until the entire paired comparison, including helper inventory, succeeds.
struct OracleRepeatCount {
  mlir::ModuleOp source, candidate;
  protocol_ir::MathematicalOp originalEntry, actualEntry;
  protocol_ir::RepeatOp repeat;
  protocol_ir::AssembleRolesOp assembly;
  llvm::SmallVector<mlir::Value> counts;
  llvm::SmallVector<mlir::Operation *> queries, leafCalls;
  llvm::SmallVector<unsigned> sourcePath;
  // Exact lexical control/arm identity. Preparation expands applications before
  // this reader; the complete original and actual entry remain associated.
  llvm::SmallVector<std::pair<mlir::Operation *, unsigned>> ancestry;
  llvm::SmallVector<mlir::Value> iterations;
  uint64_t capacity = 0, maximum = 0;
  unsigned authentication = 0;
};

// No public constructor, mutable registry or persistent equality map. The only
// constructor belongs to the immutable paired context's final completion.
class OracleCountEquations {
  friend class protocol::OracleVerificationContext;
  protocol_ir::ProtocolModuleOp original;
  llvm::ArrayRef<OracleRepeatCount> observations;
  OracleCountEquations(protocol_ir::ProtocolModuleOp original,
                       llvm::ArrayRef<OracleRepeatCount> observations)
      : original(original), observations(observations) {}

public:
  protocol_ir::ProtocolModuleOp getOriginal() const { return original; }
  llvm::ArrayRef<OracleRepeatCount> getObservations() const {
    return observations;
  }
};

// Internal phase, never represented or returned as stage admission. All other
// public paths compose this with ordinary common-control completion.
// Optional output retains the closure actually validated by structure checking
// for the single outer Protocol unit. It grants no admission/count authority.
mlir::LogicalResult
verifyStageStructure(mlir::Operation *,
                     protocol::SourceExecutionClosure * = nullptr);
// Complete ordinary admission with the caller's cumulative common-control
// allowance. This still verifies the complete source structure and supplies no
// paired count equations or candidate-admission authority. Structural traversal
// reservations belong to the caller; derivation charges this Work as it runs.
mlir::LogicalResult
admitStageWithWork(mlir::Operation *, facts::Work &,
                   protocol::SourceExecutionClosure * = nullptr);
mlir::LogicalResult
verifyMathematicalStructure(protocol_ir::ProtocolModuleOp,
                            protocol::SourceExecutionClosure * = nullptr);
llvm::Expected<llvm::SmallVector<CommonControlRequirement>>
completeCommonControl(protocol_ir::ProtocolModuleOp, facts::Work &,
                      const OracleCountEquations * = nullptr);
llvm::Expected<llvm::SmallVector<CommonControlRequirement>>
deriveCommonControlRequirements(protocol_ir::MathematicalOp, facts::Work &,
                                const OracleCountEquations &,
                                bool fullRequirements);
} // namespace zkc::detail
#endif
