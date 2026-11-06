#ifndef ZKC_LIB_COMPILER_NATIVE_CONSTRUCTION_PREPARATION_H
#define ZKC_LIB_COMPILER_NATIVE_CONSTRUCTION_PREPARATION_H

#include "zkc/Compiler/NativeProof.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include <cstdint>
#include <memory>

namespace zkc::detail {
inline constexpr uint64_t constructionPreparationWorkLimit = 3000000;
struct NativeRequestPlan;
/// Static dependency reasons, not instructions or an executable schedule.
enum class ConstructionDependencyKind {
  Input,
  Source,
  Callback,
  Capture,
  Join,
  Iteration,
  Root,
  Start,
  Query,
  Omission,
  Replica,
  Realization,
  Encode,
  Receive,
  Range,
  RawObservation,
  Decode,
  Observation,
  RecordInitialization,
  Finalization,
  Completion
};
struct ConstructionDependency {
  ConstructionDependencyKind kind;
  mlir::Operation *source = nullptr;
  mlir::Value value;
  mlir::Block *block = nullptr;
  mlir::func::FuncOp callback;
  // Indices refer only to this live analysis. Every edge is in the SAME
  // relation, including ordered effects and codec/transcript successors.
  llvm::SmallVector<unsigned> predecessors;
  bool validator = false;
  bool conditional = false;
  // Edges constrain normal continuations only. A stopped row has no normal
  // successor; its reached effects remain in the inventory. Iteration rows
  // include a zero-trip boundary. Neither flag evaluates a Boolean payload.
  bool stopped = false;
  bool includesZeroTrip = false;
};

/// A move-only borrow of the ORIGINAL admitted Protocol module, its checked
/// execution closure. Both must remain alive and immutable through
/// preparation, materialization and independent checking. Plan and invocation
/// inputs are consumed during the call and are not retained in the result.
/// Mutating or destroying either owner invalidates the borrow. Cloning or
/// reparsing does not transfer it to the new module. No serialization API.
/// In particular, these dependencies are not a replacement for source/actual
/// candidate correspondence, common-control agreement or codec correctness.
class NativeConstructionPreparation {
public:
  NativeConstructionPreparation(NativeConstructionPreparation &&) noexcept;
  NativeConstructionPreparation &
  operator=(NativeConstructionPreparation &&) noexcept;
  ~NativeConstructionPreparation();
  llvm::ArrayRef<ConstructionDependency> dependencies() const;
  mlir::ModuleOp source() const;
  const protocol::SourceExecutionClosure &execution() const;
  uint64_t workUsed() const;
  bool complete() const;
  bool needsRealization() const;
  /// Discharge logical Oracle/store and polynomial recipe obligations using
  /// the actual candidate of the SAME independently checked RealizedProtocol
  /// owner. The caller keeps
  /// this immutable module and its actual execution closure alive as well as
  /// the original owners. This extends the relation under its remaining
  /// allowance; it cannot defer another logical operation or emit a proof.
  llvm::Error resolveRealization(
      mlir::ModuleOp realized, protocol_ir::MathematicalOp entry,
      const protocol::SourceExecutionClosure &execution,
      const NativeProofPolicy &policy,
      const protocol::ConstructionPlan *checkedPlan,
      llvm::ArrayRef<protocol::ConstructionInvocation> invocations);
  /// Second-stage prerequisite: requests is the successful actual-body plan
  /// for the ordinary projection produced by the SAME checked realization of
  /// source(). The caller retains that immutable projection through independent
  /// checking; the plan itself is consumed only during this call.
  /// Projection/source and realized occurrence associations must already be
  /// independently checked; site strings only address that checked association.
  /// No caller-supplied metadata grants this premise. Closes every original
  /// reverse request before any proof emission. Uses the remainder of this
  /// preparation's single allowance, never a fresh budget.
  llvm::Error dischargeRequests(const NativeRequestPlan &requests);

private:
  struct Storage;
  std::unique_ptr<Storage> storage;
  explicit NativeConstructionPreparation(std::unique_ptr<Storage>);
  friend llvm::Expected<NativeConstructionPreparation>
  prepareNativeConstruction(mlir::ModuleOp, protocol_ir::MathematicalOp,
                            const protocol::SourceExecutionClosure &,
                            const NativeProofPolicy &,
                            const protocol::ConstructionPlan *,
                            llvm::ArrayRef<protocol::ConstructionInvocation>,
                            uint64_t);
};

/// Read-only, before oracle realization or proof materialization. Admission,
/// resolveConstructionPlan and readSourceExecutionClosure on this EXACT module
/// are premises, not repeated here under an unaccounted second budget. The
/// closure is borrowed, never copied. All subsequent setup, source/symbol and
/// closure traversal, fresh environments, edges and output growth share this
/// allowance, capped at constructionPreparationWorkLimit. Exhausted analysis
/// returns no partial result.
///
/// Fixed ABI: receive(Record, proof)->(Record, ranges),
/// decode(chunks)->payload, wire(state, chunks)->state. Every opaque
/// result/effect retains ALL inputs. No dynamic state->receive ABI is inferred.
/// Repeats have one symbolic body boundary, including the zero-trip edge;
/// branches have fresh environments and all-arm dependency joins, never
/// equality from slot/type coincidence.
///
/// Scoped execution, nested selected mathematics and finite fold/collect are
/// read from their actual bodies/domain/callback owners. A source signature
/// alone never supplies callback dependencies. Reverse requests retain their
/// actual validator dependency and remain incomplete until dischargeRequests
/// consumes the independently checked ordinary-projection request relation.
/// Logical Oracle actions and poly.realize calls retain original SSA/control
/// obligations, including the actual polynomial recipe body and all call
/// inputs. PreparedProtocol's independent polynomial recipe checker and the
/// checked RealizedProtocol edge are required before resolveRealization reads
/// the actual store/callback/communication relation under the same allowance.
/// Original and realized owners remain alive together. Capacity exhaustion is
/// terminal across both discharge stages. No emission consumer may use an
/// incomplete result.
///
/// Named refusals use native-construction-preparation- followed by capacity,
/// source, closure, signature, dependency, order, group, coverage, recursion,
/// replica, or profile.
llvm::Expected<NativeConstructionPreparation> prepareNativeConstruction(
    mlir::ModuleOp admittedSource, protocol_ir::MathematicalOp entry,
    const protocol::SourceExecutionClosure &execution,
    const NativeProofPolicy &policy,
    const protocol::ConstructionPlan *checkedPlan = nullptr,
    llvm::ArrayRef<protocol::ConstructionInvocation> invocations = {},
    uint64_t workBudget = constructionPreparationWorkLimit);
} // namespace zkc::detail
#endif
