#ifndef ZKC_LIB_COMPILER_NATIVE_REQUEST_H
#define ZKC_LIB_COMPILER_NATIVE_REQUEST_H

#include "mlir/IR/IRMapping.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include <cstdint>
#include <memory>
#include <optional>

namespace zkc::detail {
struct NativeTranscriptEvent;
// All references borrow the immutable ordinary projection. These are private
// source slots, never serialized claims. A replica reference cannot resolve in
// the ordinary environment, even when the types happen to agree.
struct NativeRequestValue {
  mlir::Value source;
  bool ordinary = false;
};
struct NativeRequestStep {
  mlir::Operation *source;
  llvm::SmallVector<NativeRequestValue> inputs;
};
struct NativeRequestFrame;
struct NativeRequestBranch {
  protocol_ir::ParticipantBranchOp producer, validator;
  NativeRequestFrame *parent = nullptr;
  llvm::SmallVector<std::unique_ptr<NativeRequestFrame>> arms;
  // Indices into validator inputs; zero is the selector, never a capture.
  llvm::SmallVector<unsigned> captures;
  llvm::SmallVector<NativeRequestValue> captured;
  // Exact validator result indices; each arm yields one value per output.
  llvm::SmallVector<unsigned> outputs;
  llvm::SmallVector<llvm::SmallVector<NativeRequestValue>> yielded;
  // Only completed all-arm judgments are cached. Positions are role-local.
  llvm::DenseMap<std::pair<mlir::Value, mlir::Value>, bool> joins;
};
struct NativeRequestLoop {
  protocol_ir::ProtocolLoopOp producer, validator;
  NativeRequestFrame *parent = nullptr;
  std::unique_ptr<NativeRequestFrame> body;
  llvm::SmallVector<unsigned> carried, captures;
  llvm::SmallVector<NativeRequestValue> initial, captured, yielded;
  // Present only after the checked source recurrence proves count equality.
  // The ordinary P count computation remains in place, including its stops.
  std::optional<NativeRequestValue> count;
};
struct NativeRequestFrame {
  mlir::Block *producer = nullptr, *validator = nullptr;
  // Mutually exclusive immediate ancestry; the root has neither.
  NativeRequestLoop *loop = nullptr;
  NativeRequestBranch *branch = nullptr;
  unsigned arm = 0;
  llvm::DenseMap<mlir::Operation *, llvm::SmallVector<NativeRequestStep>>
      before;
  llvm::DenseMap<mlir::Operation *, mlir::Operation *> definitions;
  // Count obligations may discover replica state. Visit them in source order,
  // independent of operation allocation addresses and hash iteration order.
  llvm::MapVector<mlir::Operation *, std::unique_ptr<NativeRequestLoop>> loops;
  llvm::MapVector<mlir::Operation *, std::unique_ptr<NativeRequestBranch>>
      branches;
  llvm::DenseMap<mlir::Value, NativeRequestValue> relations;
  llvm::DenseMap<mlir::Operation *, NativeRequestValue> requests;
  // Exact frontier at control entry; later sends never justify captures.
  llvm::DenseMap<mlir::Value, NativeRequestValue> entryRelations;
  bool finished = false;
};
struct NativeRequestPlan {
  std::unique_ptr<NativeRequestFrame> root;
  protocol_ir::ParticipantOp producer, validator;
  llvm::DenseMap<mlir::Block *, NativeRequestFrame *> frames;
};
struct NativeRequestCountPair {
  mlir::Value producer, validator;
  bool operator==(const NativeRequestCountPair &other) const {
    return producer == other.producer && validator == other.validator;
  }
};
// Recover only structural request-loop count equalities. The checked owner is
// mandatory. Recheck its actual common body against its prepared logical
// source, associate the supplied ordinary projection with the checked side, and
// bind the two actual round-count operands through the source query block. The
// inherited law is base-one / ordered virtual children sum / guarded ceil;
// neither record equality nor capture/shape equality is a premise.
llvm::Expected<llvm::SmallVector<NativeRequestCountPair>>
readNativeRequestCounts(const mathematical::RealizedProtocol &,
                        protocol_ir::ProtocolModuleOp projected,
                        const NativeProofPolicy &);
llvm::Expected<NativeRequestPlan>
planNativeRequests(protocol_ir::ProtocolModuleOp projected,
                   const NativeProofPolicy &,
                   llvm::ArrayRef<NativeTranscriptEvent>,
                   const mathematical::RealizedProtocol *realization = nullptr);

struct NativeRequestAction {
  std::string anchor;
  protocol_ir::LocalCallOp call;
};
struct NativeRequestEmission {
  llvm::SmallVector<NativeRequestAction> actions;
  llvm::DenseMap<mlir::Operation *, mlir::Value> requests;
};
// Emit into an exact mutable copy of plan's ordinary projection. The caller
// owns fresh sites and adds returned calls to construction action metadata.
llvm::Expected<NativeRequestEmission>
emitNativeRequests(const NativeRequestPlan &,
                   protocol_ir::ProtocolModuleOp candidate,
                   llvm::function_ref<std::string()> fresh);

using NativeRequestValues = llvm::DenseMap<mlir::Value, mlir::Value>;
mlir::Value resolveNativeRequestValue(NativeRequestValue,
                                      const NativeRequestValues &ordinary,
                                      const NativeRequestValues &replica);
// Read actual inserted operations. This function never emits or normalizes a
// candidate. Every planned step is consumed once at its actual source frontier.
// The allowance covers nested actual regions, bindings and result-map growth;
// nested selections use fresh arm environments and a maximum depth of 64.
// The caller owns this cumulative allowance across all frontiers and regions.
bool readNativeRequestSteps(const NativeRequestFrame &, mlir::Operation *anchor,
                            mlir::Operation *&cursor,
                            const NativeRequestValues &ordinary,
                            NativeRequestValues &replica, uint64_t &allowance);
bool readNativeRequestLoopInputs(const NativeRequestLoop &,
                                 protocol_ir::ProtocolLoopOp actual,
                                 unsigned stateSlots,
                                 const NativeRequestValues &ordinary,
                                 const NativeRequestValues &replica);
bool bindNativeRequestLoop(const NativeRequestLoop &,
                           protocol_ir::ProtocolLoopOp actual,
                           unsigned stateSlots, NativeRequestValues &replica);
bool readNativeRequestYield(const NativeRequestLoop &, mlir::ValueRange actual,
                            const NativeRequestValues &ordinary,
                            const NativeRequestValues &replica);
// Branch layout: selector, original captures, replica captures, caller-owned
// extra captures; original results, replica outputs, caller-owned extra
// outputs. The caller independently checks the extra state/coordinate/record
// slots. Use fresh ordinary/replica environments for each arm. Bind outputs
// only after every arm's actual operations and yield have been read
// successfully.
bool readNativeRequestBranchInputs(const NativeRequestBranch &,
                                   protocol_ir::ParticipantBranchOp actual,
                                   unsigned extraCaptures,
                                   unsigned extraOutputs,
                                   const NativeRequestValues &ordinary,
                                   const NativeRequestValues &replica);
bool bindNativeRequestBranchArm(const NativeRequestBranch &,
                                protocol_ir::ParticipantBranchOp actual,
                                unsigned arm, unsigned extraCaptures,
                                unsigned extraOutputs,
                                NativeRequestValues &ordinary,
                                NativeRequestValues &replica);
bool readNativeRequestBranchYield(const NativeRequestBranch &, unsigned arm,
                                  mlir::ValueRange actual,
                                  unsigned extraOutputs,
                                  const NativeRequestValues &ordinary,
                                  const NativeRequestValues &replica);
bool bindNativeRequestBranchOutputs(const NativeRequestBranch &,
                                    protocol_ir::ParticipantBranchOp actual,
                                    unsigned extraOutputs,
                                    NativeRequestValues &ordinary,
                                    NativeRequestValues &replica);
} // namespace zkc::detail
#endif
