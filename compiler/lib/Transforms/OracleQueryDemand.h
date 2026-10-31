#ifndef ZKC_TRANSFORMS_ORACLEQUERYDEMAND_H
#define ZKC_TRANSFORMS_ORACLEQUERYDEMAND_H
#include "OracleQueryController.h"
namespace zkc::protocol {
// One root's answer-free discovery state. Stores are immutable captures of
// advance, in the checked controller's order. The sole frame arena is append
// only; a continuation is zero for the root or a frame index plus one.
struct OracleQueryDemand {
  enum StateField : unsigned {
    Constructor,
    Instance,
    Position,
    Kind,
    Continuation,
    Phase,
    HeaderSize,
    Frames = HeaderSize
  };
  enum FrameField : unsigned {
    ParentConstructor,
    ParentInstance,
    ParentPosition,
    NextChild,
    ParentContinuation,
    FrameSize
  };
  enum PhaseValue : unsigned { Enter, Return, Request, DomainCut, Completed };
  mlir::Type frame, sequence;
  std::vector<mlir::Type> state;
  // initialize(reference, position); advance(state..., controller stores...);
  // consume(state...). Each helper takes a scope and returns an explicit
  // outcome. advance requires Enter/Return and stops at Request, DomainCut or
  // Completed. consume requires Request and only changes its phase to Return.
  mlir::func::FuncOp initialize, advance, consume;
};
// Reuse a checked controller already owned by candidate, including its exact
// kinds, constructor inventory, lookups, position maps, stores and capacity.
// This does not regenerate virtual functions or call an answer helper. Work
// is shared with the enclosing emission; discard candidate on any failure.
llvm::Expected<OracleQueryDemand>
emitOracleQueryDemand(mlir::ModuleOp candidate, const OracleAnchorStorage &,
                      const OracleQueryController &,
                      protocol_ir::OracleKindAttr root,
                      OracleVirtualFunctionWork &work);
// Independently read actual bodies and recheck the existing controller against
// prepared. The caller derives storage and capacity from source and binds the
// actual root occurrence and immutable stores. This is neither full window
// realization nor a runtime trace equivalence judgment.
class OracleVerificationContext;
llvm::Error checkOracleQueryDemand(const OracleVerificationContext &candidate,
                                   const OracleVerificationContext &prepared,
                                   const OracleAnchorStorage &,
                                   const OracleQueryController &,
                                   protocol_ir::OracleKindAttr root,
                                   const OracleQueryDemand &actual);
llvm::Error checkOracleQueryDemand(mlir::ModuleOp candidate,
                                   mlir::ModuleOp prepared,
                                   const OracleAnchorStorage &,
                                   const OracleQueryController &,
                                   protocol_ir::OracleKindAttr root,
                                   const OracleQueryDemand &actual);
} // namespace zkc::protocol
#endif
