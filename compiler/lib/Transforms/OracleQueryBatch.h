#ifndef ZKC_TRANSFORMS_ORACLEQUERYBATCH_H
#define ZKC_TRANSFORMS_ORACLEQUERYBATCH_H

#include "OracleQueryWindow.h"

namespace zkc::protocol {
struct OracleQueryBatchRoot {
  const OracleQueryController *controller;
  const OracleQueryDemand *demand;
  const OracleQueryWindow *window;
};

// Private ordinary helpers; neither these models nor their data grant
// authority. State vectors concatenate roots in exact source window order. Kind
// numbers and continuation coordinates remain local to each root's checked
// controller.
struct OracleQueryBatch {
  std::vector<mlir::Type> demandState, evaluatorState;
  mlir::Type requestSequence, answerSequence;
  // All signatures below borrow scope and return an explicit outcome. Shared
  // immutable stores occur once, in the checked controllers' common order.
  // collect(demandState..., stores...)
  //   -> (updated demandState..., requests, end0:ui64, ..., endN-1:ui64).
  // checkAvailable(requests, evaluatorState..., stores...) -> ().
  // replay(evaluatorState..., requests, answers, end0, ..., endN-1, stores...)
  //   -> updated evaluatorState....
  // finish(evaluatorState..., stores...) -> one exact logical answer per root.
  mlir::func::FuncOp collect, checkAvailable, replay, finish;
};

// roots has 1..32 entries in source window order. All windows have the same
// positive capacity (<1048576), sequence types and exact ordered store types.
// Aggregate scoped signatures must fit source execution's width limit of 512.
// The caller independently checks every controller/demand/window against its
// source occurrence and binds exact store identity; this primitive checks only
// their composition and does not reread each window's closure.
//
// Collection never takes evaluator state or evaluates answers. The caller must
// invoke checkAvailable immediately after collect, before grouping or exchange.
// It returns no data and has no effect for a nonempty request sequence.
// An empty prefix finishes every root
// on its ORIGINAL evaluator state, in source order, before
// control.require(false) diagnoses an impossible empty positive round. Any
// source failure propagates first. No empty packet is exchanged. CommonPlan
// owns positive structural rounds; zero-total blocks skip collect and invoke
// batch.finish once. Failure removes additions and restores the shared work
// allowance.
llvm::Expected<OracleQueryBatch>
emitOracleQueryBatch(mlir::ModuleOp candidate,
                     llvm::ArrayRef<OracleQueryBatchRoot> roots,
                     OracleVirtualFunctionWork &);

// Independent actual-body reader. Reacquire the immutable context after every
// mutation and rebind ALL helper handles after textual parsing. The caller
// checks the source models and windows once, binds source order and actual call
// operands, and authenticates the ENTIRE request/answer sequence before replay.
// replay neither authenticates nor finishes; finish releases answers only after
// all roots succeed. This check establishes no public realization authority.
llvm::Error checkOracleQueryBatch(const OracleVerificationContext &,
                                  llvm::ArrayRef<OracleQueryBatchRoot> roots,
                                  const OracleQueryBatch &actual);
} // namespace zkc::protocol
#endif
