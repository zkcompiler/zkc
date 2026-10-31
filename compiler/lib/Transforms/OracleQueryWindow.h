#ifndef ZKC_TRANSFORMS_ORACLEQUERYWINDOW_H
#define ZKC_TRANSFORMS_ORACLEQUERYWINDOW_H
#include "OracleQueryDemand.h"
#include "OracleQueryResponse.h"
namespace zkc::protocol {
// Ordinary private scoped MLIR for one root. These sequences and helpers grant
// no proof authority and do not establish a complete dynamic window.
struct OracleQueryWindow {
  mlir::Type requestSequence, answerSequence;
  uint64_t capacity = 0;
  // collect(demand state..., requests, blocked:i1, immutable stores...)
  //   -> (demand state..., requests, blocked:i1).
  // replay(controller state..., requests, answers, begin:ui64, end:ui64,
  //        immutable stores...) -> controller state....
  // finish(controller state..., immutable stores...) -> controller.finish's
  // exact payload. Every function borrows scope and returns an outcome.
  mlir::func::FuncOp collect, replay, finish;
};
// capacity is a packet maximum, never a source semantic bound. This lowering
// uses capacity+1 native iterations and explicitly refuses capacity >=1048576.
// The caller initializes through the existing checked demand.initialize and
// controller.initialize, independently checks both models for the same actual
// root and binds the exact immutable stores. Kind numbers belong to that
// controller; numbers from another controller are not interchangeable.
// Failure removes partial additions and restores work before returning.
llvm::Expected<OracleQueryWindow>
emitOracleQueryWindow(mlir::ModuleOp candidate, const OracleQueryController &,
                      const OracleQueryDemand &, const OracleQueryExchange &,
                      const OracleQueryResponse &, uint64_t capacity,
                      OracleVirtualFunctionWork &);
// Read actual bodies under a freshly acquired immutable context; never replay
// the producer. The supplied demand/controller require independent source
// checks by the caller. Response bodies and their association with this
// controller are checked here. Rebind every helper after textual parsing.
//
// The enclosing complete window owns root occurrence ranges, global coverage,
// packet authentication of the ENTIRE valid prefix before ANY root replay,
// transport and rounds. A pending DomainCut only sets blocked. For an empty
// pending prefix (and for zero-total blocks), the caller invokes actual finish
// before any exchange to recover original source failure. All root finishes
// must succeed before the enclosing aggregator releases any root's answer.
llvm::Error checkOracleQueryWindow(const OracleVerificationContext &,
                                   const OracleQueryController &,
                                   const OracleQueryDemand &,
                                   const OracleQueryExchange &,
                                   const OracleQueryResponse &,
                                   const OracleQueryWindow &actual);
} // namespace zkc::protocol
#endif
