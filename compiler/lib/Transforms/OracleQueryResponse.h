#ifndef ZKC_TRANSFORMS_ORACLEQUERYRESPONSE_H
#define ZKC_TRANSFORMS_ORACLEQUERYRESPONSE_H
#include "OracleQueryExchange.h"
namespace zkc::protocol {
// Ordinary private data, with one logical answer payload per exact base
// constructor. The nominal identity grants no authority, linearity or proof.
struct OracleQueryResponse {
  mlir::Type answer;
  mlir::func::FuncOp authenticate, resume;
};
// Producer-only construction in an owned candidate; discard partial output on
// failure. authenticate(request, response, receiver stores...) returns answer
// without resuming. resume(request, answer, evaluator state...) returns state
// using the actual state's continuation coordinates. Both borrow the ordinary
// scope and return outcomes, preserving native failure propagation.
//
// The enclosing caller must independently check the supplied exchange model,
// controller, lookup and Merkle helpers and bind the actual immutable stores.
// Every logical occurrence authenticates independently, including physically
// shared responses. The window checker owns root-occurrence identity, ordered
// request/answer pairing across sequences, authentication of the entire prefix
// before replay, and source answer release. These helpers cannot establish
// those obligations or standalone source realization.
llvm::Expected<OracleQueryResponse>
emitOracleQueryResponse(mlir::ModuleOp candidate, const OracleQueryExchange &,
                        OracleVirtualFunctionWork &sharedBudget);
class OracleVerificationContext;
// Reads actual bodies through the admitted closure, independently of emission.
// The immutable context must be reacquired after every mutation; fresh parsed
// modules require rebinding all model and result functions to that module.
llvm::Error checkOracleQueryResponse(const OracleVerificationContext &,
                                     const OracleQueryExchange &,
                                     const OracleQueryResponse &);
} // namespace zkc::protocol
#endif
