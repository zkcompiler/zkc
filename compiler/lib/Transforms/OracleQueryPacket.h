#ifndef ZKC_TRANSFORMS_ORACLEQUERYPACKET_H
#define ZKC_TRANSFORMS_ORACLEQUERYPACKET_H
#include "OracleQueryResponse.h"
namespace zkc::protocol {
// Private ordinary data, with no authority, security token or linearity.
// requestSequence is used for both logical occurrences and physical requests.
// groupsSequence retains one ui64 physical ordinal per logical occurrence.
struct OracleQueryPacket {
  mlir::Type requestSequence, responseSequence, answerSequence, groupsSequence;
  mlir::Type key, keySequence;
  mlir::func::FuncOp group, open, authenticate;
};
// All functions borrow a scope and return explicit outcomes:
// group(logical requests, receiver stores...) -> (physical requests, groups)
// open(physical requests, holder stores...) -> responses
// authenticate(logical requests, physical requests, groups, responses,
//              receiver stores...) -> answers
//
// Every request resolves through its exact receiver lookup and selected Merkle
// position helper. Keys are (source constructor, instance, physical leaf).
// First-use grouping preserves logical order and multiplicity. The bounded
// linear key search has quadratic worst-case runtime cost, metered by ordinary
// scoped execution. Compiler work accounts for emitted IR and retained slots.
// Each physical request opens once; each logical occurrence authenticates once
// against its own retained request. Nothing resumes an evaluator. Empty input
// is allowed; the enclosing window omits empty communication.
//
// The enclosing caller independently checks model, response, openOne,
// controllers, lookups and Merkle helpers. merkle is indexed by source
// constructor, not answer kind. capacity is positive and below the native
// range limit. Construction modifies only an owned disposable candidate;
// discard partial output on failure. Source is never modified by this API.
llvm::Expected<OracleQueryPacket> emitOracleQueryPacket(
    mlir::ModuleOp candidate, const OracleQueryExchange &model,
    const OracleQueryResponse &response, mlir::func::FuncOp openOne,
    llvm::ArrayRef<OracleMerkleFunctions> merkle, uint64_t capacity,
    OracleVirtualFunctionWork &sharedWork);
class OracleVerificationContext;
// Independent actual-body reader; reacquire context after every mutation and
// rebind every model/helper handle after parsing a fresh textual candidate.
// The caller binds source occurrences, immutable stores and actual collect /
// replay outputs, including both group outputs from the SAME call. This check
// does not certify an arbitrary caller-supplied mapping, source windows, proof
// security or full native FRI execution. Answers return only after the complete
// logical sequence authenticates; source answer release remains caller-owned.
llvm::Error checkOracleQueryPacket(const OracleVerificationContext &,
                                   const OracleQueryExchange &model,
                                   const OracleQueryResponse &response,
                                   mlir::func::FuncOp openOne,
                                   llvm::ArrayRef<OracleMerkleFunctions> merkle,
                                   uint64_t capacity,
                                   const OracleQueryPacket &actual);
} // namespace zkc::protocol
#endif
