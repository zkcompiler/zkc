#ifndef ZKC_TRANSFORMS_ORACLEQUERYCONTROLLER_H
#define ZKC_TRANSFORMS_ORACLEQUERYCONTROLLER_H
#include "OracleAnchorStorage.h"
#include "OracleQueryCapacity.h"
#include "OracleVirtualFunctions.h"
namespace zkc::protocol {
// Available anchors serve ordinary queries. Holder access excludes unrelated
// received commitments, even when the same party participates in both roles.
enum class OracleControllerAccess { Available, Holder };
struct OracleQueryContinuation {
  unsigned constructor, query;
  mlir::Type record, sequence;
  // Kind indices derived from the preceding source queries. The record stores
  // one index into each corresponding typed answer arena, never an answer copy.
  std::vector<unsigned> previousKinds;
};
struct OracleQueryControllerConstructor {
  unsigned source, role, kind, firstContinuation;
  mlir::func::FuncOp lookup;
  OracleVirtualFunctions functions;
};
struct OracleQueryController {
  // All state is ordinary SSA data. Stores are immutable captures; frame
  // arenas and append-only typed answers are carried across suspension.
  enum StateField : unsigned {
    Constructor,
    Instance,
    Position,
    Continuation,
    ContinuationInstance,
    Kind,
    Phase,
    AnswerIndex,
    HeaderSize
  };
  enum PhaseValue : unsigned { Enter, Return, Request, Completed };
  std::string role;
  OracleControllerAccess access = OracleControllerAccess::Available;
  OracleQuerySize capacity;
  std::vector<protocol_ir::OracleKindAttr> kinds;
  std::vector<mlir::Type> answers, state, stores;
  std::vector<OracleQueryControllerConstructor> constructors;
  std::vector<OracleQueryContinuation> continuations;
  // Per-kind lookup of the stored structural leaf count. These helpers read
  // references and metadata only, never positions, domains or table contents.
  std::vector<mlir::func::FuncOp> leafCounts;
  // Actual immutable table dimensions, selected by the dynamic reference.
  std::vector<mlir::func::FuncOp> rowCounts;
  // Per-constructor recurrence: all declared child references, then stores,
  // return one for a base or the ordered sum of virtual query child counts.
  // The complete stage binds this value to the same anchor allocation.
  std::vector<mlir::func::FuncOp> constructionCounts;
  mlir::func::FuncOp initialize, advance, finish;
  // Each resume consumes state, its five request/continuation coordinates,
  // and the answer of this kind. Actual-body checking must also bind the call
  // to the reached exchange; this ordinary value is not a linear capability.
  std::vector<mlir::func::FuncOp> resume;
  // Present only when this role has every base table's data. Uses the same
  // controller to evaluate leaves locally; never substitutes for Merkle work.
  mlir::func::FuncOp evaluate;
  // Holder-domain only: bases return stored data; virtuals evaluate rows when
  // contents are demanded, under the retained source admissibility obligation.
  mlir::func::FuncOp contents;
};
// Table-kind controller construction in an owned candidate. Every child kind
// must also be a table; other closed kinds need their own domain semantics.
// Producer-only construction in an owned candidate. The frozen prepared source
// supplies virtual definitions and the caller derives storage/capacity from its
// selected entry. Discard partial output on failure. No production publication
// is authorized by this producer; complete actual-body correspondence remains
// a separate boundary.
llvm::Expected<OracleQueryController> emitOracleQueryController(
    mlir::ModuleOp candidate, mlir::ModuleOp prepared,
    const OracleAnchorStorage &, llvm::StringRef role,
    protocol_ir::OracleKindAttr root, OracleQuerySize capacity,
    OracleVirtualFunctionWork &work,
    OracleControllerAccess access = OracleControllerAccess::Available);
// Read the actual scoped closure and compare all layouts, ordered transitions,
// pure maps, domain checks, suspensions and resumptions. The surrounding stage
// must independently derive storage/capacity and bind the root/call operands to
// their source occurrences. This primitive check is not full realization or a
// Lean simulation.
llvm::Error checkOracleQueryController(
    mlir::ModuleOp candidate, mlir::ModuleOp prepared,
    const OracleAnchorStorage &, llvm::StringRef role,
    protocol_ir::OracleKindAttr root, OracleQuerySize capacity,
    const OracleQueryController &actual,
    OracleControllerAccess access = OracleControllerAccess::Available);
} // namespace zkc::protocol
#endif
