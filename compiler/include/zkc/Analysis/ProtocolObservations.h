#ifndef ZKC_ANALYSIS_PROTOCOL_OBSERVATIONS_H
#define ZKC_ANALYSIS_PROTOCOL_OBSERVATIONS_H

#include "zkc/Analysis/ExecutionObservations.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include <optional>
#include <vector>

namespace zkc {
/// Exact forwarding, deliberately separate from dependence. A query path is
/// actual call operations followed by its query; it denotes an occurrence in
/// this definition, not all invocations of a shared callee or loop body.
struct ProtocolValueOrigin {
  enum class Kind { Unknown, Formal, Query };
  Kind kind = Kind::Unknown;
  unsigned port = 0;
  llvm::SmallVector<mlir::Operation *> path;
  bool operator==(const ProtocolValueOrigin &other) const {
    return kind == other.kind && port == other.port && path == other.path;
  }
  bool operator!=(const ProtocolValueOrigin &other) const {
    return !(*this == other);
  }
};

struct ProtocolPendingTransfer {
  enum class Input { Any, Empty, Formal };
  enum class Output { Preserved, Empty, Query };
  Input input = Input::Any;
  unsigned port = 0;
  Output output = Output::Preserved;
  ProtocolValueOrigin query;
};

struct ProtocolObservationSummary;
struct ProtocolObservationAction {
  mlir::Operation *operation = nullptr;
  /// Actual shared definition or retained repeat-body transfer. Never an
  /// expanded copy. Numerical summaries borrow this analysis's lifetime too.
  const ProtocolObservationSummary *callee = nullptr;
  const ExecutionObservationSummary *numerical = nullptr;
  /// Dependencies in the containing summary's atom basis. An empty-width
  /// vector means unavailable at the observer, not a constant value.
  llvm::SmallVector<llvm::BitVector> inputs, results;
  llvm::SmallVector<ProtocolValueOrigin> inputOrigins;
  llvm::BitVector stops;
  bool mayStop = false;
  /// Query authority must be an exact formal service, through actual aliases.
  std::optional<unsigned> service;
  /// Exact value at an outgoing delivery. May name an incoming formal whose
  /// challenge identity is supplied by the caller's pending transfer.
  ProtocolValueOrigin delivered;
  /// Independently selected deterministic transport, not a challenge delivery.
  bool dataExchange = false;
};

struct ProtocolObservationAtom {
  enum class Kind {
    Formal,
    Query,
    Receive,
    CallResult,
    CallStop,
    RepeatResult,
    RepeatStop
  };
  Kind kind;
  mlir::Operation *operation = nullptr;
  unsigned port = 0;
};

/// One observer's symbolic transfer over a definition or a retained repeat
/// body. Dependency atoms for calls/repeats refer to the actual child result
/// or stop transfer, not an unconstrained message or independent randomness.
struct ProtocolObservationSummary {
  protocol_ir::MathematicalOp declaration;
  mlir::Block *block = nullptr;
  std::string observer;
  unsigned formals = 0, depth = 1, queryFamilies = 0;
  llvm::SmallVector<ProtocolObservationAtom> atoms;
  std::vector<ProtocolObservationAction> actions;
  llvm::SmallVector<llvm::BitVector> results;
  llvm::SmallVector<ProtocolValueOrigin> resultOrigins;
  llvm::BitVector stops, services;
  bool mayStop = false;
  ProtocolPendingTransfer pending;
};

/// Module-owned analysis of admitted, immutable Protocol IR. Uses the actual
/// interaction structure and numerical observation owner. No preparation,
/// inlining, provider selection or serialized report grants premises here.
/// The closed profile refuses unknown verifier effects and pending transfers
/// without an invariant across every repeat count, including zero.
///
/// Clear BEFORE changing bodies, symbols, roles, types, bindings or policies.
/// All borrowed pointers expire at clear/invalidation/destruction. The module
/// must outlive this analysis. Work is cumulative and caller-owned; query
/// failure is sticky until clear. Source and candidate need separate owners.
class ProtocolObservationAnalysis {
public:
  explicit ProtocolObservationAnalysis(mlir::Operation *module);
  /// A consumer may select exact data exchanges from its independently checked
  /// realization edge. This is a conditional analysis input, not authority
  /// inferred from names/attributes or an untrusted report. Selected sends
  /// require Empty pending state and observed data. clear() drops selections.
  ProtocolObservationAnalysis(mlir::Operation *module,
                              llvm::ArrayRef<mlir::Operation *> dataExchanges);
  ProtocolObservationAnalysis(mlir::Operation *module, mlir::AnalysisManager &);
  ~ProtocolObservationAnalysis();
  ProtocolObservationAnalysis(const ProtocolObservationAnalysis &) = delete;
  ProtocolObservationAnalysis &
  operator=(const ProtocolObservationAnalysis &) = delete;
  bool isInvalidated(const mlir::AnalysisManager::PreservedAnalyses &);
  void clear();
  mlir::Operation *getOwner() const;
  llvm::Expected<const ProtocolObservationSummary *>
  get(protocol_ir::MathematicalOp, llvm::StringRef observer, facts::Work &);

private:
  struct Impl;
  std::unique_ptr<Impl> impl_;
};
} // namespace zkc
#endif
