#ifndef ZKC_COMPILER_PUBLIC_COIN_GRAPH_H
#define ZKC_COMPILER_PUBLIC_COIN_GRAPH_H
#include "zkc/Analysis/ProtocolObservations.h"
#include "llvm/Support/JSON.h"
namespace zkc::detail {
// Serialize borrowed summaries while their immutable analysis owner lives.
// Actual query/delivery selectors are checked in call contexts, with repeats
// represented as event families. The JSON does not grant new analysis facts.
llvm::Expected<llvm::json::Object> publicCoinGraph(
    mlir::ModuleOp, ProtocolObservationAnalysis &,
    const ProtocolObservationSummary &, facts::Work &,
    llvm::ArrayRef<std::pair<std::string, std::string>> selectedDraws);
} // namespace zkc::detail
#endif
