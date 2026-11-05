#ifndef ZKC_COMPILER_CONSTRUCTIONBINDING_H
#define ZKC_COMPILER_CONSTRUCTIONBINDING_H
#include "NativeProofVerification.h"
namespace zkc::detail {
/// Private, transient fact over an admitted immutable prepared function. The
/// caller retains its owner for the whole call. Indices refer to actual events
/// in static source order; starts and selected draw deliveries are not
/// messages.
struct ConstructionTerminalSummary {
  llvm::SmallVector<unsigned> pending;
  bool selectedControl = false;
};
/// Requires source formation and independently admitted events/draw pairs.
/// Checks their complete site/kind association, including starts. Unselected
/// service queries are not transcript events. Work includes input/index costs,
/// traversal, copies and joins; the caller can lower, but never raise, 100,000.
/// Repeats are read once; no path or runtime occurrence expansion is performed.
llvm::Expected<ConstructionTerminalSummary> summarizeConstructionTerminal(
    protocol_ir::MathematicalOp preparedSource,
    llvm::ArrayRef<NativeTranscriptEvent> events,
    llvm::ArrayRef<std::pair<std::string, std::string>> draws,
    uint64_t workBudget = 100000);
/// Requires independently checked candidate/source transcript correspondence.
/// This adds actual canonical-encoding/state coverage, never execution
/// admission. The prepared source owner must outlive this call.
llvm::Expected<llvm::json::Value> analyzeConstructionBinding(
    mlir::ModuleOp candidate, protocol_ir::MathematicalOp preparedSource,
    llvm::ArrayRef<mlir::Type> sourceInputs, const NativeProofPolicy &,
    NativeProofBindingProfile, llvm::ArrayRef<NativeTranscriptEvent>,
    const protocol::ConstructionPlan *);
} // namespace zkc::detail
#endif
