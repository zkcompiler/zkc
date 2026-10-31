#ifndef ZKC_ANALYSIS_INTERACTIONS_H
#define ZKC_ANALYSIS_INTERACTIONS_H

#include "mlir/IR/Operation.h"
#include "mlir/Pass/AnalysisManager.h"
#include "zkc/Contracts/MathematicalFacts.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"
#include <memory>
#include <optional>
#include <vector>

namespace zkc {
class InteractionAnalysis;

/// One actual source operation. Paths are operation ordinals from the selected
/// declaration body, descending ONLY through owned Protocol repeats. A path is
/// neither an invocation identity nor evidence that an action was reached.
class InteractionAction {
public:
  mlir::Operation *getOperation() const { return operation_; }
  mlir::Operation *getDeclaration() const { return declaration_; }
  mlir::Block *getBlock() const { return operation_->getBlock(); }
  mlir::OperandRange getInputs() const { return operation_->getOperands(); }
  mlir::ResultRange getOutputs() const { return operation_->getResults(); }
  llvm::ArrayRef<unsigned> getPath() const { return path_; }
  /// Actual Protocol application, virtual-definition, local-call or math
  /// target, distinct from the containing owner. Other symbol uses stay on the
  /// op. The target body is not expanded or interpreted by this view.
  mlir::Operation *getReferencedSymbol() const { return referencedSymbol_; }
  std::optional<unsigned> getRepeatBody() const { return repeatBody_; }

private:
  friend class InteractionAnalysis;
  mlir::Operation *operation_ = nullptr, *declaration_ = nullptr;
  mlir::Operation *referencedSymbol_ = nullptr;
  llvm::SmallVector<unsigned> path_;
  std::optional<unsigned> repeatBody_;
};

class InteractionSequence {
public:
  mlir::Block *getBlock() const { return block_; }
  /// Indices into the declaration's actions, in source order in this block.
  llvm::ArrayRef<unsigned> getActions() const { return actions_; }

private:
  friend class InteractionAnalysis;
  mlir::Block *block_ = nullptr;
  llvm::SmallVector<unsigned> actions_;
};

class InteractionDeclaration {
public:
  InteractionDeclaration(const InteractionDeclaration &) = delete;
  InteractionDeclaration &operator=(const InteractionDeclaration &) = delete;
  mlir::Operation *getDeclaration() const { return declaration_; }
  /// Lexical preorder, including repeat operations and their retained bodies.
  /// This storage order does not prescribe a consumer's query order.
  llvm::ArrayRef<InteractionAction> getActions() const { return actions_; }
  const InteractionSequence &getBody() const { return sequences_.front(); }
  const InteractionSequence &getSequence(unsigned index) const {
    return sequences_[index];
  }
  /// Missing paths return nullptr. Every attempted component debits Work;
  /// exhausted work returns interaction-analysis-capacity, never absence.
  llvm::Expected<const InteractionAction *>
  lookup(llvm::ArrayRef<unsigned> path, facts::Work &) const;

private:
  friend class InteractionAnalysis;
  InteractionDeclaration() = default;
  mlir::Operation *declaration_ = nullptr;
  std::vector<InteractionAction> actions_;
  std::vector<InteractionSequence> sequences_;
  uint64_t extractionWork_ = 0;
};

/// Module-owned borrowed structure of actual admitted Protocol functions and
/// virtual oracle definitions. Admission
/// (including unused declarations) is a prerequisite supplied by the caller;
/// this view supplies no admission, reachability or semantic approval result.
/// Only Protocol repetition introduces sequences. Pure mathematical regions
/// remain opaque actions; local Exec control belongs to its existing readers.
///
/// Construct on the containing builtin ModuleOp, never a callable or a set of
/// referenced symbols. Subject, helper, role, layout, installation or policy
/// mutation requires clear() BEFORE mutation or reconstruction. All returned
/// pointers/references expire at clear(), invalidation or destruction; the IR
/// and owner must outlive them. The containing owner itself cannot be replaced.
/// No internal allowance exists: each extraction (including hits) replays the
/// same unit debits against caller-owned cumulative Work. Failures are not
/// cached. Consumers debit their own transfers/iteration over the const views;
/// lookup() debits path navigation. Source and candidate modules require
/// distinct analyses. This analysis and its borrowed views are not thread-safe.
class InteractionAnalysis {
public:
  struct Limits {
    /// Callers may tighten these Protocol limits; larger values are clamped.
    unsigned depth = 64;
    unsigned actions = 100000;
  };
  explicit InteractionAnalysis(mlir::Operation *owner);
  InteractionAnalysis(mlir::Operation *owner, Limits);
  InteractionAnalysis(mlir::Operation *owner, mlir::AnalysisManager &);
  ~InteractionAnalysis();
  InteractionAnalysis(const InteractionAnalysis &) = delete;
  InteractionAnalysis &operator=(const InteractionAnalysis &) = delete;
  bool isInvalidated(const mlir::AnalysisManager::PreservedAnalyses &);
  void clear();
  mlir::Operation *getOwner() const;
  /// Refusals: interaction-analysis-owner for a foreign/non-module owner;
  /// interaction-analysis-unsupported for a profile/structure outside this
  /// slice; interaction-analysis-capacity for sticky work/depth/size limits.
  llvm::Expected<const InteractionDeclaration *>
  get(mlir::Operation *declaration, facts::Work &);

private:
  struct Impl;
  std::unique_ptr<Impl> impl_;
};
} // namespace zkc
#endif
