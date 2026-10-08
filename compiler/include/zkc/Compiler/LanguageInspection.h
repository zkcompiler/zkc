#ifndef ZKC_COMPILER_LANGUAGEINSPECTION_H
#define ZKC_COMPILER_LANGUAGEINSPECTION_H
#include "zkc/Compiler/LanguageInterface.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
namespace zkc::language {
class CheckedOriginal;
struct AppliedSelector {
  unsigned role; // Index in the caller roster.
  llvm::SmallVector<mlir::Value> values;
};
struct AppliedClause {
  const InterfaceClause &definition;
  llvm::SmallVector<AppliedSelector> subject;
  std::optional<llvm::SmallVector<AppliedSelector>> residual;
  std::optional<AppliedSelector> decision;
};
/// A static application in the exact original. Path indices select operations
/// in the caller block, then each enclosing repeat block. Loops and transitive
/// calls are not expanded. The operation, values and all referenced storage are
/// borrowed for one visitor invocation and must not be mutated or retained.
struct ApplicationOccurrence {
  const LanguageInterface &interface;
  const InterfaceProtocol &caller, &callee;
  protocol_ir::ApplyOp operation;
  llvm::ArrayRef<unsigned> path, roles;
  llvm::ArrayRef<AppliedClause> clauses;
};
/// Admit the entire original/interface before invoking the visitor. Derive each
/// clause binding from actual application operands/results and its injective
/// role substitution; no application graph is supplied by metadata. This has
/// readInterface's structural guarantees, not source-authentication authority.
/// Return the first visitor error. Callback work is the caller's
/// responsibility.
llvm::Error inspectApplications(
    llvm::StringRef original, llvm::StringRef interface,
    llvm::function_ref<llvm::Error(const ApplicationOccurrence &)> visitor,
    const Limits & = {}, llvm::ArrayRef<RelationAsset> assets = {});
/// Inspect an immutable source-checked original, including its captured assets.
/// Reparse and structurally admit under the requested limits. Source authority
/// comes from the retained CheckedOriginal rather than caller-supplied
/// metadata.
llvm::Error inspectApplications(
    const CheckedOriginal &,
    llvm::function_ref<llvm::Error(const ApplicationOccurrence &)> visitor,
    const Limits & = {});
} // namespace zkc::language
#endif
