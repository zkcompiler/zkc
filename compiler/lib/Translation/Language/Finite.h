#ifndef ZKC_TRANSLATION_LANGUAGE_FINITE_H
#define ZKC_TRANSLATION_LANGUAGE_FINITE_H
#include "mlir/IR/Builders.h"
#include "zkc/Language/Layout.h"
#include <set>
namespace zkc::protocol::detail {
class ScopedExecutionBuilder;
}
namespace zkc::exec {
class ControlCursor;
}
namespace zkc::language {
class EmissionBudget;
/// Emit the closed source finite operation using private descriptor and ABI
/// adapters. The source helpers retain their ordinary flattened signatures.
/// An ordered caller supplies its persistent scoped constructor to emit actual
/// scoped Func callbacks and an exec.fold/collect occurrence. All insertions
/// use the caller's budget listener; publication requires a final budget check.
llvm::Expected<llvm::SmallVector<mlir::Value>>
emitFinite(const ClosedEntry &, const Body &, const FiniteComputation &,
           const Type &, llvm::ArrayRef<llvm::SmallVector<mlir::Value>>,
           mlir::OpBuilder &, mlir::Location, mlir::Block &definitions,
           Layouts &, llvm::StringRef prefix, llvm::StringRef site,
           EmissionBudget &, uint64_t &remaining,
           protocol::detail::ScopedExecutionBuilder *scoped = nullptr);
/// Read the supplied descriptor, adapters and occurrence relationally. This
/// checker never invokes the emitter or constructs an expected MLIR module.
/// Scoped callers supply an already-entered cursor over formed IR. Comparison
/// advances it past the finite occurrence and debits the operation/work counts
/// for its CFG and adapters. The enclosing checker owns ordinary helper bodies,
/// complete definition inventory and the rest of the caller's CFG.
llvm::Expected<llvm::SmallVector<mlir::Value>>
compareFinite(const ClosedEntry &, const Body &, const FiniteComputation &,
              const Type &, llvm::ArrayRef<llvm::SmallVector<mlir::Value>>,
              mlir::Block &, mlir::Block::iterator &,
              const std::map<std::string, mlir::Operation *> &definitions,
              std::set<mlir::Operation *> &used, Layouts &,
              llvm::StringRef prefix, llvm::StringRef site, const Limits &,
              uint64_t &operations, uint64_t &remaining,
              exec::ControlCursor *scoped = nullptr);
} // namespace zkc::language
#endif
