#ifndef ZKC_TRANSLATION_LANGUAGE_FINITE_H
#define ZKC_TRANSLATION_LANGUAGE_FINITE_H
#include "mlir/IR/Builders.h"
#include "zkc/Language/Layout.h"
#include <set>
namespace zkc::language {
/// Emit the closed source finite operation using private descriptor and ABI
/// adapters. The source helpers retain their ordinary flattened signatures.
llvm::Expected<llvm::SmallVector<mlir::Value>>
emitFinite(const ClosedEntry &, const Body &, const FiniteComputation &,
           const Type &, llvm::ArrayRef<llvm::SmallVector<mlir::Value>>,
           mlir::OpBuilder &, mlir::Location, mlir::Block &definitions,
           Layouts &, llvm::StringRef prefix, llvm::StringRef site,
           const Limits &, uint64_t &operations, uint64_t &remaining);
/// Read the supplied descriptor, adapters and occurrence relationally. This
/// checker never invokes the emitter or constructs an expected MLIR module.
llvm::Expected<llvm::SmallVector<mlir::Value>>
compareFinite(const ClosedEntry &, const Body &, const FiniteComputation &,
              const Type &, llvm::ArrayRef<llvm::SmallVector<mlir::Value>>,
              mlir::Block &, mlir::Block::iterator &,
              const std::map<std::string, mlir::Operation *> &definitions,
              std::set<mlir::Operation *> &used, Layouts &,
              llvm::StringRef prefix, llvm::StringRef site, const Limits &,
              uint64_t &operations, uint64_t &remaining);
} // namespace zkc::language
#endif
