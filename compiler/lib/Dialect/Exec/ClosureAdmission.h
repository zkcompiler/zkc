#ifndef ZKC_DIALECT_EXEC_CLOSURE_ADMISSION_H
#define ZKC_DIALECT_EXEC_CLOSURE_ADMISSION_H
#include "zkc/Dialect/Exec/Execution.h"
namespace zkc::protocol::detail {
/// Check data uses and the complete call/control graph after structural CFG,
/// operation and symbol verification. Scope ownership is a separate premise.
/// The borrowed association must describe the current immutable owner. No
/// serialized Program, synthetic callable or encoded type participates.
llvm::Error verifyClosureUses(mlir::Operation *owner,
                              const SourceExecutionClosure &closure,
                              bool physical, uint64_t &remaining);
} // namespace zkc::protocol::detail
#endif
