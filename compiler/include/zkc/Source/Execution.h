#ifndef ZKC_SOURCE_EXECUTION_H
#define ZKC_SOURCE_EXECUTION_H

#include "zkc/Source/Model.h"
#include "llvm/Support/Error.h"
#include <map>

namespace zkc::source {

struct ExecutionValue {
  std::string type, origin, name, role;
};
struct ExecutionInvocation {
  std::string callee, instance;
  Names inputs, outputs;
};
struct ExecutionGuard {
  std::string value, role;
};
struct ExecutionOperation {
  std::string callee;
  Names inputs, outputs;
  /// Local owner, or sender for a message. receiver is nonempty for messages.
  std::string role, receiver;
  Names attributes;
  /// Ordinal in actual bounded expansion order, not lexical path order.
  size_t ordinal = 0;
};

/// Bounded structural execution view of admitted common source. Values are SSA
/// occurrences; a received value is distinct from the value sent by its peer.
/// Operations are not evaluated and no honest-message equality, randomness
/// independence, cryptographic law or reachability of success is assumed.
/// Lexical maps support stable lookup; order preserves actual operation order.
struct Execution {
  Names roles, order, results;
  std::map<std::string, ExecutionValue> values;
  std::map<std::string, ExecutionInvocation> invocations;
  std::map<std::string, ExecutionGuard> guards;
  std::map<std::string, uint64_t> loops;
  std::map<std::string, ExecutionOperation> operations;
};

/// Admit and instantiate before expanding calls and finite loop instances.
/// Unsupported control structures and excessive expansion fail closed.
llvm::Expected<Execution> inspectExecution(const Module &,
                                           llvm::StringRef entry);

} // namespace zkc::source
#endif
