#ifndef ZKC_CONTRACTS_NUMERICAL_H
#define ZKC_CONTRACTS_NUMERICAL_H

#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/RingExpression.h"

namespace zkc::protocol {
/// These compiler-generated consumers own their positional signature. The
/// declaration's Field scope selects implementations; M is opaque to generic
/// static-term resolution, and is never a Nat or a nominal identity.
struct NumericalLimits {
  static constexpr size_t slots = 1023, bodyBytes = 4096;
  static constexpr uint64_t rows = 1048576;
};
bool numericalContract(llvm::StringRef contract);
llvm::Error checkNumericalArguments(const BindingApplication &binding);
llvm::Expected<BoundOperation>
resolveNumericalSignature(const BindingApplication &binding);
/// Independently admit the actual canonical body, including unused inputs and
/// every node. No producer digest or sharing receipt is accepted as evidence.
llvm::Expected<ring::Expression> readNumericalExpression(llvm::StringRef body,
                                                         llvm::StringRef field,
                                                         size_t slots);
llvm::Error checkNumericalParameters(const BindingApplication &binding,
                                     llvm::ArrayRef<std::string> parameters);
} // namespace zkc::protocol
#endif
