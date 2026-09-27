#ifndef ZKC_CONTRACTS_KERNELS_H
#define ZKC_CONTRACTS_KERNELS_H

#include "zkc/Contracts/Binding.h"
#include "zkc/Contracts/Operations.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/Error.h"

namespace zkc::protocol {
/// Installed contract shapes shared by binding resolution.
struct Kernel {
  llvm::StringRef key;
  std::vector<std::string> inputs;
  std::vector<std::string> outputs;
  OperationContracts contracts{};
};
llvm::ArrayRef<Kernel> kernels();
/// Formation of static operation attributes under an installed contract.
llvm::Error checkParameters(llvm::StringRef key, llvm::ArrayRef<std::string>,
                            llvm::StringRef field = {});
/// Attributes valid without choosing a field: field literals must be 0 or 1.
/// All ordinary arity and non-field attribute checks still apply.
llvm::Error checkGenericParameters(llvm::StringRef key,
                                   llvm::ArrayRef<std::string>);
/// Resolve the declared literal field from a closed operation application.
llvm::Error checkParameters(const BindingApplication &,
                            llvm::ArrayRef<std::string>);
/// Canonical modulus if installed; empty means no admitted constant domain.
llvm::StringRef fieldModulus(llvm::StringRef identity);
} // namespace zkc::protocol
#endif
