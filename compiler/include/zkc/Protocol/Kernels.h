#ifndef ZKC_PROTOCOL_KERNELS_H
#define ZKC_PROTOCOL_KERNELS_H

#include "mlir/IR/Types.h"
#include "zkc/Protocol/Contracts.h"
#include "zkc/Source/Model.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/Error.h"

namespace mlir {
class Operation;
}
namespace zkc::protocol {
/// Installed contract shapes shared by binding resolution.
struct Kernel {
  llvm::StringRef key;
  llvm::StringRef operation;
  std::vector<std::string> inputs;
  std::vector<std::string> outputs;
  OperationContracts contracts{};
};
llvm::ArrayRef<Kernel> kernels();
/// Formation of static operation attributes under an installed contract.
llvm::Error checkParameters(llvm::StringRef key, const source::Names &,
                            llvm::StringRef field = "bls12-381.fr");
/// Canonical modulus if installed; empty means no admitted constant domain.
llvm::StringRef fieldModulus(llvm::StringRef identity);
} // namespace zkc::protocol
#endif
