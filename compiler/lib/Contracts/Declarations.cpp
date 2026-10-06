#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"

namespace zkc::protocol {
#include "zkc/Contracts/Declarations.cpp.inc"
llvm::ArrayRef<generic::Operation> executableOperationContracts() {
  static const auto all = [] {
    std::vector<generic::Operation> result(boundOperationContracts().begin(),
                                           boundOperationContracts().end());
    result.insert(result.end(), nonGenericOperationContracts().begin(),
                  nonGenericOperationContracts().end());
    return result;
  }();
  return all;
}
} // namespace zkc::protocol
