#ifndef ZKC_TEST_SUPPORT_CONTRACT_WITNESSES_H
#define ZKC_TEST_SUPPORT_CONTRACT_WITNESSES_H
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "llvm/ADT/STLExtras.h"
namespace zkc::test {
/// Generic checker witnesses exercise fixed signatures without complete-Type
/// ports. Construction-only Type ports and numerical families have their own
/// admission tests. This is a test selection, not a second production catalog.
inline llvm::ArrayRef<generic::Operation> genericWitnessOperations() {
  static const auto selected = [] {
    std::vector<generic::Operation> result;
    for (const auto &operation : protocol::executableOperationContracts()) {
      if (operation.numerical ||
          protocol::authoringStage(operation.name) ==
              protocol::AuthoringStage::CompilerGenerated ||
          protocol::authoringStage(operation.name) ==
              protocol::AuthoringStage::Physical)
        continue;
      auto complete = [](const auto &type) { return type.term.has_value(); };
      if (llvm::any_of(operation.signature.inputs, complete) ||
          llvm::any_of(operation.signature.outputs, complete))
        continue;
      result.push_back(operation);
    }
    return result;
  }();
  return selected;
}
} // namespace zkc::test
#endif
