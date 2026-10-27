#ifndef ZKC_TEST_COMPUTATIONFIXTURE_H
#define ZKC_TEST_COMPUTATIONFIXTURE_H

#include "NativeCases.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Exec/Execution.h"
#include <memory>

namespace zkc::test {
// Keep this owner alive while inspecting a derived computation view. The
// admitted association borrows the source module, which must remain unchanged.
struct OwnedComputation : finite::Computation {
  std::shared_ptr<protocol::SourceExecutionClosure> source;
};
inline OwnedComputation readComputation(mlir::ModuleOp module,
                                        mlir::Operation *operation = nullptr) {
  if (!operation)
    module.walk([&](mlir::Operation *found) {
      if (finite::isComputation(found))
        operation = found;
    });
  OwnedComputation result;
  require(operation && mlir::succeeded(finite::describe(operation, result)),
          "missing computation");
  if (result.scoped) {
    result.source = std::make_shared<protocol::SourceExecutionClosure>(
        take(protocol::readSourceExecutionClosure(&module.getBody()->front())));
    result.scopedSource = result.source.get();
  }
  return result;
}
} // namespace zkc::test
#endif
