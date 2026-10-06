#include "zkc/Compiler/Algorithms.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"
using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
Expected<ExpandedAlgorithms> expandAlgorithms(const source::Module &source,
                                              MLIRContext &context) {
  auto module = importModule(source, context);
  if (!module)
    return module.takeError();
  std::vector<AlgorithmOrigin> origins;
  if (failed(expandAlgorithms(**module, &origins)))
    return error("algorithm-expansion-failed");
  auto result = readExecutionModel(**module);
  if (!result)
    return result.takeError();
  auto expanded = source;
  expanded.functions = std::get<source::Module>(std::move(*result)).functions;
  return ExpandedAlgorithms{std::move(expanded), std::move(origins)};
}
} // namespace zkc::protocol
