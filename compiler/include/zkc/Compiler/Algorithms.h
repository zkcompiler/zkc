#ifndef ZKC_COMPILER_ALGORITHMS_H
#define ZKC_COMPILER_ALGORITHMS_H
#include "zkc/Transforms/Algorithms.h"
namespace zkc::protocol {
/// Source convenience adapter: import, expand SSA calls and reconstruct the
/// admitted source model. Requires the CompilerCore library.
struct ExpandedAlgorithms {
  source::Module source;
  std::vector<AlgorithmOrigin> origins;
};
llvm::Expected<ExpandedAlgorithms> expandAlgorithms(const source::Module &,
                                                    mlir::MLIRContext &);
} // namespace zkc::protocol
#endif
