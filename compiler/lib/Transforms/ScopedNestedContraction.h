#ifndef ZKC_TRANSFORMS_SCOPEDNESTEDCONTRACTION_H
#define ZKC_TRANSFORMS_SCOPEDNESTEDCONTRACTION_H

#include "zkc/Analysis/Finite.h"

namespace zkc::nested {
// Reconstructed only by the independent source reader. This type contains no
// selected implementation or producer witness and is never input to emission.
struct ScopedSource {
  finite::Computation outer, inner;
  mlir::Operation *call = nullptr;
  unsigned matrix = 0, vector = 0, axis = 0;
  struct Seed {
    std::optional<unsigned> input;
    std::string constant;
  } seed;
  llvm::SmallVector<unsigned> inputMap;
};
std::optional<ScopedSource>
readScopedSource(const finite::Computation &computation, uint64_t &remaining,
                 bool &exhausted);
} // namespace zkc::nested
#endif
