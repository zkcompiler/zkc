//===- FriShape.h - The FRI family's one geometric fact ---------*- C++ -*-===//
// The shape equation, stated once.
//
// It is read in two places that cannot see each other: the family
// generator validates a description against it before emitting an
// instance, and the `zkc.side.fri_shape` decider re-checks it at
// dispatch against facts projected from the sealed artifact. Those are
// different inputs answering to the same fact, which is why the fact
// lives here rather than in either of them — the two sites once stated
// it differently, and the difference understated an error bound.
//===----------------------------------------------------------------------===//

#ifndef ZKC_FAMILY_FRISHAPE_H
#define ZKC_FAMILY_FRISHAPE_H

#include <cstdint>

namespace zkc {
namespace family {

/// Whether a FRI instance's declared shape is a realizable one.
///
/// The evaluation domain covers the message at rate `2^-logBlowup` and
/// the fold chain stops at a final polynomial of `2^logFinalPolyLen`
/// coefficients, so the query space's log size is the fold depth plus
/// both. A blowup below one would be a rate at or above one, where the
/// domain no longer covers the message and proximity says nothing; a
/// negative final length names no polynomial.
inline bool friShapeHolds(int64_t queryLog2, int64_t foldDepth,
                          int64_t logBlowup, int64_t logFinalPolyLen) {
  if (logBlowup < 1 || logFinalPolyLen < 0 || foldDepth < 1)
    return false;
  return queryLog2 == foldDepth + logBlowup + logFinalPolyLen;
}

} // namespace family
} // namespace zkc

#endif // ZKC_FAMILY_FRISHAPE_H
