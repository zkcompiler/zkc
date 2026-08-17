//===- KernelPredicates.h - The shapes a kernel value may take --*- C++ -*-===//
// Four translation units asked the same four questions of a value —
// whether a citation names both an authority and a revision, and
// whether a rational is an integer, a positive one, a non-negative one
// — and each answered them for itself, byte for byte the same. A
// predicate every layer shares is a fact about the kernel's value
// domain rather than a convenience local to whoever needed it first.
//
// Header-only and Support-only, so the soundness libraries stay free
// of MLIR and the compiler core can read them too.
//===----------------------------------------------------------------------===//

#ifndef ZKC_SOUNDNESS_KERNELPREDICATES_H
#define ZKC_SOUNDNESS_KERNELPREDICATES_H

#include "zkc/Registry/Rational.h"
#include "zkc/Soundness/SoundnessRuntime.h"

namespace zkc {
namespace soundness {

/// Whether a citation names both what it cites and which revision of
/// it. A reference missing either half pins nothing.
inline bool validRef(const ExactRef &ref) {
  return !ref.id.empty() && !ref.sourceRevision.empty();
}

/// Whether an exact rational denotes an integer. The rational is
/// canonical, so its denominator says this outright.
inline bool isInteger(const registry::Rational &value) {
  return value.denStr() == "1";
}

inline bool isPositive(const registry::Rational &value) {
  return value.compare(registry::Rational::fromInteger(0)) > 0;
}

inline bool isNonnegative(const registry::Rational &value) {
  return value.compare(registry::Rational::fromInteger(0)) >= 0;
}

inline bool isPositiveInteger(const registry::Rational &value) {
  return isInteger(value) && isPositive(value);
}

} // namespace soundness
} // namespace zkc

#endif // ZKC_SOUNDNESS_KERNELPREDICATES_H
