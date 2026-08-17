//===- AnchorProjection.h - An anchor's transcript projection ---*- C++ -*-===//
// A relation anchor is a digest; a transcript absorbs field elements.
// Binding a relation's identity into a protocol's transcript needs a
// stated map between them, and the map is normative
// (docs/spec/relations.md §2.8) rather than each author's choice, so
// that two artifacts binding the same relation bind the same value.
//===----------------------------------------------------------------------===//

#ifndef ZKC_RELATION_ANCHORPROJECTION_H
#define ZKC_RELATION_ANCHORPROJECTION_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"

#include <cstdint>
#include <string>
#include <vector>

namespace zkc {
namespace relation {

/// The number of elements an anchor projects to: one per 32-bit word of
/// a sha256 digest.
constexpr unsigned kAnchorProjectionElements = 8;

/// The bits each element keeps. Below the characteristic of every field
/// a digest payload class frames, so no element is ever reduced on its
/// way into a sponge and the absorption of a projection is injective on
/// its domain (docs/spec/relations.md §2.8).
constexpr unsigned kAnchorProjectionBits = 27;

/// The eight elements of `anchor`'s transcript projection, in the
/// payload class's limb order. `anchor` is a `sha256:<64 lowercase hex>`
/// reference; anything else is an error rather than a partial result.
llvm::Expected<std::vector<uint32_t>>
anchorProjection(llvm::StringRef anchor);

/// The projection rendered as the packed decimal a seal-stage binding
/// carries: element `i` occupies the digest class's `i`-th 32-bit limb,
/// so the value a binding declares and the elements a sponge receives
/// are the same eight numbers.
llvm::Expected<std::string> anchorProjectionValue(llvm::StringRef anchor);

} // namespace relation
} // namespace zkc

#endif // ZKC_RELATION_ANCHORPROJECTION_H
