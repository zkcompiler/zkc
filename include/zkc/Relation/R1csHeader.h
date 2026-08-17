//===- R1csHeader.h - The r1cs-bin-v1 reading form --------------*- C++ -*-===//
#ifndef ZKC_RELATION_R1CSHEADER_H
#define ZKC_RELATION_R1CSHEADER_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <string>

namespace zkc {
namespace relation {

/// What the `r1cs-bin-v1` header establishes as computed facts
/// (docs/spec/relations.md §5). Everything here is read from bytes; a
/// fact that is not in this struct is not one this reader can promote
/// out of the asserted tier.
struct R1csHeader {
  std::string prime;         // exact cardinality, decimal
  int64_t publicArity = 0;   // n_pub_out + n_pub_in
  int64_t privateInputs = 0; // n_prv_in
  int64_t constraintCount = 0;
  int64_t wires = 0;
};

/// Reads the iden3 R1CS binary format, version 1, header only. Closed
/// world: the admitted section types are exactly the header, the
/// constraints, and the wire-to-label map, and any other type refuses —
/// an unrecognized section can change what the sections a consumer does
/// understand mean, and this reader does not guess. Constraint bodies
/// are never read; what the header establishes is stated in R1csHeader
/// and nothing beyond it.
///
/// `declaredFieldOrder`, when non-empty, bounds the prime's byte width
/// before any allocation, so a crafted `field_size` cannot make a
/// reader allocate before it can be refused.
llvm::Expected<R1csHeader> readR1csHeader(llvm::StringRef bytes,
                                          llvm::StringRef declaredFieldOrder);

} // namespace relation
} // namespace zkc

#endif // ZKC_RELATION_R1CSHEADER_H
