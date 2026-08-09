//===- EncodingDomain.h - The canonical encoding domain ---------*- C++ -*-===//
#ifndef ZKC_ENCODING_ENCODINGDOMAIN_H
#define ZKC_ENCODING_ENCODINGDOMAIN_H

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringRef.h"

namespace zkc {
namespace encoding {

/// The string half of the canonical encoding domain (kernel.md §3, item 4):
/// printable ASCII only. Everything identity-bearing — op fields,
/// kappa, expr trees, and registry vocabulary (schema ids and roles
/// enter reduce rows) — must satisfy this; the seal battery and the
/// registry loaders reject violations, so the two encoders never see
/// an input they could disagree on. Header-only so the registry
/// library needs no encoding-library link.
inline bool inEncodingDomain(llvm::StringRef value) {
  return llvm::all_of(value, [](char c) {
    return static_cast<unsigned char>(c) >= 0x20 &&
           static_cast<unsigned char>(c) <= 0x7e;
  });
}

/// The integer half (kernel.md §3, item 4): signed-64-bit-representable.
/// Callers pass the attribute's APInt and signedness so this stays
/// MLIR-free.
inline bool inIntegerDomain(const llvm::APInt &value, bool isUnsigned) {
  return value.getBitWidth() <= 64 &&
         (!isUnsigned || value.getActiveBits() <= 63);
}

/// 64-lowercase-hex — the digest body of a `sha256:` reference and of
/// artifact ids (kernel.md §8: one identity, one spelling).
inline bool isLowerHex64(llvm::StringRef value) {
  return value.size() == 64 && llvm::all_of(value, [](char c) {
           return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f');
         });
}

/// A full digest reference — `sha256:` + 64 lowercase hex, kernel.md
/// §8's reference form. The one predicate every citation surface
/// (anchors, artifact sources, row revisions, opt-in requests)
/// shares, so no surface can drift to a laxer spelling.
inline bool isSha256Ref(llvm::StringRef value) {
  return value.consume_front("sha256:") && isLowerHex64(value);
}

/// The nesting bound for identity-bearing attribute trees (expr,
/// kappa, params, anchors). Real interiors are a handful of levels;
/// the bound exists so every recursive walk over authored or loaded
/// content is total — a hostile depth must exhaust a counter, never
/// the stack (kernel §3 WF is decidable structure checking).
inline constexpr unsigned kMaxAttrDepth = 64;

} // namespace encoding
} // namespace zkc

#endif // ZKC_ENCODING_ENCODINGDOMAIN_H
