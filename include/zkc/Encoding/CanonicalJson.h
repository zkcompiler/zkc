//===- CanonicalJson.h - Deterministic JSON emission ------------*- C++ -*-===//
#ifndef ZKC_ENCODING_CANONICALJSON_H
#define ZKC_ENCODING_CANONICALJSON_H

#include "mlir/IR/BuiltinAttributes.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"

#include <string>

namespace zkc {
namespace encoding {

/// Parses JSON while refusing duplicate object keys at every nesting depth.
/// LLVM's ordinary parser otherwise keeps the last value, which would give an
/// authority document two source spellings for one admitted object. Syntax and
/// UTF-8 validation remain delegated to LLVM; this adds the missing uniqueness
/// judgment before consumers inspect the parsed tree.
llvm::Expected<llvm::json::Value> parseJsonUniqueKeys(llvm::StringRef input);

/// Serializes `value` as deterministic JSON: object keys sorted by code
/// point, compact separators (no whitespace), and integers only. The
/// enforced encoding domain (kernel.md §3, item 4) admits printable-ASCII
/// strings alone, so anything outside that range is an error, never an
/// escape. This is the byte format of the canonical protocol encoding
/// (docs/spec/carrier.md §6); `reference/oracle/model.py` must
/// produce identical bytes for the same data, and the differential
/// test suite holds both sides to that.
///
/// Fails on non-integer numbers and on out-of-domain strings; neither
/// can appear in a canonical encoding.
llvm::Error writeCanonicalJson(const llvm::json::Value &value,
                               llvm::raw_ostream &os);

/// Converts the closed identity-bearing MLIR attribute domain to JSON:
/// printable-ASCII strings, signed-64-bit integers, arrays, and dictionaries.
/// No caller gets to invent a second attribute spelling for a digest preimage.
llvm::Expected<llvm::json::Value>
attributeToCanonicalJson(mlir::Attribute attribute, unsigned depth = 0);

/// The deterministic bytes produced by writeCanonicalJson.
llvm::Expected<std::string> canonicalJsonBytes(const llvm::json::Value &value);

/// `sha256:` reference over `domain || canonical(value)`. Domains include
/// their terminating newline at the call site, making allocations visible.
llvm::Expected<std::string> taggedSha256Ref(llvm::StringRef domain,
                                            const llvm::json::Value &value);

} // namespace encoding
} // namespace zkc

#endif // ZKC_ENCODING_CANONICALJSON_H
