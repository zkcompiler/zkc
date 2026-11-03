#ifndef ZKC_SUPPORT_LOGICALTREE_H
#define ZKC_SUPPORT_LOGICALTREE_H
#include "llvm/Support/JSON.h"
#include <cstdint>
namespace zkc {
/// Canonical bounded string/array tree bytes shared by construction formats.
/// Syntax validity does not establish correspondence or authority.
llvm::Expected<std::string> encodeLogicalTree(const llvm::json::Value &tree);
/// The leading bytes of the canonical encoding of an array of `arity` elements
/// whose first elements are `elements`: the array header with its full
/// eight-byte arity, then each present element's canonical bytes. Appending
/// the canonical bytes of the remaining elements gives `encodeLogicalTree` of
/// the completed array.
///
/// Bounds on the prefix: the declared arity is at most the array element
/// limit, `elements` holds at most that many elements, the present elements
/// obey the full encoding's depth, node, string-length and array-length limits
/// as children of the array, and the prefix bytes fit the byte limit. Bounds
/// on the completed tree are not checked here: its total bytes and node count,
/// including the elements still to come, belong to the caller that appends
/// them. This encodes bytes only; it neither reconstructs nor authorizes the
/// tree it begins.
llvm::Expected<std::string>
encodeLogicalTreePrefix(const llvm::json::Array &elements, uint64_t arity);
} // namespace zkc
#endif
