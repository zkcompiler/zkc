#ifndef ZKC_SOURCE_SNAPSHOT_H
#define ZKC_SOURCE_SNAPSHOT_H

#include "zkc/Source/Codec.h"
#include "llvm/Support/Error.h"

namespace zkc::source {
/// Exact portable-source snapshot used by persisted compiler selectors.
/// Structural validation precedes hashing. This is neither a transcript
/// identity nor an authentication claim. An optional map records encoding
/// coordinates during the same traversal used to compute the digest.
llvm::Expected<std::string> snapshot(const Content &, RecordMap * = nullptr);
llvm::Expected<std::string> snapshot(const Module &, RecordMap * = nullptr);
} // namespace zkc::source

#endif
