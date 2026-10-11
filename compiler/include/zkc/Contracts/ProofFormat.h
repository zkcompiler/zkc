#ifndef ZKC_CONTRACTS_PROOFFORMAT_H
#define ZKC_CONTRACTS_PROOFFORMAT_H

#include "llvm/ADT/StringRef.h"
#include <optional>

namespace zkc::protocol {
// The deployment selects the transport. Candidate proof bytes never select it.
enum class ProofFormat { Native, RawBytes };
inline llvm::StringRef proofFormatName(ProofFormat format) {
  return format == ProofFormat::Native ? "zkc.framed/0" : "raw.bytes/0";
}
inline std::optional<ProofFormat> parseProofFormat(llvm::StringRef value) {
  if (value == "zkc.framed/0")
    return ProofFormat::Native;
  if (value == "raw.bytes/0")
    return ProofFormat::RawBytes;
  return std::nullopt;
}
} // namespace zkc::protocol
#endif
