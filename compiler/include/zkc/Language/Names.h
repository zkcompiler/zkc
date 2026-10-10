#ifndef ZKC_LANGUAGE_NAMES_H
#define ZKC_LANGUAGE_NAMES_H

#include "llvm/ADT/StringRef.h"
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>

namespace zkc::language {

struct SourceScalar {
  uint32_t value;
  size_t bytes;
};

// Strict UTF-8 at an exact byte offset; never reads past the supplied view.
std::optional<SourceScalar> decodeSourceScalar(llvm::StringRef text,
                                               size_t offset);
bool sourceIdentifierStart(uint32_t scalar);
bool sourceIdentifierContinue(uint32_t scalar);
bool isSourceIdentifier(llvm::StringRef text);

// Checks exact spelling, without rewriting it. Callers enforce their source
// byte limits before admission. This also accepts non-identifier NFC text;
// identifier admission checks the pinned repertoire before calling it.
bool isSourceNFC(llvm::StringRef text);
bool isMathematicalSymbol(uint32_t scalar);
std::optional<uint32_t> matchingSourceDelimiter(uint32_t opener);
bool isSourceDelimiterCloser(uint32_t scalar);
std::string sourceNameProfileIdentity();

// The caller validates the authenticated roster and its count first.
std::string nativeRoleName(unsigned ordinal);
std::string nativeSetupName(unsigned ordinal);
std::string nativeAlternativeName(unsigned ordinal);

// Exact UTF-8 preimage bytes, without normalization. Decoding accepts only
// lowercase, even-length hex and valid UTF-8, bounded by decoded byte count.
// The encoder's caller bounds the preimage and its twofold encoded expansion.
std::string encodeNominalIdentity(llvm::StringRef text);
std::optional<std::string> decodeNominalIdentity(llvm::StringRef hex,
                                                 uint64_t maxBytes);

// Validate qualified identifier segments and preflight the complete expanded
// byte count before allocating. The encoding includes ASCII segments too.
std::optional<std::string> encodeSourceSymbol(llvm::StringRef qualifiedName,
                                              uint64_t maxBytes);

} // namespace zkc::language

#endif
