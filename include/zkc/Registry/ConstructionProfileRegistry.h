//===- ConstructionProfileRegistry.h - Construction profiles ----*- C++ -*-===//
#ifndef ZKC_REGISTRY_CONSTRUCTIONPROFILEREGISTRY_H
#define ZKC_REGISTRY_CONSTRUCTIONPROFILEREGISTRY_H

#include "zkc/Registry/RegistryBase.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <map>
#include <string>

namespace zkc {
namespace registry {

/// One duplex-sponge profile: the construction facts a sealed kappa's
/// `sponge` name resolves to. Pure shape — alphabet size, capacity,
/// and rate in alphabet symbols; what those facts are worth is a
/// Soundness Kernel rule's business. The values are
/// attested at vocabulary admission (for the toy sponge they are the
/// declared model, like the toy field order).
struct SpongeProfile {
  std::string alphabetOrder; // |Sigma|, exact cardinality, decimal
  int64_t capacity = 0;      // c, in alphabet symbols
  int64_t rate = 0;          // r, in alphabet symbols

  /// The entry's tagged content digest (`sha256:<hex>`), computed at
  /// load. A sealed artifact that consumes this content pins
  /// the digest in its vocabulary table (kernel.md §8's
  /// vocabulary-citation rule).
  std::string digest;

  llvm::json::Value toCanonicalJson() const;
};

/// One codec profile: how a payload class crosses the sponge
/// boundary. The squeeze declaration is present exactly for codecs
/// that derive verifier messages from squeezed symbols; an
/// absorb-only codec (commitments, group elements) has none. Again
/// pure shape: both admitted kinds read `symbols` alphabet symbols.
/// `mod_reduce` maps the resulting integer modulo the challenge space;
/// `tuple_bijection` is an exact coordinate tuple and therefore applies
/// only when the challenge space is exactly alphabet_order^symbols.  What
/// either shape is worth is derived by the Soundness Kernel, never
/// declared here.
struct CodecProfile {
  std::string squeezeKind;    // closed kind vocabulary; empty = absorb-only
  int64_t squeezeSymbols = 0; // squeezed symbols per draw

  bool squeezes() const { return !squeezeKind.empty(); }

  std::string digest;

  llvm::json::Value toCanonicalJson() const;
};

/// The construction-profile registry (docs/spec/vocabularies.md §6):
/// the vocabulary the sealed kappa's `sponge` and `codecs` names
/// resolve into when a theorem row prices the Fiat-Shamir
/// transformation itself. Two sections, both fail-closed:
///
/// ```json
/// {
///   "registry": "zkc.construction_profiles",
///   "sponges": {"toy_duplex": {"alphabet_order": "256",
///                              "capacity": 32, "rate": 32}},
///   "codecs": {"ts_be8": {"squeeze": {"kind": "mod_reduce",
///                                     "symbols": 8}},
///              "bls_g1_be48": {}}
/// }
/// ```
class ConstructionProfileRegistry
    : public RegistryBase<ConstructionProfileRegistry, SpongeProfile> {
  friend class RegistryBase<ConstructionProfileRegistry, SpongeProfile>;

  static constexpr llvm::StringLiteral kRegistryName =
      "zkc.construction_profiles";
  static constexpr llvm::StringLiteral kPayloadField = "sponges";
  static constexpr llvm::StringLiteral kEntryNoun = "sponge";

  static llvm::Expected<SpongeProfile>
  parseEntry(const RegistryFile &file, llvm::StringRef name,
             const llvm::json::Value &value);

public:
  /// Multi-section envelope: sponges ride the base payload path, the
  /// codec section is parsed here under the same discipline.
  static llvm::Expected<ConstructionProfileRegistry>
  parse(llvm::StringRef json, llvm::StringRef sourceName);

  const CodecProfile *lookupCodec(llvm::StringRef name) const {
    auto it = codecs_.find(name);
    return it == codecs_.end() ? nullptr : &it->second;
  }

  const std::map<std::string, CodecProfile, std::less<>> &codecEntries() const {
    return codecs_;
  }

private:
  std::map<std::string, CodecProfile, std::less<>> codecs_;
};

} // namespace registry
} // namespace zkc

#endif // ZKC_REGISTRY_CONSTRUCTIONPROFILEREGISTRY_H
