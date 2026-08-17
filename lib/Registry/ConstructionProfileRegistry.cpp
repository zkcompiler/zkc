//===- ConstructionProfileRegistry.cpp - Construction profiles -*- C++ -*-===//
// Loader-time admission of the construction-profile vocabulary:
// sponge and codec entries are pure construction shape, digested at
// admission so a sealed artifact pins the content that determines its
// transcript bytes (kernel.md §8's vocabulary-citation rule). The
// squeeze-kind vocabulary is closed here, next to admission — an
// unknown derivation shape must be refused where entries load, not
// where a consumer reads it.
//===----------------------------------------------------------------------===//

#include "zkc/Registry/ConstructionProfileRegistry.h"

#include "zkc/Encoding/CanonicalJson.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
using namespace zkc::registry;

namespace {
/// The widest alphabet an admitted profile may name, in decimal digits.
/// A sample space is a field or a digest space; 1024 bits of them is
/// past anything a construction names, and it keeps the squeeze-domain
/// exponentiation's operands to a size exact arithmetic answers
/// promptly.
constexpr size_t kMaxAlphabetDigits = 309;
} // namespace

json::Value SpongeProfile::toCanonicalJson() const {
  return json::Object{{"alphabet_order", alphabetOrder},
                      {"capacity", capacity},
                      {"rate", rate}};
}

json::Value CodecProfile::toCanonicalJson() const {
  json::Object entry;
  if (squeezes())
    entry["squeeze"] =
        json::Object{{"kind", squeezeKind}, {"symbols", squeezeSymbols}};
  return json::Value(std::move(entry));
}

Expected<SpongeProfile> ConstructionProfileRegistry::parseEntry(
    const RegistryFile &file, StringRef name, const json::Value &value) {
  std::string context = ("sponge '" + name + "'").str();
  auto err = [&](const Twine &message) {
    return file.error(context + ": " + message);
  };
  const json::Object *object = value.getAsObject();
  if (!object)
    return err("must map to an object");
  if (Error e = file.requireClosedFields(
          *object, {"alphabet_order", "capacity", "rate"}, context))
    return std::move(e);
  SpongeProfile profile;
  if (Error e = file.requireStringField(*object, "alphabet_order", context,
                                        profile.alphabetOrder))
    return std::move(e);
  // Exact cardinality as a decimal string, the carrier's spelling for
  // every sample space; at least binary or the sponge carries no
  // information.
  for (char c : profile.alphabetOrder)
    if (!isDigit(c))
      return err("'alphabet_order' must be a decimal integer string");
  if (profile.alphabetOrder == "0" || profile.alphabetOrder == "1" ||
      profile.alphabetOrder.front() == '0')
    return err("'alphabet_order' must be at least 2, without leading zeros");
  // The exponent is bounded below; the base is bounded here. An
  // alphabet wide enough to make the bound evaluator's exact
  // arithmetic slow is refused rather than admitted and then endured,
  // which is the same rule the capacity and rate carry.
  if (profile.alphabetOrder.size() > kMaxAlphabetDigits)
    return err("'alphabet_order' is wider than the exact bound arithmetic "
               "admits");
  std::optional<int64_t> capacity = object->getInteger("capacity");
  if (!capacity || *capacity <= 0)
    return err("needs a positive integer 'capacity'");
  // Bounded before anything exponentiates by it: the duplex loss
  // divides by alphabet_order^capacity, and an unbounded exponent
  // lets a crafted profile hang the Soundness Kernel's bound
  // evaluator (which exponentiates by this value) — a derivation that
  // never terminates is not fail-closed.
  // No real duplex capacity is above a few dozen symbols; the cap
  // matches the codec 'symbols' bound.
  if (*capacity > 4096)
    return err("'capacity' above 4096 is not a real sponge");
  profile.capacity = *capacity;
  std::optional<int64_t> rate = object->getInteger("rate");
  if (!rate || *rate <= 0)
    return err("needs a positive integer 'rate'");
  if (*rate > 4096)
    return err("'rate' above 4096 is not a real sponge");
  profile.rate = *rate;
  auto digest = RegistryFile::digestEntry("zkc/profile-sponge\n",
                                          profile.toCanonicalJson());
  if (!digest)
    return digest.takeError();
  profile.digest = std::move(*digest);
  return profile;
}

static Expected<CodecProfile>
parseCodec(const RegistryFile &file, StringRef name, const json::Value &value) {
  std::string context = ("codec '" + name + "'").str();
  auto err = [&](const Twine &message) {
    return file.error(context + ": " + message);
  };
  const json::Object *object = value.getAsObject();
  if (!object)
    return err("must map to an object");
  if (Error e = file.requireClosedFields(*object, {"squeeze"}, context))
    return std::move(e);
  CodecProfile codec;
  if (const json::Value *squeeze = object->get("squeeze")) {
    const json::Object *shape = squeeze->getAsObject();
    if (!shape)
      return err("'squeeze' must be an object");
    if (Error e = file.requireClosedFields(*shape, {"kind", "symbols"},
                                           context + " squeeze"))
      return std::move(e);
    if (Error e = file.requireStringField(*shape, "kind", context + " squeeze",
                                          codec.squeezeKind))
      return std::move(e);
    // The derivation vocabulary is closed. mod_reduce reads `symbols`
    // alphabet symbols as one integer and reduces modulo the challenge
    // space. tuple_bijection interprets the coordinate tuple directly and
    // is admissible only for a target of exactly alphabet^symbols elements.
    // A new derivation shape is a new kind here plus the Soundness
    // Kernel rule that accounts for it.
    if (codec.squeezeKind != "mod_reduce" &&
        codec.squeezeKind != "tuple_bijection")
      return err("unknown squeeze kind '" + codec.squeezeKind +
                 "' (this loader admits: mod_reduce, tuple_bijection)");
    std::optional<int64_t> symbols = shape->getInteger("symbols");
    if (!symbols || *symbols <= 0)
      return err("squeeze needs a positive integer 'symbols'");
    // Bounded before anything exponentiates by it: no real codec
    // squeezes kilobytes per draw, and an unbounded exponent would
    // let a crafted registry hang the Soundness Kernel's bound evaluator.
    if (*symbols > 4096)
      return err("squeeze 'symbols' above 4096 is not a real codec");
    codec.squeezeSymbols = *symbols;
  }
  auto digest =
      RegistryFile::digestEntry("zkc/profile-codec\n", codec.toCanonicalJson());
  if (!digest)
    return digest.takeError();
  codec.digest = std::move(*digest);
  return codec;
}

Expected<ConstructionProfileRegistry>
ConstructionProfileRegistry::parse(StringRef json, StringRef sourceName) {
  Expected<RegistryFile> file = RegistryFile::parse(
      json, sourceName, kRegistryName, kPayloadField, {"codecs"});
  if (!file)
    return file.takeError();
  ConstructionProfileRegistry result;
  for (const auto &entry : file->payload()) {
    StringRef name(entry.first);
    if (name.empty() || !zkc::encoding::inEncodingDomain(name))
      return file->error("sponge names must be non-empty printable ASCII");
    auto parsed = parseEntry(*file, name, entry.second);
    if (!parsed)
      return parsed.takeError();
    result.addEntry(name, std::move(*parsed));
  }
  if (const json::Object *codecs = file->extra("codecs")) {
    for (const auto &entry : *codecs) {
      StringRef name(entry.first);
      if (name.empty() || !zkc::encoding::inEncodingDomain(name))
        return file->error("codec names must be non-empty printable ASCII");
      auto parsed = parseCodec(*file, name, entry.second);
      if (!parsed)
        return parsed.takeError();
      result.codecs_[name.str()] = std::move(*parsed);
    }
  }
  return result;
}
