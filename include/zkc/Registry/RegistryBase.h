//===- RegistryBase.h - Shared registry loading skeleton --------*- C++ -*-===//
#ifndef ZKC_REGISTRY_REGISTRYBASE_H
#define ZKC_REGISTRY_REGISTRYBASE_H

#include "zkc/Encoding/EncodingDomain.h"
#include "zkc/Registry/RegistryFile.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
#include <map>
#include <string>

namespace zkc {
namespace registry {

/// The gate every name a registry admits passes: entry names, and the
/// names inside an entry (entrypoints, parameters, roles). Names reach
/// the canonical encoding, so admission is where the domain is
/// enforced; emptiness is refused explicitly because the domain
/// predicate is vacuously true on the empty string.
///
/// `noun` is the word the diagnostic uses for what was being named.
inline llvm::Error requireEntryName(const RegistryFile &file,
                                    llvm::StringRef noun,
                                    llvm::StringRef name) {
  if (!name.empty() && zkc::encoding::inEncodingDomain(name))
    return llvm::Error::success();
  return file.error(llvm::Twine(noun) +
                    " names must be non-empty printable ASCII");
}

/// Admit one named section of a registry envelope: each key is held to
/// the name gate, then handed to `admit` with its value.
///
/// Every registry in this repository walks a named object this way,
/// including the ones whose envelopes carry several sections and so
/// cannot use `RegistryBase::parse`. Stating the loop once is what
/// keeps the name gate from being a rule each loader remembers to
/// apply.
template <typename AdmitT>
llvm::Error parseSection(const RegistryFile &file,
                         const llvm::json::Object &section,
                         llvm::StringRef entryNoun, AdmitT admit) {
  for (const auto &entry : section) {
    llvm::StringRef name(entry.first);
    if (llvm::Error error = requireEntryName(file, entryNoun, name))
      return error;
    if (llvm::Error error = admit(file, name, entry.second))
      return error;
  }
  return llvm::Error::success();
}

/// The loading skeleton every zkc registry shares. The base owns the
/// fail-closed pipeline — file read, envelope validation
/// (RegistryFile::parse), the entry-name domain gate, and the sorted
/// entry map — so a derived registry contributes exactly its schema
/// constants and its entry admission; there is no per-registry hook
/// through which loading could become lenient.
///
/// A derived class supplies:
///   - `kRegistryName`, `kPayloadField`: the
///     envelope constants RegistryFile::parse enforces;
///   - `kEntryNoun`: the word its entry-name diagnostic uses;
///   - `static llvm::Expected<EntryT> parseEntry(const RegistryFile &,
///     llvm::StringRef name, const llvm::json::Value &)`: admission of
///     one named entry, everything past the name gate.
template <typename Derived, typename EntryT> class RegistryBase {
public:
  static llvm::Expected<Derived> loadFromFile(llvm::StringRef path) {
    auto buffer = RegistryFile::readFile(path);
    if (!buffer)
      return buffer.takeError();
    // Derived:: so a registry that owns its parse (multi-section
    // envelope) is reached; plain `parse` would bind to the base.
    return Derived::parse((*buffer)->getBuffer(), path);
  }

  static llvm::Expected<Derived> parse(llvm::StringRef json,
                                       llvm::StringRef sourceName) {
    llvm::Expected<RegistryFile> file = RegistryFile::parse(
        json, sourceName, Derived::kRegistryName, Derived::kPayloadField);
    if (!file)
      return file.takeError();
    Derived result;
    if (llvm::Error error = parseSection(
            *file, file->payload(), Derived::kEntryNoun,
            [&](const RegistryFile &from, llvm::StringRef name,
                const llvm::json::Value &value) -> llvm::Error {
              llvm::Expected<EntryT> parsed =
                  Derived::parseEntry(from, name, value);
              if (!parsed)
                return parsed.takeError();
              result.entries_[name.str()] = std::move(*parsed);
              return llvm::Error::success();
            }))
      return std::move(error);
    return result;
  }

  /// Returns the entry registered under `name`, or null — the caller's
  /// unknown-entry case, which every consumer treats fail-closed.
  const EntryT *lookup(llvm::StringRef name) const {
    auto it = entries_.find(name);
    return it == entries_.end() ? nullptr : &it->second;
  }

  /// All entries in sorted order — deterministic; the lint tool's dump
  /// order.
  const std::map<std::string, EntryT, std::less<>> &entries() const {
    return entries_;
  }

protected:
  /// For a derived registry whose envelope carries several sections:
  /// entries reach here from a `parseSection` walk, so they pass the
  /// same name gate as every other entry.
  void addEntry(llvm::StringRef name, EntryT entry) {
    entries_[name.str()] = std::move(entry);
  }

private:
  std::map<std::string, EntryT, std::less<>> entries_;
};

} // namespace registry
} // namespace zkc

#endif // ZKC_REGISTRY_REGISTRYBASE_H
