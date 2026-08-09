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
    for (const auto &entry : file->payload()) {
      llvm::StringRef name(entry.first);
      // Entry names reach the canonical encoding, so admission is where
      // the domain gate lives; emptiness is refused explicitly because
      // the domain predicate is vacuously true on the empty string.
      if (name.empty() || !zkc::encoding::inEncodingDomain(name))
        return file->error(llvm::Twine(Derived::kEntryNoun) +
                           " names must be non-empty printable ASCII");
      llvm::Expected<EntryT> parsed =
          Derived::parseEntry(*file, name, entry.second);
      if (!parsed)
        return parsed.takeError();
      result.entries_[name.str()] = std::move(*parsed);
    }
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
  /// For a derived registry that owns its parse (multi-section
  /// envelopes): entries still pass the same name gate + parseEntry
  /// path, they just land through here.
  void addEntry(llvm::StringRef name, EntryT entry) {
    entries_[name.str()] = std::move(entry);
  }

private:
  std::map<std::string, EntryT, std::less<>> entries_;
};

} // namespace registry
} // namespace zkc

#endif // ZKC_REGISTRY_REGISTRYBASE_H
