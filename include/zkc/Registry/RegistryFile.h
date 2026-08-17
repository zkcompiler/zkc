//===- RegistryFile.h - The registry loading discipline ---------*- C++ -*-===//
#ifndef ZKC_REGISTRY_REGISTRYFILE_H
#define ZKC_REGISTRY_REGISTRYFILE_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include <string>
#include <vector>

namespace zkc {
namespace registry {

/// One loading discipline for every zkc registry (carrier.md §7):
/// a registry file is JSON with a closed envelope —
///
/// ```json
/// {"registry": "<name>", "<payload>": {...}}
/// ```
///
/// — where a wrong name or any unknown field
/// fails closed: a reader that skipped fields it does not understand
/// could silently accept data written against a newer schema.
/// Duplicate object keys fail before schema validation at every nesting
/// depth, so an authority input never acquires a parser-dependent last-wins
/// reading. Registries are seal-time environment
/// consumed by boundary passes, never artifact content (kernel §7
/// separates RegistryEnv from P).
class RegistryFile {
public:
  /// `extraFields` admits additional top-level sections beside the
  /// payload (the soundness signature carries its schemas, bindings, and
  /// annotations); every field outside {registry, payload,
  /// extras} still fails closed.
  static llvm::Expected<RegistryFile>
  parse(llvm::StringRef json, llvm::StringRef sourceName,
        llvm::StringRef expectedName, llvm::StringRef payloadField,
        llvm::ArrayRef<llvm::StringRef> extraFields = {});

  /// The payload object (re-derived from the owned root, so the file
  /// value is safely movable).
  const llvm::json::Object &payload() const {
    return *root.getAsObject()->getObject(payloadField);
  }

  /// An extra top-level section admitted via `extraFields`; null when
  /// absent.  A caller that treats absent and present-but-not-an-object
  /// alike would read a mistyped section as an empty one, so ask
  /// `hasExtra` first when the distinction matters.
  const llvm::json::Object *extra(llvm::StringRef field) const {
    return root.getAsObject()->getObject(field);
  }

  /// Whether the section is written at all, whatever its shape.
  bool hasExtra(llvm::StringRef field) const {
    return root.getAsObject()->get(field) != nullptr;
  }

  /// An extra top-level section that is a list; null when absent or when it
  /// is written as something else.  Pair it with `hasExtra` when the two
  /// cases have to be told apart.
  const llvm::json::Array *extraArray(llvm::StringRef field) const {
    return root.getAsObject()->getArray(field);
  }

  /// An extra top-level section that is an object, with the same contract as
  /// `extraArray`.
  const llvm::json::Object *extraObject(llvm::StringRef field) const {
    return root.getAsObject()->getObject(field);
  }

  /// A schema-violation error, prefixed with the source name so every
  /// diagnostic names its file.
  llvm::Error error(const llvm::Twine &message) const;

  /// The nesting a registry tree may reach, matching the encoding domain's
  /// descriptor bound (docs/spec/kernel.md §3, item 4).
  static constexpr unsigned kMaxRegistryDepth = 64;

  /// Refuse a document that leaves the encoding domain before a recursive
  /// parser is asked to walk it: nesting beyond the bound, and any float,
  /// which the domain does not represent.
  llvm::Error requireEncodingDomain(llvm::StringRef json) const;

  /// Fails closed on any field of `object` outside `allowed`.
  llvm::Error requireClosedFields(const llvm::json::Object &object,
                                  llvm::ArrayRef<llvm::StringRef> allowed,
                                  const llvm::Twine &context) const;

  /// A required string field: present, non-empty, and inside the
  /// canonical encoding domain — registry vocabulary reaches the
  /// canonical encoding, so admission is where the domain gate lives.
  llvm::Expected<llvm::StringRef>
  requireString(const llvm::json::Object &object, llvm::StringRef key,
                const llvm::Twine &context) const;

  /// requireString, copied into owned storage (registry entries outlive
  /// the parsed JSON).
  llvm::Error requireStringField(const llvm::json::Object &object,
                                 llvm::StringRef key,
                                 const llvm::Twine &context,
                                 std::string &out) const;

  /// The shape validators, in the one spelling the loaders share.
  /// Without them each loader writes its own sentence for "this key is
  /// not the shape the schema says", and a reader who has seen two of
  /// them cannot tell whether they mean the same thing. A site with
  /// something further to say about the shape says it separately rather
  /// than by rewording the refusal.
  llvm::Expected<const llvm::json::Object *>
  requireObject(const llvm::json::Object &object, llvm::StringRef key,
                const llvm::Twine &context) const;

  llvm::Expected<const llvm::json::Array *>
  requireArray(const llvm::json::Object &object, llvm::StringRef key,
               const llvm::Twine &context) const;

  llvm::Expected<int64_t> requireInteger(const llvm::json::Object &object,
                                         llvm::StringRef key,
                                         const llvm::Twine &context) const;

  /// A required array field whose members are all held to the same
  /// domain gate as requireString. An empty array is legal — presence
  /// requirements beyond existence stay with the caller.
  llvm::Expected<std::vector<std::string>>
  requireStringList(const llvm::json::Object &object, llvm::StringRef key,
                    const llvm::Twine &context) const;

  /// Reads a registry file with the uniform failure message every
  /// loader and the lint tool share.
  static llvm::Expected<std::unique_ptr<llvm::MemoryBuffer>>
  readFile(llvm::StringRef path);

  /// The tagged content digest every registry entry shares
  /// (kernel.md §8's vocabulary-citation rule): canonical JSON bytes
  /// under a domain-separation tag, as `sha256:<hex>`. One
  /// implementation so the tag discipline has one place to audit
  /// against the reference twin's *_digest mirrors.
  static llvm::Expected<std::string>
  digestEntry(llvm::StringRef tag, const llvm::json::Value &canonical);

private:
  std::string sourceName;
  std::string payloadField;
  llvm::json::Value root = nullptr;
};

} // namespace registry
} // namespace zkc

#endif // ZKC_REGISTRY_REGISTRYFILE_H
