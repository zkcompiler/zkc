//===- RegistryFile.cpp - The registry loading discipline -------*- C++ -*-===//
#include "zkc/Registry/RegistryFile.h"

#include "zkc/Encoding/CanonicalJson.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

#include "zkc/Encoding/EncodingDomain.h"

using namespace llvm;
using namespace zkc::registry;

Expected<std::unique_ptr<MemoryBuffer>> RegistryFile::readFile(StringRef path) {
  ErrorOr<std::unique_ptr<MemoryBuffer>> buffer = MemoryBuffer::getFile(path);
  if (!buffer)
    return createStringError(buffer.getError(), "cannot read registry '%s'",
                             path.str().c_str());
  return std::move(*buffer);
}

Expected<StringRef> RegistryFile::requireString(const json::Object &object,
                                                StringRef key,
                                                const Twine &context) const {
  std::optional<StringRef> value = object.getString(key);
  if (!value || value->empty() || !zkc::encoding::inEncodingDomain(*value))
    return error(context + " needs a non-empty printable-ASCII '" + key + "'");
  return *value;
}

Error RegistryFile::requireStringField(const json::Object &object,
                                       StringRef key, const Twine &context,
                                       std::string &out) const {
  Expected<StringRef> value = requireString(object, key, context);
  if (!value)
    return value.takeError();
  out = value->str();
  return Error::success();
}

Expected<const json::Object *>
RegistryFile::requireObject(const json::Object &object, StringRef key,
                            const Twine &context) const {
  const json::Object *value = object.getObject(key);
  if (!value)
    return error(context + " needs an object '" + key + "'");
  return value;
}

Expected<const json::Array *>
RegistryFile::requireArray(const json::Object &object, StringRef key,
                           const Twine &context) const {
  const json::Array *value = object.getArray(key);
  if (!value)
    return error(context + " needs an array '" + key + "'");
  return value;
}

Expected<int64_t> RegistryFile::requireInteger(const json::Object &object,
                                               StringRef key,
                                               const Twine &context) const {
  std::optional<int64_t> value = object.getInteger(key);
  if (!value)
    return error(context + " needs an integer '" + key + "'");
  return *value;
}

Expected<std::vector<std::string>>
RegistryFile::requireStringList(const json::Object &object, StringRef key,
                                const Twine &context) const {
  Expected<const json::Array *> arrayOrError = requireArray(object, key,
                                                            context);
  if (!arrayOrError)
    return arrayOrError.takeError();
  const json::Array *array = *arrayOrError;
  std::vector<std::string> result;
  result.reserve(array->size());
  for (const json::Value &member : *array) {
    std::optional<StringRef> value = member.getAsString();
    if (!value || value->empty() || !zkc::encoding::inEncodingDomain(*value))
      return error(context + " '" + key +
                   "' entries must be non-empty printable-ASCII strings");
    result.push_back(value->str());
  }
  return result;
}

Error RegistryFile::requireEncodingDomain(StringRef json) const {
  unsigned depth = 0;
  bool inString = false;
  bool escaped = false;
  for (size_t index = 0; index < json.size(); ++index) {
    const char c = json[index];
    if (inString) {
      if (escaped)
        escaped = false;
      else if (c == '\\')
        escaped = true;
      else if (c == '"')
        inString = false;
      continue;
    }
    if (c == '"') {
      inString = true;
    } else if (c == '{' || c == '[') {
      if (++depth > kMaxRegistryDepth)
        return error("[zkc-E120] nesting exceeds " +
                     Twine(kMaxRegistryDepth) + " levels");
    } else if (c == '}' || c == ']') {
      if (depth > 0)
        --depth;
    } else if (c == '.' || c == 'e' || c == 'E') {
      // A number token outside a string is the only place these can appear,
      // and the encoding domain has no float: an exact value is written as a
      // decimal integer or as a decimal string. Reading 3.0 as position three
      // would give one declaration two spellings, and a signature is named by
      // the digest over that declaration.
      // A number token has no interior whitespace, so the preceding
      // character settles whether this is part of one.
      if (index > 0 && (isDigit(json[index - 1]) || json[index - 1] == '.'))
        return error("[zkc-E120] a numeric value leaves the encoding domain: exact "
                     "values are decimal integers or decimal strings");
    }
  }
  return Error::success();
}

Error RegistryFile::error(const Twine &message) const {
  return createStringError(sourceName + ": " + message);
}

Error RegistryFile::requireClosedFields(const json::Object &object,
                                        ArrayRef<StringRef> allowed,
                                        const Twine &context) const {
  for (const auto &entry : object) {
    StringRef key(entry.first);
    if (!llvm::is_contained(allowed, key))
      return error(context + " has unknown field '" + key + "'");
  }
  return Error::success();
}

Expected<RegistryFile> RegistryFile::parse(StringRef json, StringRef sourceName,
                                           StringRef expectedName,
                                           StringRef payloadField,
                                           ArrayRef<StringRef> extraFields) {
  RegistryFile file;
  file.sourceName = sourceName.str();
  file.payloadField = payloadField.str();

  // Bounded before parsing, not after: the parser is recursive descent, so a
  // depth it cannot survive is one it never gets to report. The judgment over
  // a registry is total because the tree is bounded, and hostile nesting has
  // to exhaust a counter rather than an implementation
  // (docs/spec/kernel.md §3, item 4).
  if (Error err = file.requireEncodingDomain(json))
    return std::move(err);

  Expected<json::Value> parsed = zkc::encoding::parseJsonUniqueKeys(json);
  if (!parsed)
    return file.error("[zkc-E120] " + toString(parsed.takeError()));
  file.root = std::move(*parsed);

  const json::Object *rootObject = file.root.getAsObject();
  if (!rootObject)
    return file.error("[zkc-E120] top level must be an object");
  SmallVector<StringRef> allowed{"registry", payloadField};
  allowed.append(extraFields.begin(), extraFields.end());
  if (Error err = file.requireClosedFields(*rootObject, allowed,
                                           "[zkc-E120] top level"))
    return std::move(err);

  std::optional<StringRef> registryName = rootObject->getString("registry");
  if (registryName != expectedName)
    return file.error("[zkc-E120] 'registry' must be the string \"" +
                      expectedName + "\"");

  const json::Object *payload = rootObject->getObject(payloadField);
  if (!payload || payload->empty())
    return file.error("[zkc-E120] '" + payloadField +
                      "' must be a non-empty object");
  return std::move(file);
}

Expected<std::string> RegistryFile::digestEntry(StringRef tag,
                                                const json::Value &canonical) {
  std::string bytes;
  raw_string_ostream os(bytes);
  if (Error err = zkc::encoding::writeCanonicalJson(canonical, os))
    return std::move(err);
  SHA256 hasher;
  hasher.update(tag);
  hasher.update(bytes);
  return "sha256:" + toHex(hasher.final(), /*LowerCase=*/true);
}
