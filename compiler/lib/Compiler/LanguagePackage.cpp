#include "zkc/Compiler/LanguagePackage.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/SHA256.h"
using namespace llvm;
namespace zkc::language {
Expected<EntryPackage> packageEntry(const CompiledEntry &entry,
                                    uint64_t byteLimit) {
  if (byteLimit > entryPackageByteLimit ||
      entry.bytes().size() > 16 * 1024 * 1024)
    return error("source.package-limit", "Entry package limit exceeded");
  std::string bytes;
  BoundedStream stream(bytes, byteLimit);
  json::OStream out(stream);
  out.object([&] {
    out.attribute("format", "zkc.entry");
    out.attribute("original", entry.original().bytes());
    out.attribute("interface", entry.original().interfaceJson());
    out.attribute("artifact", entry.bytes());
    out.attributeObject("options", [&] {
      out.attribute("simplify", entry.options().simplify);
      out.attribute("release_storage", entry.options().releaseStorage);
    });
  });
  if (stream.overflow())
    return error("source.package-limit", "Entry package byte limit exceeded");
  auto digest = toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
  return EntryPackage(std::move(bytes), std::move(digest));
}
} // namespace zkc::language
