#include "zkc/Compiler/LanguagePackage.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Json.h"
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
  std::vector<std::pair<std::string, std::string>> assets;
  uint64_t assetBytes = 0;
  for (const auto &asset : entry.original().entry().assets()) {
    auto body = printJson(asset.encode());
    assetBytes += body.size();
    if (body.size() > 8 * 1024 * 1024 || assetBytes > 32 * 1024 * 1024 ||
        assets.size() == 256)
      return error("source.package-limit", "Entry asset limit exceeded");
    assets.emplace_back(asset.identity().str(), std::move(body));
  }
  std::string bytes;
  BoundedStream stream(bytes, byteLimit);
  json::OStream out(stream);
  out.object([&] {
    out.attribute("format", "zkc.entry/0");
    out.attribute("original", entry.original().bytes());
    out.attribute("interface", entry.original().interfaceJson());
    out.attribute("artifact", entry.bytes());
    out.attributeArray("assets", [&] {
      for (const auto &asset : assets)
        out.array([&] {
          out.value(asset.first);
          out.value(asset.second);
        });
    });
    out.attributeObject("options", [&] {
      out.attribute("simplify", entry.options().simplify);
      out.attribute("release_storage", entry.options().releaseStorage);
      out.attribute("fuse_vector_reductions",
                    entry.options().fuseVectorReductions);
    });
  });
  if (stream.overflow())
    return error("source.package-limit", "Entry package byte limit exceeded");
  auto digest = toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
  return EntryPackage(std::move(bytes), std::move(digest));
}
} // namespace zkc::language
