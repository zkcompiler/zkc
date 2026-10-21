#include "zkc/Compiler/LanguagePackage.h"
#include "LanguagePackageReader.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/SHA256.h"
#include <set>
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
      out.attribute("finite_bulk",
                    entry.options().mathematicalSelection.finiteBulk);
      out.attribute(
          "fuse_vector_reductions",
          entry.options().mathematicalSelection.vectorReductionFusion);
      out.attribute("fuse_collect_fold",
                    entry.options().mathematicalSelection.collectFoldFusion);
      out.attribute("calculation_batching",
                    entry.options().mathematicalSelection.calculationBatching);
    });
  });
  if (stream.overflow())
    return error("source.package-limit", "Entry package byte limit exceeded");
  auto digest = toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
  return EntryPackage(std::move(bytes), std::move(digest));
}
namespace detail {
Expected<PackagedEntry> readPackagedEntry(StringRef bytes,
                                          const Limits &limits) {
  auto package = parseNaturalJson(bytes, entryPackageByteLimit, 256,
                                  "entry.deployment", "source.limit");
  if (!package)
    return package.takeError();
  auto *p = package->getAsObject();
  if (!p || p->size() != 6 || p->getString("format") != "zkc.entry/0" ||
      !p->getString("original") || !p->getString("interface") ||
      !p->getString("artifact") || !p->getArray("assets") ||
      !p->getObject("options"))
    return error("entry.deployment", "invalid exact child package");
  auto *options = p->getObject("options");
  if (options->size() != 6)
    return error("entry.deployment", "invalid child compiler options");
  for (StringRef option :
       {"simplify", "release_storage", "finite_bulk", "fuse_vector_reductions",
        "fuse_collect_fold", "calculation_batching"})
    if (!options->getBoolean(option))
      return error("entry.deployment", "invalid child compiler option");
  std::vector<Asset> assets;
  std::set<std::string> identities;
  uint64_t assetBytes = 0;
  for (const auto &value : *p->getArray("assets")) {
    auto *asset = value.getAsArray();
    if (!asset || asset->size() != 2 || !(*asset)[0].getAsString() ||
        !(*asset)[1].getAsString())
      return error("entry.deployment", "invalid child asset record");
    auto id = *(*asset)[0].getAsString(), bytes = *(*asset)[1].getAsString();
    assetBytes += bytes.size();
    if (assets.size() == 256 || bytes.size() > 8 * 1024 * 1024 ||
        assetBytes > 32 * 1024 * 1024 || !identities.insert(id.str()).second)
      return error("entry.deployment", "child asset limit or duplicate");
    auto definition = json::parse(bytes);
    if (!definition)
      return definition.takeError();
    StringRef format;
    if (auto *array = definition->getAsArray(); array && !array->empty()) {
      auto tag = (*array)[0].getAsString();
      if (tag == "zkc.relation.r1cs/0")
        format = "r1cs-json";
      else if (tag == "zkc.relation-bundle/0")
        format = "relation-bundle-json";
      else if (tag == "zkc.ring/0")
        format = "ring-json";
    } else if (auto *object = definition->getAsObject();
               object && object->getString("schema") == "zkc.air.v0")
      format = "air-json";
    auto admitted =
        Asset::read({id.str(), format.str(), bytes.str(), id.str()});
    if (!admitted)
      return admitted.takeError();
    if (admitted->identity() != id)
      return error("entry.deployment", "child asset identity differs");
    assets.push_back(std::move(*admitted));
  }
  auto child = readInterface(*p->getString("original"),
                             *p->getString("interface"), limits, assets);
  if (!child)
    return child.takeError();
  return PackagedEntry{std::move(*child), p->getString("artifact")->str()};
}
} // namespace detail
} // namespace zkc::language
