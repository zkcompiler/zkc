#include "zkc/Mathematical/Codec.h"
#include "zkc/Mathematical/Placement.h"
#include "zkc/Source/Codec.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
namespace zkc::mathematical {
namespace {
template <class T> json::Array numbers(const std::vector<T> &values) {
  json::Array result;
  for (auto value : values)
    result.push_back(uint64_t(value));
  return result;
}
} // namespace
Expected<json::Value> encode(const PlacementWitness &witness) {
  json::Array roots, operations, wires, components, sites, results;
  for (const auto &[index, target] : witness.roots)
    roots.push_back(json::Object{{"source", index}, {"target", target}});
  for (const auto &[index, target] : witness.operations)
    operations.push_back(json::Object{{"source", index}, {"target", target}});
  for (const auto &[index, schema] : witness.wires)
    wires.push_back(json::Object{{"source", index}, {"schema", schema}});
  for (const auto &mapping : witness.components) {
    const auto &address = mapping.component.source;
    components.push_back(json::Object{
        {"instance", 0},
        {"source", json::Object{{"definition", address.definition},
                                {"regions", numbers(address.regions)},
                                {"binding", address.binding}}},
        {"role", mapping.component.role},
        {"target", json::Object{{"regions", numbers(mapping.target.regions)},
                                {"name", mapping.target.name},
                                {"path", numbers(mapping.target.path)}}}});
  }
  for (const auto &site : witness.sites)
    sites.push_back(json::Object{{"instance", 0},
                                 {"site", site.site},
                                 {"targetSite", site.targetSite},
                                 {"kind", site.kind},
                                 {"callee", json::Array{}}});
  for (const auto &result : witness.results)
    results.push_back(json::Object{{"instance", 0},
                                   {"role", result.role},
                                   {"sourcePort", result.sourcePort},
                                   {"targetPort", result.targetPort},
                                   {"path", json::Array{}}});
  json::Value encoded = json::Object{
      {"profile", "zkc.math.placement.v1"},
      {"source", witness.source},
      {"target", witness.target},
      {"instances", json::Array{json::Object{
                        {"sourceDefinition", witness.definition},
                        {"targetProtocol", witness.protocol},
                        {"targetInstance", witness.instance},
                        {"statics", numbers(witness.statics)},
                        {"roles", numbers(witness.roles)},
                        {"capabilities", numbers(witness.capabilities)}}}},
      {"roots", std::move(roots)},
      {"operations", std::move(operations)},
      {"wires", std::move(wires)},
      {"components", std::move(components)},
      {"sites", std::move(sites)},
      {"results", std::move(results)}};
  auto checked = encodeValue(encoded);
  if (!checked)
    return checked.takeError();
  return encoded;
}

Expected<std::string> placementTargetDigest(const source::Module &target) {
  if (auto failure = source::checkStructure(target))
    return failure;
  auto bytes = encodeValue(source::encode(target));
  if (!bytes)
    return bytes.takeError();
  SHA256 hash;
  hash.update("zkc.math.placement.target.v1");
  hash.update(StringRef("\0", 1));
  hash.update(*bytes);
  return toHex(hash.final(), true);
}
Expected<json::Value> encode(const Placement &placement) {
  auto source = raw::encode(placement.source.source());
  if (!source)
    return source.takeError();
  auto witness = encode(placement.witness);
  if (!witness)
    return witness.takeError();
  return json::Value(
      json::Object{{"format", "zkc.mathematical-placement/1"},
                   {"mathematical", std::move(*source)},
                   {"located", source::encode(placement.target.root())},
                   {"witness", std::move(*witness)}});
}
} // namespace zkc::mathematical
