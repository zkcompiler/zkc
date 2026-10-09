// Bounded observation of the actual Contracts APIs. No signature replicas.
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/TypeProperties.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"
#include <iostream>

using namespace llvm;
using namespace zkc::protocol;

namespace {
constexpr size_t lineLimit = 16384;
json::Object refused() { return json::Object{{"accepted", false}}; }

using Resolver = Expected<BoundOperation> (*)(const BindingApplication &, bool);

// Test-only interpretation drift, after ordinary admission. Keep the installed
// declarations, request, input ports and physical resolution unchanged.
Expected<BoundOperation>
divergentLogicalResolver(const BindingApplication &binding, bool physical) {
  auto signature = resolveBinding(binding, physical);
  if (signature && !physical && binding.contract == "field.add") {
    auto boolean = parseBoundType("bool", false);
    if (!boolean)
      return boolean.takeError();
    signature->outputs = {std::move(*boolean)};
  }
  return signature;
}

// Count object fields before parsing so duplicate keys cannot disappear into a
// JSON map. Only ASCII transport and shallow request envelopes are in profile.
std::optional<size_t> envelope(StringRef line) {
  bool quoted = false, escaped = false;
  unsigned depth = 0;
  size_t fields = 0;
  for (unsigned char c : line) {
    if (c > 127 || (c < 32 && c != '\t' && c != '\r'))
      return std::nullopt;
    if (quoted) {
      if (escaped)
        escaped = false;
      else if (c == '\\')
        escaped = true;
      else if (c == '"')
        quoted = false;
    } else if (c == '"') {
      quoted = true;
    } else if (c == '{' || c == '[') {
      if (++depth > 8)
        return std::nullopt;
    } else if (c == '}' || c == ']') {
      if (depth == 0)
        return std::nullopt;
      --depth;
    } else if (c == ':') {
      ++fields;
    }
  }
  return quoted || depth ? std::nullopt : std::optional<size_t>(fields);
}

json::Object respond(StringRef line, Resolver resolve, bool attributeDrift,
                     bool shareDrift) {
  auto fields = envelope(line);
  if (!fields)
    return refused();
  auto parsed = json::parse(line);
  if (!parsed) {
    consumeError(parsed.takeError());
    return refused();
  }
  auto *request = parsed->getAsObject();
  if (!request || request->size() != *fields)
    return refused();
  if (request->size() == 1 && request->getBoolean("implementations") == true) {
    json::Array entries;
    for (const auto &entry : installedImplementations().all())
      entries.push_back(json::Object{{"contract", entry.contract},
                                     {"implementation", entry.identity}});
    // Resource-unit and table-relayout bindings bypass this catalog. They are
    // covered by resolver probes, not falsely reported as catalog entries.
    return json::Object{{"accepted", true},
                        {"discovery", "physical-catalog"},
                        {"implementations", std::move(entries)}};
  }
  if (request->size() == 1 && request->getString("physical_type")) {
    auto type = parseBoundType(*request->getString("physical_type"), true);
    if (!type) {
      consumeError(type.takeError());
      return refused();
    }
    return json::Object{{"accepted", true}, {"canonical", type->spelling()}};
  }
  if (request->size() == 1 && request->getString("native_policy")) {
    auto type = parseBoundType(*request->getString("native_policy"), false);
    if (!type) {
      consumeError(type.takeError());
      return refused();
    }
    auto policy = nativeTypePolicy(*type);
    if (!policy)
      return refused();
    if (shareDrift && type->spelling() == "field:koala-bear")
      policy->shared = !policy->shared;
    return json::Object{{"accepted", true},
                        {"share", policy->shared},
                        {"affine", policy->affine},
                        {"copy", duplicable(*type)},
                        {"drop", discardable(*type)}};
  }
  if (request->size() == 1) {
    auto text = request->getString("type");
    if (!text)
      return refused();
    auto type = parseBoundType(*text, false);
    if (!type) {
      consumeError(type.takeError());
      return refused();
    }
    auto physical = defaultRepresentation(*type);
    json::Value selected(nullptr);
    if (physical)
      selected = physical->spelling();
    else
      consumeError(physical.takeError());
    return json::Object{{"accepted", true},
                        {"canonical", type->spelling()},
                        {"copy", duplicable(type->spelling())},
                        {"drop", discardable(type->spelling())},
                        {"serializable", serializable(type->spelling())},
                        {"default_physical", std::move(selected)}};
  }
  const bool facetQuery =
      request->size() == 2 && request->getString("facets").has_value();
  const bool attributeQuery =
      request->size() == 5 && request->getArray("attributes");
  if (!facetQuery && !attributeQuery && request->size() != 4)
    return refused();
  auto contract = request->getString(facetQuery ? "facets" : "contract");
  auto implementation = facetQuery ? std::optional<StringRef>("")
                                   : request->getString("implementation");
  auto physical =
      facetQuery ? std::optional<bool>(false) : request->getBoolean("physical");
  auto *arguments = request->getArray("arguments");
  if (!contract || !implementation || !physical || !arguments ||
      arguments->size() > 16)
    return refused();
  BindingApplication binding{contract->str(), {}, implementation->str()};
  for (const auto &argument : *arguments) {
    auto value = argument.getAsString();
    if (!value)
      return refused();
    binding.arguments.push_back(value->str());
  }
  auto signature = resolve(binding, *physical);
  if (!signature) {
    consumeError(signature.takeError());
    return refused();
  }
  if (attributeQuery) {
    std::vector<std::string> attributes;
    for (const auto &attribute : *request->getArray("attributes")) {
      auto value = attribute.getAsString();
      if (!value)
        return refused();
      attributes.push_back(value->str());
    }
    // Deliberately perturb the value supplied to the real validator. No local
    // attribute rule or expected outcome is substituted in this driver.
    if (attributeDrift && binding.contract == "field.add")
      attributes.push_back("0");
    if (auto error = checkParameters(binding, attributes))
      return json::Object{{"accepted", true},
                          {"admitted", false},
                          {"error", toString(std::move(error))}};
    return json::Object{{"accepted", true}, {"admitted", true}};
  }
  if (facetQuery) {
    const auto *facets = operationContracts(binding.contract);
    if (!facets)
      return refused();
    return json::Object{
        {"accepted", true},
        {"facets",
         json::Object{
             {"history", isHistoryTransition(binding.contract)},
             {"publicReplay", isPublicReplay(binding.contract)},
             {"sampling", samplingContract(binding.contract) != nullptr},
             {"observation", facets->observation.has_value()},
             {"acceptanceGuard", isAcceptanceGuard(binding.contract)},
             {"conjunction", isConjunction(binding.contract)},
             {"unclassifiedProviderEffect",
              hasUnclassifiedProviderEffect(binding.contract)}}},
        {"unsupported", json::Array{}}};
  }
  json::Array inputs, outputs;
  for (const auto &type : signature->inputs)
    inputs.push_back(type.spelling());
  for (const auto &type : signature->outputs)
    outputs.push_back(type.spelling());
  return json::Object{{"accepted", true},
                      {"physical", *physical},
                      {"inputs", std::move(inputs)},
                      {"outputs", std::move(outputs)}};
}
} // namespace

int main(int argc, char **argv) {
  Resolver resolve = resolveBinding;
  bool attributeDrift = false, shareDrift = false;
  if (argc == 2 && StringRef(argv[1]) == "--divergent-logical-field-add")
    resolve = divergentLogicalResolver;
  else if (argc == 2 &&
           StringRef(argv[1]) == "--divergent-field-add-attributes")
    attributeDrift = true;
  else if (argc == 2 && StringRef(argv[1]) == "--divergent-field-share")
    shareDrift = true;
  else if (argc != 1) {
    errs() << "usage: contract-conformance [--divergent-logical-field-add | "
              "--divergent-field-add-attributes | --divergent-field-share]\n";
    return 2;
  }
  std::string line;
  bool oversized = false;
  auto emit = [&] {
    outs() << json::Value(oversized ? refused()
                                    : respond(line, resolve, attributeDrift,
                                              shareDrift))
           << '\n';
    outs().flush();
    line.clear();
    oversized = false;
  };
  char c;
  while (std::cin.get(c)) {
    if (c == '\n')
      emit();
    else if (line.size() < lineLimit)
      line.push_back(c);
    else
      oversized = true;
  }
  if (!line.empty() || oversized)
    emit();
  return std::cin.bad() ? 1 : 0;
}
