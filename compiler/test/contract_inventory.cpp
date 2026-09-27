// Inert installation data for conformance enumeration. No consumer loads this
// output as an admission table, representation registry, or interpretation.
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/TypeRepresentations.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace zkc::protocol;

int main() {
  const auto &catalog = installedDomains();
  json::Array domains, codecs, types, representations, appliedRepresentations;
  for (const auto &domain : catalog.allDomains()) {
    json::Object members;
    json::Array capabilities;
    for (const auto &member : domain.associated)
      members[member.member] = member.identity;
    for (const auto &capability : domain.capabilities)
      capabilities.push_back(capability);
    domains.push_back(
        json::Object{{"identity", domain.identity},
                     {"sort", domain.sort},
                     {"associated", std::move(members)},
                     {"capabilities", std::move(capabilities)},
                     {"provider", catalog.defaultProvider(domain.identity)}});
  }
  for (const auto &codec : catalog.allCodecs())
    codecs.push_back(json::Object{{"identity", codec.identity},
                                  {"kind", codec.kind},
                                  {"domain", codec.domain}});
  for (const auto &type : catalog.allLogicalTypes())
    types.push_back(json::Object{{"kind", type.kind}, {"domain", type.domain}});
  for (const auto &entry : catalog.allRepresentations())
    representations.push_back(json::Object{{"kind", entry.kind},
                                           {"domain", entry.domain},
                                           {"representation", entry.identity},
                                           {"default", entry.isDefault},
                                           {"layout", entry.layout}});
  for (const auto &entry : appliedTypeRepresentations()) {
    json::Array arguments;
    for (const auto &argument : entry.arguments) {
      if (argument.kind == TypeArgument::Kind::Nat)
        arguments.push_back(json::Object{
            {"kind", "Nat"}, {"minimum", 0}, {"maximum", argument.maximum}});
      else
        arguments.push_back(json::Object{
            {"kind",
             argument.kind == TypeArgument::Kind::Type ? "Type" : "Domain"},
            {"exact", argument.exact}});
    }
    appliedRepresentations.push_back(
        json::Object{{"constructor", entry.constructor},
                     {"arguments", std::move(arguments)},
                     {"representation", entry.representation},
                     {"default", entry.isDefault}});
  }
  outs() << json::Value(json::Object{
                {"profile", "zkc.contract-catalog/1"},
                {"domains", std::move(domains)},
                {"codecs", std::move(codecs)},
                {"logical_types", std::move(types)},
                {"atomic_representations", std::move(representations)},
                {"applied_representations", std::move(appliedRepresentations)}})
         << '\n';
}
