// Inert installation data for conformance enumeration. No consumer loads this
// output as an admission table, representation registry, or interpretation.
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeRepresentations.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace zkc::protocol;

int main() {
  const auto &catalog = installedDomains();
  json::Array domains, codecs, types, representations, appliedRepresentations;
  json::Array fields, services, cosets, widths;
  for (const auto &domain : catalog.allDomains()) {
    // Declared order is part of the published catalogue bytes, so members
    // are ordered pairs rather than an object.
    json::Array members;
    json::Array capabilities;
    for (const auto &member : domain.associated)
      members.push_back(json::Array{member.member, member.identity});
    for (const auto &capability : domain.capabilities)
      capabilities.push_back(capability);
    domains.push_back(
        json::Object{{"identity", domain.identity},
                     {"sort", domain.sort},
                     {"members", std::move(members)},
                     {"capabilities", std::move(capabilities)},
                     {"modulus", domain.modulus},
                     {"provider", catalog.defaultProvider(domain.identity)}});
    if (const auto *convention = cosetConvention(domain.identity))
      cosets.push_back(json::Object{{"field", domain.identity},
                                    {"identity", convention->identity},
                                    {"rootField", convention->rootField},
                                    {"maximalRoot", convention->maximalRoot},
                                    {"order", convention->order},
                                    {"maxLogSize", convention->maxLogSize}});
    if (unsigned width = fieldBitPatternWidth(domain.identity))
      widths.push_back(
          json::Object{{"field", domain.identity}, {"width", width}});
  }
  for (const auto &field : plonky3Fields())
    fields.push_back(json::Object{{"identity", field.identity},
                                  {"base", field.base},
                                  {"modulus", field.modulus},
                                  {"degree", field.degree},
                                  {"nonresidue", field.nonresidue},
                                  {"coordinateBytes", field.coordinateBytes},
                                  {"montgomery32", field.montgomery32}});
  for (const auto &service : randomServices())
    services.push_back(
        json::Object{{"contract", service.contract}, {"field", service.field}});
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
      if (argument.argument.kind == TypeArgument::Kind::Nat)
        arguments.push_back(json::Object{{"kind", "Nat"},
                                         {"minimum", argument.minimum},
                                         {"maximum", argument.maximum}});
      else
        arguments.push_back(json::Object{
            {"kind", argument.argument.kind == TypeArgument::Kind::Type
                         ? "Type"
                         : "Domain"},
            {"exact", argument.argument.spelling()}});
    }
    appliedRepresentations.push_back(
        json::Object{{"constructor", entry.constructor},
                     {"arguments", std::move(arguments)},
                     {"representation", entry.representation},
                     {"default", entry.isDefault},
                     {"child", entry.childType.spelling()}});
  }
  outs() << json::Value(json::Object{
                {"profile", "zkc.contract-catalog"},
                {"domains", std::move(domains)},
                {"codecs", std::move(codecs)},
                {"logical_types", std::move(types)},
                {"atomic_representations", std::move(representations)},
                {"applied_representations", std::move(appliedRepresentations)},
                {"plonky3_fields", std::move(fields)},
                {"random_services", std::move(services)},
                {"coset_conventions", std::move(cosets)},
                {"bit_pattern_widths", std::move(widths)}})
         << '\n';
}
