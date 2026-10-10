#include "zkc/Language/Inspection.h"
#include "zkc/Language/Diagnostics.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/JSON.h"

using namespace llvm;
namespace zkc::language {
namespace {
json::Array permissions(Permissions value) {
  json::Array result;
  if (value.copy)
    result.push_back("Copy");
  if (value.drop)
    result.push_back("Drop");
  if (value.share)
    result.push_back("Share");
  if (value.wire)
    result.push_back("Wire");
  return result;
}
json::Object describe(const CheckedProject &project, const Declaration &decl) {
  auto type = [&](const Type &t) { return formatType(t); };
  const auto *owner =
      decl.parent ? &project.declarations()[decl.parent->index] : nullptr;
  json::Array parameters;
  for (unsigned i = 0; i < decl.parameters.size(); ++i) {
    const auto &p = decl.parameters[i];
    std::string sort;
    switch (p.sort) {
    case Parameter::Sort::Type:
      sort = "Type";
      break;
    case Parameter::Sort::Natural:
      sort = "nat";
      break;
    case Parameter::Sort::Component:
      sort = "component";
      break;
    case Parameter::Sort::Domain:
    case Parameter::Sort::Asset:
      sort = p.domainSort;
      break;
    }
    json::Object parameter{{"name", p.name},
                           {"sort", sort},
                           {"inherited", owner && i < owner->parameters.size()},
                           {"permissions", permissions(p.permissions)}};
    if (p.interface) {
      parameter["interface"] =
          project.declarations()[p.interface->index].qualifiedName;
      json::Array arguments;
      for (const auto &arg : p.arguments)
        arguments.push_back(type(arg));
      parameter["arguments"] = std::move(arguments);
    }
    parameters.push_back(std::move(parameter));
  }
  auto roles = [&](ArrayRef<unsigned> indices) {
    json::Array result;
    for (auto index : indices)
      result.push_back(decl.roles[index]);
    return result;
  };
  auto ports = [&](ArrayRef<Port> ports) {
    json::Array result;
    for (const auto &port : ports)
      result.push_back(json::Object{{"name", port.name},
                                    {"type", type(port.type)},
                                    {"roles", roles(port.roles)}});
    return result;
  };
  json::Array services, requirements;
  for (const auto &service : decl.services)
    services.push_back(json::Object{{"name", service.name},
                                    {"field", type(service.field)},
                                    {"owner", decl.roles[service.owner]}});
  for (const auto &bound : decl.bounds)
    requirements.push_back(json::Object{{"kind", "natural"},
                                        {"lhs", formatNatural(bound.lhs)},
                                        {"rhs", formatNatural(bound.rhs)},
                                        {"inferred", bound.inferred}});
  for (const auto &bound : decl.capabilityBounds) {
    json::Array arguments;
    for (const auto &arg : bound.arguments)
      arguments.push_back(type(arg));
    requirements.push_back(json::Object{{"kind", "capability"},
                                        {"predicate", bound.predicate},
                                        {"arguments", std::move(arguments)},
                                        {"inferred", bound.inferred}});
  }
  for (const auto &bound : decl.permissionBounds)
    requirements.push_back(
        json::Object{{"kind", "permission"},
                     {"type", type(bound.type)},
                     {"permissions", permissions(bound.permissions)},
                     {"inferred", false}});
  json::Array roster, order;
  for (const auto &role : decl.roles)
    roster.push_back(role);
  for (const auto &slot : decl.inputOrder)
    order.push_back(json::Object{
        {"kind",
         slot.kind == Declaration::InputSlot::Kind::Data ? "data" : "service"},
        {"index", slot.index}});
  bool ordered = decl.kind != Declaration::Kind::Math;
  Effects effects =
      decl.body ? Effects{decl.body->mayStop, decl.body->opaque}
                : decl.effectAllowance.value_or(Effects{ordered, ordered});
  json::Object result{
      {"name", decl.qualifiedName},
      {"abstract", decl.abstract},
      {"definition", decl.primitive  ? "primitive"
                     : decl.abstract ? "abstract"
                                     : "body"},
      {"kind", !ordered                                ? "math"
               : decl.kind == Declaration::Kind::Local ? "local"
                                                       : "protocol"},
      {"parameters", std::move(parameters)},
      {"roles", std::move(roster)},
      {"input_order", std::move(order)},
      {"inputs", ports(decl.inputs)},
      {"outputs", ports(decl.outputs)},
      {"services", std::move(services)},
      {"requirements", std::move(requirements)},
      {"effects",
       json::Object{{"stop", effects.mayStop}, {"opaque", effects.opaque}}},
      {"source",
       json::Object{{"module", project.sources()[decl.module.index].module},
                    {"origin", project.sources()[decl.module.index].origin ==
                                       SourceOrigin::Installation
                                   ? "installation"
                                   : "captured"},
                    {"begin", decl.span.begin},
                    {"end", decl.span.end}}}};
  if (decl.primitive)
    result["primitive"] = decl.primitive->identity;
  if (decl.effectAllowance || decl.abstract) {
    auto allowance = decl.effectAllowance.value_or(Effects{ordered, ordered});
    result["effect_allowance"] =
        json::Object{{"stop", allowance.mayStop}, {"opaque", allowance.opaque}};
  }
  if (owner) {
    json::Object parent{{"name", owner->qualifiedName},
                        {"kind", owner->kind == Declaration::Kind::Interface
                                     ? "interface"
                                     : "component"}};
    if (owner->implementation)
      parent["implements"] = type(*owner->implementation);
    result["owner"] = std::move(parent);
  }
  return result;
}
} // namespace
Expected<std::string> inspectEntries(const CheckedProject &project,
                                     const Limits &limits) {
  if (auto failure = checkLimits(limits))
    return std::move(failure);
  std::string bytes;
  BoundedStream out(bytes, limits.interfaceBytes);
  json::OStream json(out);
  json.array([&] {
    for (auto id : project.entries()) {
      const auto &decl = project.declarations()[id.index];
      json.value(json::Object{
          {"name", decl.qualifiedName},
          {"kind", decl.entryKind() == EntryKind::Proof ? "proof" : "run"}});
      if (out.overflow())
        break;
    }
  });
  if (out.overflow())
    return error("source.limit", "Entry inventory byte limit exceeded");
  return bytes;
}
Expected<std::string> inspectDeclarations(const CheckedProject &project,
                                          const Limits &limits) {
  if (auto failure = checkLimits(limits))
    return std::move(failure);
  std::vector<const Declaration *> declarations;
  for (const auto &decl : project.declarations()) {
    // The project inventory describes captured modules. Installed definitions
    // remain available through the checked source/declaration API.
    if (project.sources()[decl.module.index].origin ==
        SourceOrigin::Installation)
      continue;
    if (decl.kind != Declaration::Kind::Math &&
        decl.kind != Declaration::Kind::Local &&
        decl.kind != Declaration::Kind::Protocol)
      continue;
    if (decl.generatedReduction)
      continue;
    const Declaration *owner = &decl;
    while (owner->parent)
      owner = &project.declarations()[owner->parent->index];
    if (owner->isPublic)
      declarations.push_back(&decl);
  }
  llvm::sort(declarations, [](auto *a, auto *b) {
    return a->qualifiedName < b->qualifiedName;
  });
  std::string bytes;
  BoundedStream out(bytes, limits.interfaceBytes);
  json::OStream json(out);
  json.array([&] {
    for (auto *decl : declarations) {
      json.value(describe(project, *decl));
      if (out.overflow())
        break;
    }
  });
  if (out.overflow())
    return error("source.limit", "declaration report byte limit exceeded");
  return bytes;
}
} // namespace zkc::language
