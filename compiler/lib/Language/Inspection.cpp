#include "zkc/Language/Inspection.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
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
// Render checked parameter atoms using their source binder names. This is only
// presentation; neither term substitution nor inference runs for inspection.
std::string display(std::string text, const Declaration &decl) {
  for (const auto &parameter : decl.parameters) {
    size_t offset = 0;
    while ((offset = text.find(parameter.atom, offset)) != std::string::npos) {
      auto end = offset + parameter.atom.size();
      if (end < text.size() && (isAlnum(text[end]) || text[end] == '_')) {
        offset = end;
        continue;
      }
      text.replace(offset, parameter.atom.size(), parameter.name);
      offset += parameter.name.size();
    }
  }
  return text;
}
json::Object describe(const CheckedProject &project, const Declaration &decl) {
  auto type = [&](const Type &t) { return display(spelling(t), decl); };
  json::Array parameters;
  for (const auto &p : decl.parameters) {
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
    requirements.push_back(
        json::Object{{"kind", "natural"},
                     {"lhs", display(bound.lhs.spelling(), decl)},
                     {"rhs", display(bound.rhs.spelling(), decl)},
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
       json::Object{
           {"module", project.capture().sources()[decl.module.index].module},
           {"begin", decl.span.begin},
           {"end", decl.span.end}}}};
  if (decl.effectAllowance)
    result["effect_allowance"] =
        json::Object{{"stop", decl.effectAllowance->mayStop},
                     {"opaque", decl.effectAllowance->opaque}};
  return result;
}
} // namespace
Expected<std::string> inspectDeclarations(const CheckedProject &project,
                                          const Limits &limits) {
  if (auto failure = checkLimits(limits))
    return std::move(failure);
  std::vector<const Declaration *> declarations;
  for (const auto &decl : project.declarations()) {
    if (decl.kind != Declaration::Kind::Math &&
        decl.kind != Declaration::Kind::Local &&
        decl.kind != Declaration::Kind::Protocol)
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
