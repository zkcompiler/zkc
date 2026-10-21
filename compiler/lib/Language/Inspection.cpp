#include "zkc/Language/Inspection.h"
#include "State.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Language/Diagnostics.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/JSON.h"
#include <tuple>

using namespace llvm;
namespace zkc::language {
namespace {
json::Array permissions(Permissions value) {
  json::Array result;
  if (value.copy)
    result.push_back("Copy");
  if (value.drop)
    result.push_back("Drop");
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
    case Parameter::Sort::Module:
      sort = "module";
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
                     {"inferred", bound.inferred}});
  auto location = [&](Span span) {
    return json::Object{{"module", project.sources()[span.source.index].module},
                        {"begin", span.begin},
                        {"end", span.end}};
  };
  json::Array admissions;
  for (const auto &obligation : decl.admissions) {
    json::Array calls;
    for (auto span : obligation.calls)
      calls.push_back(location(span));
    admissions.push_back(json::Object{
        {"kind", obligation.boundary == Boundary::Participants ? "participants"
                 : obligation.boundary == Boundary::Construction
                     ? "construction"
                     : "message"},
        {"type", type(obligation.type)},
        {"source", location(obligation.span)},
        {"calls", std::move(calls)}});
  }
  auto selector = [&](const InputSelector &input, unsigned axis) {
    json::Array path;
    for (auto index : input.path)
      path.push_back(index);
    return json::Object{{"input", decl.inputs[input.port].name},
                        {"path", std::move(path)},
                        {"axis", axis}};
  };
  for (const auto &condition : decl.dataPreconditions)
    requirements.push_back(json::Object{
        {"kind", condition.kind == DataPrecondition::Kind::IndexBound
                     ? "index_bound"
                     : "equal_extent"},
        {"left", selector(condition.left, condition.leftAxis)},
        {"right", selector(condition.right, condition.rightAxis)}});
  json::Array scoped;
  for (const auto &parameter : decl.scopedInputs) {
    json::Array inputs;
    for (const auto &input : parameter.signature.inputs)
      inputs.push_back(type(input));
    scoped.push_back(json::Object{
        {"name", parameter.name},
        {"mode", parameter.signature.mode == ScopedSignature::Mode::Math
                     ? "math"
                     : "local"},
        {"inputs", std::move(inputs)},
        {"result", type(parameter.signature.result)},
        {"effect_allowance",
         json::Object{{"stop", parameter.signature.allowance.mayStop},
                      {"opaque", parameter.signature.allowance.opaque}}}});
    json::Array labels, origins;
    for (unsigned i = 0; i < parameter.signature.inputs.size(); ++i)
      labels.push_back(i < parameter.inputLabels.size() &&
                               !parameter.inputLabels[i].empty()
                           ? json::Value(parameter.inputLabels[i])
                           : json::Value(nullptr));
    for (const auto &[input, domain] : parameter.itemOrigins)
      origins.push_back(json::Object{{"input", input}, {"domain", domain}});
    (*scoped.back().getAsObject())["input_labels"] = std::move(labels);
    (*scoped.back().getAsObject())["item_origins"] = std::move(origins);
  }
  json::Array roster, order;
  for (const auto &role : decl.roles)
    roster.push_back(role);
  for (const auto &slot : decl.inputOrder)
    order.push_back(json::Object{
        {"kind", slot.kind == Declaration::InputSlot::Kind::Data     ? "data"
                 : slot.kind == Declaration::InputSlot::Kind::Scoped ? "scoped"
                 : slot.kind == Declaration::InputSlot::Kind::Domain
                     ? "domain"
                     : "service"},
        {"index", slot.index}});
  bool domain = decl.kind == Declaration::Kind::DomainFunction;
  bool ordered = decl.kind != Declaration::Kind::Math && !domain;
  auto renderEffects = [](const EffectSummary &summary) {
    json::Array dependencies;
    for (const auto &[slot, ceiling] : summary.dependencies)
      dependencies.push_back(json::Object{{"callback", slot},
                                          {"stop", ceiling.mayStop},
                                          {"opaque", ceiling.opaque}});
    return json::Object{{"stop", summary.fixed.mayStop},
                        {"opaque", summary.fixed.opaque},
                        {"dependencies", std::move(dependencies)}};
  };
  auto effects = decl.body ? decl.body->effects
                           : decl.effectAllowance.value_or(EffectSummary{});
  json::Object result{
      {"name", decl.qualifiedName},
      {"abstract", decl.abstract},
      {"definition", decl.primitive          ? "primitive"
                     : decl.finiteDefinition ? "finite"
                     : decl.abstract         ? "abstract"
                                             : "body"},
      {"kind", domain                                          ? "domain"
               : !ordered                                      ? "math"
               : decl.kind == Declaration::Kind::EntryFunction ? "entry"
               : decl.kind == Declaration::Kind::Local         ? "local"
                                                               : "protocol"},
      {"parameters", std::move(parameters)},
      {"roles", std::move(roster)},
      {"input_order", std::move(order)},
      {"inputs", ports(decl.inputs)},
      {"scoped_inputs", std::move(scoped)},
      {"outputs", ports(decl.outputs)},
      {"services", std::move(services)},
      {"requirements", std::move(requirements)},
      {"admissions", std::move(admissions)},
      {"effects", renderEffects(effects)},
      {"source",
       json::Object{
           {"module", project.sources()[decl.span.source.index].module},
           {"origin", project.sources()[decl.span.source.index].origin ==
                              SourceOrigin::Installation
                          ? "installation"
                          : "captured"},
           {"begin", decl.span.begin},
           {"end", decl.span.end}}}};
  if (decl.kind == Declaration::Kind::EntryFunction ||
      (decl.generated && decl.generated->operation))
    result["stage"] = "host";
  if (decl.generated) {
    result["generated"] = json::Object{
        {"target",
         project.declarations()[decl.generated->target.index].qualifiedName},
        {"member", decl.generated->member},
        {"identity", decl.generated->identity},
        {"constructible", decl.generated->constructible}};
  }
  if (decl.construction) {
    for (StringRef key : {"abstract", "definition", "roles", "input_order",
                          "inputs", "outputs", "services", "effects"})
      result.erase(key);
    result["kind"] = "construction";
    const auto &construction = *decl.construction;
    const auto &target = project.declarations()[decl.target->index];
    json::Array arguments, rules;
    for (const auto &argument : decl.staticArguments)
      arguments.push_back(type(argument));
    result["target"] = json::Object{{"name", target.qualifiedName},
                                    {"arguments", std::move(arguments)}};
    result["provider"] = construction.provider
                             ? json::Value(type(*construction.provider))
                             : json::Value(nullptr);
    result["state"] = construction.state
                          ? json::Value(type(*construction.state))
                          : json::Value(nullptr);
    result["root"] =
        construction.root == ConstructionDefinition::Root::Local  ? "local"
        : construction.root == ConstructionDefinition::Root::Host ? "host"
                                                                  : "none";
    json::Array replaced;
    for (auto port : construction.services)
      replaced.push_back(target.services[port].name);
    result["replace"] = std::move(replaced);
    result["suite"] = construction.suite;
    result["format"] = protocol::proofFormatName(
        decl.proofFormat.value_or(protocol::ProofFormat::Native));
    if (construction.codec) {
      json::Array inputs;
      for (auto index : construction.codec->inputs)
        inputs.push_back(target.inputs[index].name);
      result["codec"] =
          json::Object{{"provider", type(construction.codec->provider)},
                       {"record", type(construction.codec->record)},
                       {"inputs", std::move(inputs)}};
    }
    result["base"] =
        construction.parent
            ? project.declarations()[construction.parent->index].qualifiedName
        : construction.base == ConstructionDefinition::Base::Native
            ? "fiat_shamir"
        : construction.base == ConstructionDefinition::Base::Authored
            ? "authored"
            : "";
    for (const auto &rule : construction.rules) {
      json::Array path, inputs;
      for (const auto &part : rule.path)
        path.push_back(part);
      for (auto input : rule.inputs)
        inputs.push_back(target.inputs[input].name);
      rules.push_back(json::Object{
          {"kind", protocol::constructionRuleName(rule.kind)},
          {"path", std::move(path)},
          {"inputs", std::move(inputs)},
          {"handler",
           project.declarations()[rule.handler.index].qualifiedName}});
    }
    result["rules"] = std::move(rules);
    json::Array applications;
    for (const auto &application : construction.applications) {
      json::Array path, arguments;
      for (const auto &part : application.path)
        path.push_back(part);
      for (const auto &argument : application.arguments)
        arguments.push_back(type(argument));
      applications.push_back(
          json::Object{{"construction",
                        project.declarations()[application.construction.index]
                            .qualifiedName},
                       {"arguments", std::move(arguments)},
                       {"path", std::move(path)}});
    }
    result["applications"] = std::move(applications);
    return result;
  }
  if (decl.primitive)
    result["primitive"] = decl.primitive->identity;
  if (decl.finiteDefinition)
    result["finite"] = *decl.finiteDefinition;
  if (domain || !decl.domainInputs.empty()) {
    json::Array domains;
    for (const auto &input : decl.domainInputs)
      domains.push_back(
          json::Object{{"name", input.name}, {"item", type(input.item)}});
    result["domain_inputs"] = std::move(domains);
    if (decl.domainResult)
      result["domain_result"] = type(*decl.domainResult);
    if (decl.domainDefinition && decl.domainDefinition->constructor)
      result["definition"] = "domain_constructor";
  }
  if (decl.effectAllowance || decl.abstract) {
    auto allowance = decl.effectAllowance.value_or(EffectSummary{});
    result["effect_allowance"] = renderEffects(allowance);
  }
  if (decl.kind == Declaration::Kind::Module ||
      decl.kind == Declaration::Kind::Interface) {
    for (StringRef key : {"abstract", "definition", "roles", "input_order",
                          "inputs", "scoped_inputs", "outputs", "services",
                          "effects", "effect_allowance"})
      result.erase(key);
    result["kind"] =
        decl.kind == Declaration::Kind::Module ? "module" : "interface";
    if (decl.implementation)
      result["implements"] = type(*decl.implementation);
    json::Array members;
    for (auto id : decl.members) {
      const auto &member = project.declarations()[id.index];
      if (member.isPublic && !member.anonymous)
        members.push_back(member.qualifiedName);
    }
    result["members"] = std::move(members);
  }
  if (owner) {
    json::Object parent{{"name", owner->qualifiedName},
                        {"kind", owner->kind == Declaration::Kind::Interface
                                     ? "interface"
                                     : "module"}};
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
          {"name", decl.entryName()},
          {"kind", decl.entryKind() == EntryKind::Proof      ? "proof"
                   : decl.entryKind() == EntryKind::Function ? "function"
                                                             : "run"}});
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
    if (project.sources()[decl.span.source.index].origin ==
        SourceOrigin::Installation)
      continue;
    if (decl.kind != Declaration::Kind::Math &&
        decl.kind != Declaration::Kind::Local &&
        decl.kind != Declaration::Kind::EntryFunction &&
        decl.kind != Declaration::Kind::DomainFunction &&
        decl.kind != Declaration::Kind::Protocol &&
        decl.kind != Declaration::Kind::Construction &&
        decl.kind != Declaration::Kind::Module &&
        decl.kind != Declaration::Kind::Interface)
      continue;
    if (decl.anonymous && decl.parent &&
        project.declarations()[decl.parent->index].kind ==
            Declaration::Kind::Construction)
      continue;
    const Declaration *owner = &decl;
    bool exposed = owner->isPublic;
    while (owner->parent) {
      owner = &project.declarations()[owner->parent->index];
      exposed &= owner->isPublic;
    }
    if (exposed)
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

Expected<std::string> inspectPublicAPI(const CheckedProject &project,
                                       const Limits &limits) {
  if (auto failure = checkLimits(limits))
    return std::move(failure);
  if (project.checkedWork() > limits.work ||
      project.checkedDeclarations() > limits.declarations ||
      project.checkedOperations() > limits.operations)
    return error("source.limit",
                 "checked project exceeds API inspection limits");
  const auto &records = project.storage->api;
  detail::Work work{limits};
  if (auto failure =
          work.charge(project.declarations().size() + records.exports.size() +
                      records.references.size()))
    return std::move(failure);
  auto name = [&](DeclarationId id) -> const std::string & {
    return project.declarations()[id.index].qualifiedName;
  };
  auto source = [&](Span span) -> const SourceBuffer & {
    return project.sources()[span.source.index];
  };
  auto location = [&](Span span) {
    return json::Object{{"module", source(span).module},
                        {"origin", source(span).origin == SourceOrigin::Captured
                                       ? "captured"
                                       : "installation"},
                        {"begin", span.begin},
                        {"end", span.end}};
  };
  std::vector<std::vector<unsigned>> exports(project.declarations().size());
  for (unsigned i = 0; i < records.exports.size(); ++i)
    exports[records.exports[i].owner.index].push_back(i);
  const auto &notationRecords = project.storage->notations;
  std::vector<std::vector<unsigned>> syntax(project.declarations().size());
  for (const auto &scope : notationRecords.scopes)
    if (scope.owner && !scope.body) {
      if (auto failure = work.charge(scope.exported.size() + 1))
        return std::move(failure);
      syntax[scope.owner->index] = scope.exported;
    }
  std::vector<unsigned> depth(project.declarations().size());
  std::vector<DeclarationId> reachable, roots;
  for (const auto &decl : project.declarations())
    if (!decl.parent && decl.kind == Declaration::Kind::Module &&
        source(decl.span).origin == SourceOrigin::Captured) {
      roots.push_back(decl.id);
      reachable.push_back(decl.id);
      depth[decl.id.index] = 1;
    }
  // Follow each graph node once, regardless of the number of public aliases.
  for (unsigned i = 0; i < reachable.size(); ++i) {
    auto id = reachable[i];
    if (depth[id.index] > limits.importDepth)
      return error("source.limit", "public API graph depth exceeded");
    for (auto edge : exports[id.index]) {
      if (auto failure = work.charge())
        return std::move(failure);
      auto target = records.exports[edge].target;
      if (!depth[target.index]) {
        depth[target.index] = depth[id.index] + 1;
        reachable.push_back(target);
      }
    }
    for (auto binding : syntax[id.index]) {
      if (auto failure = work.charge())
        return std::move(failure);
      auto target = notationRecords.bindings[binding].target;
      if (!depth[target.index]) {
        depth[target.index] = depth[id.index] + 1;
        reachable.push_back(target);
      }
    }
  }
  auto byName = [&](DeclarationId a, DeclarationId b) {
    return name(a) < name(b);
  };
  llvm::sort(roots, byName);
  llvm::sort(reachable, byName);
  std::vector<unsigned> edges, references;
  for (unsigned i = 0; i < records.exports.size(); ++i)
    if (depth[records.exports[i].owner.index])
      edges.push_back(i);
  llvm::sort(edges, [&](unsigned a, unsigned b) {
    const auto &x = records.exports[a], &y = records.exports[b];
    return std::tie(name(x.owner), x.name, name(x.target)) <
           std::tie(name(y.owner), y.name, name(y.target));
  });
  for (unsigned i = 0; i < records.references.size(); ++i)
    if (source(records.references[i].span).origin == SourceOrigin::Captured)
      references.push_back(i);
  auto key = [&](unsigned i) {
    const auto &r = records.references[i];
    return std::tie(name(r.owner), source(r.span).module, r.span.begin,
                    r.span.end, r.written, name(r.provider), name(r.target),
                    r.abstractModule);
  };
  llvm::sort(references,
             [&](unsigned a, unsigned b) { return key(a) < key(b); });
  references.erase(
      std::unique(references.begin(), references.end(),
                  [&](unsigned a, unsigned b) { return key(a) == key(b); }),
      references.end());
  std::string bytes;
  BoundedStream out(bytes, limits.apiInspectionBytes);
  json::OStream json(out);
  json.object([&] {
    json.attribute("format", "zkc.source-api/0");
    json.attributeArray("roots", [&] {
      for (auto id : roots)
        json.value(name(id));
    });
    json.attributeArray("exports", [&] {
      for (auto i : edges) {
        const auto &e = records.exports[i];
        json.value(json::Object{{"owner", name(e.owner)},
                                {"name", e.name},
                                {"target", name(e.target)},
                                {"imported", e.imported},
                                {"source", location(e.span)}});
        if (out.overflow())
          break;
      }
    });
    json.attributeArray("declarations", [&] {
      for (auto id : reachable) {
        if (out.overflow())
          break;
        const auto &decl = project.declarations()[id.index];
        auto value = describe(project, decl);
        for (auto &requirement : *value.getArray("requirements")) {
          auto *record = requirement.getAsObject();
          if (record->getString("kind") != "capability")
            continue;
          std::optional<std::string> selected;
          for (const auto &exported : protocol::sourceCapabilityExports())
            if (record->getString("predicate") == exported.predicate) {
              auto path = exported.module + "::" + exported.name;
              if (!selected || path < *selected)
                selected = std::move(path);
            }
          if (selected)
            (*record)["export"] = *selected;
        }
        value["requirements_written"] = records.writtenRequirements[id.index];
        value["effects_written"] = records.writtenEffects[id.index];
        auto dataKind = [&](StringRef kind) {
          for (StringRef key :
               {"definition", "roles", "input_order", "inputs", "scoped_inputs",
                "outputs", "services", "effects", "effect_allowance"})
            value.erase(key);
          value["kind"] = kind;
        };
        auto fields = [&](ArrayRef<TypeField> fields) {
          json::Array result;
          for (const auto &field : fields)
            if (field.isPublic)
              result.push_back(json::Object{{"name", field.name},
                                            {"type", formatType(field.type)}});
          return result;
        };
        switch (decl.kind) {
        case Declaration::Kind::Domain:
        case Declaration::Kind::Alias:
          dataKind(decl.kind == Declaration::Kind::Domain ? "domain" : "alias");
          value["type"] = formatType(decl.domain);
          break;
        case Declaration::Kind::Record:
        case Declaration::Kind::Variant: {
          dataKind(decl.kind == Declaration::Kind::Record ? "record"
                                                          : "variant");
          bool privateFields = llvm::any_of(
              decl.fields, [](const auto &f) { return !f.isPublic; });
          json::Array alternatives;
          for (const auto &alternative : decl.alternatives) {
            privateFields |= llvm::any_of(
                alternative.fields, [](const auto &f) { return !f.isPublic; });
            alternatives.push_back(
                json::Object{{"name", alternative.name},
                             {"fields", fields(alternative.fields)}});
          }
          value["constructor"] =
              decl.generated && !decl.generated->constructible ? "native"
              : decl.sealed || privateFields                   ? "owner"
                                                               : "public";
          value["private_fields"] = privateFields;
          value["fields"] = fields(decl.fields);
          if (decl.kind == Declaration::Kind::Variant)
            value["alternatives"] = std::move(alternatives);
          break;
        }
        case Declaration::Kind::Associated:
          dataKind("associated");
          value["sort"] =
              decl.associatedSort.empty() ? "Type" : decl.associatedSort;
          value["abstract"] = decl.abstract;
          value["representation"] = "private";
          if (decl.permissions)
            value["permissions"] = permissions(*decl.permissions);
          break;
        case Declaration::Kind::Relation: {
          value["kind"] = "relation";
          json::Array purposes;
          for (auto purpose : decl.relation->purposes)
            purposes.push_back(
                purpose == RelationPurpose::Parameter   ? "parameter"
                : purpose == RelationPurpose::Statement ? "statement"
                                                        : "witness");
          value["purposes"] = std::move(purposes);
          break;
        }
        case Declaration::Kind::EntryFunction:
          value["entry_kind"] = "function";
          break;
        case Declaration::Kind::Entry:
          dataKind("entry");
          value["entry_kind"] = decl.entryKind() == EntryKind::Proof ? "proof"
                                : decl.entryKind() == EntryKind::Function
                                    ? "function"
                                    : "run";
          break;
        default:
          break;
        }
        json.value(std::move(value));
      }
    });
    json.attributeArray("notations", [&] {
      for (auto owner : reachable) {
        auto bindings = syntax[owner.index];
        llvm::sort(bindings, [&](unsigned a, unsigned b) {
          const auto &x = notationRecords.bindings[a];
          const auto &y = notationRecords.bindings[b];
          return x.identity < y.identity;
        });
        for (auto id : bindings) {
          if (out.overflow())
            break;
          const auto &binding = notationRecords.bindings[id];
          const auto &descriptor =
              notationRecords.descriptors[binding.descriptor].descriptor;
          json::Array arguments;
          for (const auto &argument : binding.arguments)
            arguments.push_back(argument ? json::Value(*argument)
                                         : json::Value(nullptr));
          json::Object value{{"owner", name(owner)},
                             {"descriptor", descriptor.key()},
                             {"symbol", descriptor.symbol},
                             {"target", name(binding.target)},
                             {"arguments", std::move(arguments)},
                             {"source", location(binding.span)}};
          if (binding.module)
            value["abstract_module"] = *binding.module;
          json.value(std::move(value));
        }
      }
    });
    json.attributeArray("references", [&] {
      for (auto i : references) {
        if (out.overflow())
          break;
        const auto &r = records.references[i];
        json::Object value{
            {"owner", name(r.owner)},
            {"written", r.written},
            {"provider",
             source(project.declarations()[r.provider.index].span).module},
            {"provider_origin",
             source(project.declarations()[r.provider.index].span).origin ==
                     SourceOrigin::Captured
                 ? "captured"
                 : "installation"},
            {"target", name(r.target)},
            {"target_module",
             source(project.declarations()[r.target.index].span).module},
            {"source", location(r.span)}};
        if (r.abstractModule)
          value["abstract_module"] = *r.abstractModule;
        json.value(std::move(value));
      }
    });
  });
  if (out.overflow())
    return error("source.limit", "public API report byte limit exceeded");
  return bytes;
}
} // namespace zkc::language
