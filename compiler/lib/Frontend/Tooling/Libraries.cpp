#include "Libraries.h"
#include "../Resolution/Project.h"
#include "../Semantics/Libraries.h"

using namespace llvm;
namespace zkc::frontend::tooling {
namespace lib = library;
namespace {
json::Value declarationView(const lib::QualifiedDecl &d) {
  json::Array module;
  for (const auto &segment : d.module)
    module.push_back(segment);
  return json::Object{
      {"namespace", d.library.nameSpace}, {"library", d.library.name},
      {"version", d.library.version},     {"resolution", d.library.resolution},
      {"module", std::move(module)},      {"name", d.name}};
}
std::string displayName(const lib::QualifiedDecl &d) {
  std::string result;
  for (const auto &part : d.module)
    result += part + "::";
  return result + d.name;
}
json::Value staticView(const lib::StaticTerm &t) {
  static const char *kinds[] = {"root", "project", "apply", "natural", "seal"};
  json::Array arguments;
  for (const auto &a : t.arguments)
    arguments.push_back(staticView(a));
  return json::Object{{"kind", kinds[static_cast<unsigned>(t.kind)]},
                      {"declaration", declarationView(t.declaration)},
                      {"member", t.member},
                      {"natural", int64_t(t.number)},
                      {"arguments", std::move(arguments)}};
}
json::Value typeView(const lib::Type &t) {
  auto kind = [&]() -> StringRef {
    switch (t.kind) {
    case lib::Type::Kind::Logical:
      return "logical";
    case lib::Type::Kind::Parameter:
      return "parameter";
    case lib::Type::Kind::Abstract:
      return "abstract";
    case lib::Type::Kind::Product:
      return "product";
    case lib::Type::Kind::Record:
      return "record";
    case lib::Type::Kind::Array:
      return "array";
    case lib::Type::Kind::Variant:
      return "variant";
    }
    llvm_unreachable("unknown checked library type kind");
  }();
  json::Array arguments, elements, fields;
  for (const auto &a : t.arguments)
    arguments.push_back(staticView(a));
  for (const auto &e : t.elements)
    elements.push_back(typeView(e));
  for (const auto &f : t.fields)
    fields.push_back(f);
  return json::Object{{"kind", kind},
                      {"name", t.name},
                      {"declaration", declarationView(t.declaration)},
                      {"arguments", std::move(arguments)},
                      {"elements", std::move(elements)},
                      {"fields", std::move(fields)}};
}
json::Value placeView(const lib::Place &p) {
  json::Array path;
  for (auto index : p.path)
    path.push_back(int64_t(index));
  return json::Object{{"value", int64_t(p.value.index)},
                      {"path", std::move(path)}};
}
json::Value valueView(const lib::Value &v) {
  return json::Object{{"id", int64_t(v.id.index)},
                      {"type", typeView(v.port.type)},
                      {"role", v.port.role}};
}
json::Array importsView(const std::vector<lib::Import> &imports) {
  json::Array out;
  for (const auto &i : imports)
    out.push_back(json::Object{
        {"parameter", staticView(i.parameter)},
        {"interface", declarationView(i.interface.declaration().id)},
        {"interface_identity", i.interface.identity()},
        {"interface_fingerprint", i.interface.fingerprint()}});
  return out;
}
json::Array typeBoundsView(const std::vector<lib::TypeBound> &bounds) {
  json::Array out;
  for (const auto &b : bounds)
    out.push_back(json::Object{{"parameter", declarationView(b.parameter)},
                               {"copy", b.permissions.copy},
                               {"drop", b.permissions.drop}});
  return out;
}
json::Array
requirementsView(const std::vector<lib::Requirement> &requirements) {
  json::Array out;
  for (const auto &r : requirements) {
    json::Array arguments;
    for (const auto &a : r.arguments)
      arguments.push_back(staticView(a));
    out.push_back(json::Object{{"relation", r.relation},
                               {"arguments", std::move(arguments)}});
  }
  return out;
}
json::Value signatureView(const lib::Signature &s) {
  json::Array inputs, outputs, effects, requirements, ensures, labels;
  for (const auto &label : s.inputLabels)
    labels.push_back(label);
  for (const auto &p : s.inputs)
    inputs.push_back(
        json::Object{{"type", typeView(p.type)}, {"role", p.role}});
  for (const auto &p : s.outputs)
    outputs.push_back(
        json::Object{{"type", typeView(p.type)}, {"role", p.role}});
  for (const auto &e : s.effects)
    effects.push_back(e);
  auto predicates = [](const auto &rs, auto &out) {
    for (const auto &r : rs) {
      json::Array terms;
      for (const auto &t : r.arguments)
        terms.push_back(staticView(t));
      out.push_back(json::Object{{"relation", r.relation},
                                 {"arguments", std::move(terms)}});
    }
  };
  predicates(s.preconditions, requirements);
  predicates(s.postconditions, ensures);
  return json::Object{{"inputs", std::move(inputs)},
                      {"input_labels", std::move(labels)},
                      {"outputs", std::move(outputs)},
                      {"effects", std::move(effects)},
                      {"requires", std::move(requirements)},
                      {"ensures", std::move(ensures)}};
}
json::Value substitutionView(const lib::Substitution &s) {
  json::Array statics, types;
  for (const auto &[parameter, argument] : s.statics)
    statics.push_back(json::Object{{"parameter", staticView(parameter)},
                                   {"argument", staticView(argument)}});
  for (const auto &[parameter, argument] : s.types)
    types.push_back(json::Object{{"parameter", declarationView(parameter)},
                                 {"argument", typeView(argument)}});
  return json::Object{{"statics", std::move(statics)},
                      {"types", std::move(types)}};
}
template <class B> json::Value bodyView(const B &b) {
  json::Array inputs, instructions, returns;
  for (const auto &v : b.inputs)
    inputs.push_back(valueView(v));
  for (const auto &p : b.returns)
    returns.push_back(placeView(p));
  for (const auto &i : b.instructions) {
    json::Object instruction;
    if (const auto *c = std::get_if<lib::Call>(&i)) {
      instruction["kind"] = "call";
      instruction["role"] = c->role;
      json::Array args, results, attributes;
      for (const auto &p : c->inputs)
        args.push_back(placeView(p));
      for (const auto &v : c->outputs)
        results.push_back(valueView(v));
      for (const auto &a : c->attributes)
        attributes.push_back(a);
      instruction["inputs"] = std::move(args);
      instruction["outputs"] = std::move(results);
      instruction["attributes"] = std::move(attributes);
      if (const auto *m = std::get_if<lib::MemberCall>(&c->target))
        instruction["target"] = json::Object{
            {"component", staticView(m->component)}, {"member", m->member}};
      else if (const auto *logical =
                   std::get_if<lib::LogicalCall>(&c->target)) {
        const auto &l = *logical;
        json::Array terms;
        for (const auto &a : l.arguments)
          terms.push_back(staticView(a));
        instruction["target"] = json::Object{{"operation", l.operation},
                                             {"arguments", std::move(terms)}};
      } else {
        const auto &call = std::get<lib::SourceCall>(c->target);
        instruction["target"] = json::Object{
            {"function", declarationView(call.callable.declaration().id)},
            {"interface_identity", call.callable.identity()},
            {"signature", signatureView(call.callable.declaration().signature)},
            {"substitutions", substitutionView(call.arguments)}};
      }
    } else if (const auto *c = std::get_if<lib::Construct>(&i)) {
      instruction["kind"] = "construct";
      instruction["output"] = valueView(c->output);
      json::Array elements;
      for (const auto &p : c->elements)
        elements.push_back(placeView(p));
      instruction["elements"] = std::move(elements);
    } else if (const auto *p = std::get_if<lib::Project>(&i)) {
      instruction["kind"] = "project";
      instruction["input"] = placeView(p->input);
      instruction["output"] = valueView(p->output);
    } else if (const auto *drop = std::get_if<lib::Drop>(&i)) {
      instruction["kind"] = "drop";
      instruction["input"] = placeView(drop->input);
    } else if (const auto *stop = std::get_if<lib::Stop>(&i)) {
      instruction["kind"] = "stop";
      instruction["reason"] = stop->reason;
    } else if (const auto *construct = std::get_if<lib::VariantConstruct>(&i)) {
      instruction["kind"] = "variant";
      instruction["output"] = valueView(construct->output);
      instruction["alternative"] = construct->alternative;
      instruction["payload"] = placeView(construct->payload);
    } else if (const auto *match = lib::branches(i)) {
      instruction["kind"] =
          std::holds_alternative<lib::Conditional>(i) ? "conditional" : "match";
      instruction["input"] = placeView(match->input);
      instruction["role"] = match->role;
      json::Array captures, outputs, arms;
      for (const auto &p : match->captures)
        captures.push_back(placeView(p));
      for (const auto &v : match->outputs)
        outputs.push_back(valueView(v));
      for (const auto &arm : match->arms)
        arms.push_back(json::Object{{"alternative", arm.alternative},
                                    {"body", bodyView(*arm.body)}});
      instruction["captures"] = std::move(captures);
      instruction["outputs"] = std::move(outputs);
      instruction["arms"] = std::move(arms);
    } else if (const auto *loop = std::get_if<lib::ArrayTraversal>(&i)) {
      instruction["kind"] = "array_traversal";
      instruction["input"] = placeView(loop->input);
      instruction["role"] = loop->role;
      json::Array initial, captures, outputs;
      for (const auto &p : loop->initial)
        initial.push_back(placeView(p));
      for (const auto &p : loop->captures)
        captures.push_back(placeView(p));
      for (const auto &v : loop->outputs)
        outputs.push_back(valueView(v));
      instruction["initial"] = std::move(initial);
      instruction["captures"] = std::move(captures);
      instruction["outputs"] = std::move(outputs);
      instruction["body"] = bodyView(*loop->body);
      instruction["collected"] =
          loop->collected ? valueView(*loop->collected) : json::Value(nullptr);
    }
    instructions.push_back(std::move(instruction));
  }
  json::Object result{{"inputs", std::move(inputs)},
                      {"instructions", std::move(instructions)},
                      {"returns", std::move(returns)}};
  if constexpr (std::is_same_v<B, lib::Body>) {
    result["declaration"] = declarationView(b.id);
    result["signature"] = signatureView(b.signature);
  }
  return result;
}
json::Value layoutLeafView(const lib::LayoutLeaf &leaf) {
  json::Array path, alternatives;
  for (auto index : leaf.path)
    path.push_back(int64_t(index));
  for (const auto &alternative : leaf.alternatives) {
    json::Array payload;
    for (const auto &child : alternative)
      payload.push_back(layoutLeafView(child));
    alternatives.push_back(std::move(payload));
  }
  return json::Object{{"kind", leaf.kind == lib::LayoutLeaf::Kind::ResourceUnit
                                   ? "resource_unit"
                               : leaf.kind == lib::LayoutLeaf::Kind::Variant
                                   ? "variant"
                                   : "logical"},
                      {"type", typeView(leaf.type)},
                      {"resource_identity", leaf.resourceIdentity},
                      {"variant_identity", leaf.variantIdentity},
                      {"alternatives", std::move(alternatives)},
                      {"copy", leaf.permissions.copy},
                      {"drop", leaf.permissions.drop},
                      {"path", std::move(path)}};
}
} // namespace
json::Value inspectLibraries(const semantics::LibraryReport &report,
                             const resolution::Context *context) {
  auto readable = [&](StringRef name) {
    if (context)
      if (const auto *d = context->lookup(name))
        return displayName(d->identity);
    return name.str();
  };
  json::Array interfaces, clients, components, componentBodies, links,
      associations;
  for (const auto &a : report.associations)
    associations.push_back(json::Object{{"name", a.name},
                                        {"display_name", readable(a.name)},
                                        {"kind", a.kind},
                                        {"subject", a.subject}});
  for (const auto &[name, interface] : report.interfaces) {
    json::Array types, statics, functions, facets;
    const auto &d = interface.declaration();
    for (const auto &t : d.types)
      types.push_back(json::Object{{"name", t.name},
                                   {"copy", t.permissions.copy},
                                   {"drop", t.permissions.drop}});
    static const char *sortNames[] = {"type", "domain", "natural",
                                      "association", "component"};
    for (const auto &s : d.statics)
      statics.push_back(
          json::Object{{"name", s.name},
                       {"sort", sortNames[static_cast<unsigned>(s.sort.kind)]},
                       {"domain", s.sort.domain},
                       {"equation", s.equation ? staticView(*s.equation)
                                               : json::Value(nullptr)}});
    for (const auto &[n, s] : d.functions)
      functions.push_back(
          json::Object{{"name", n}, {"signature", signatureView(s)}});
    for (const auto &f : d.facets)
      facets.push_back(json::Object{
          {"owner", f.owner}, {"name", f.name}, {"required", f.required}});
    interfaces.push_back(
        json::Object{{"name", name},
                     {"display_name", displayName(d.id)},
                     {"state", "formed"},
                     {"identity", interface.identity()},
                     {"fingerprint", interface.fingerprint()},
                     {"declaration", declarationView(d.id)},
                     {"self", staticView(d.self)},
                     {"types", std::move(types)},
                     {"statics", std::move(statics)},
                     {"functions", std::move(functions)},
                     {"type_bounds", typeBoundsView(d.typeBounds)},
                     {"requirements", requirementsView(d.requirements)},
                     {"facets", std::move(facets)}});
  }
  for (const auto &[name, checked] : report.components) {
    const auto &d = checked.declaration();
    json::Array representations, statics, functions;
    for (const auto &[name, type] : d.representations)
      representations.push_back(
          json::Object{{"name", name}, {"type", typeView(type)}});
    for (const auto &[name, term] : d.statics)
      statics.push_back(
          json::Object{{"name", name}, {"value", staticView(term)}});
    for (const auto &[name, body] : d.functions)
      functions.push_back(
          json::Object{{"name", name}, {"fingerprint", body.fingerprint()}});
    components.push_back(json::Object{
        {"name", name},
        {"display_name", readable(name)},
        {"state", "checked_parametric"},
        {"fingerprint", checked.fingerprint()},
        {"interface", declarationView(d.interface.declaration().id)},
        {"interface_fingerprint", d.interface.fingerprint()},
        {"imports", importsView(d.imports)},
        {"type_bounds", typeBoundsView(d.typeBounds)},
        {"requirements", requirementsView(d.requirements)},
        {"representations", std::move(representations)},
        {"statics", std::move(statics)},
        {"functions", std::move(functions)}});
  }
  auto bodies = [](const auto &bodies, auto &out) {
    for (const auto &[name, checked] : bodies) {
      out.push_back(json::Object{
          {"name", name},
          {"display_name", displayName(checked.body().id)},
          {"declaration", declarationView(checked.body().id)},
          {"state", "checked"},
          {"identity", checked.identity()},
          {"fingerprint", checked.fingerprint()},
          {"imports", importsView(checked.imports())},
          {"type_bounds", typeBoundsView(checked.body().typeBounds)},
          {"obligations", requirementsView(checked.obligations())},
          {"body", bodyView(checked.body())}});
    }
  };
  bodies(report.clients, clients);
  bodies(report.componentBodies, componentBodies);
  for (const auto &[name, linked] : report.links) {
    json::Array dependencies, evidence, functions;
    for (const auto &d : linked.dependencies()) {
      json::Array paths, children;
      for (const auto &p : d.paths)
        paths.push_back(p);
      for (const auto &child : d.dependencies)
        children.push_back(child);
      dependencies.push_back(json::Object{
          {"selection", d.selection},
          {"normalized_selection", d.normalizedSelection},
          {"interface_identity", d.interfaceIdentity},
          {"implementation_identity", d.implementationIdentity},
          {"capture_identity", d.captureIdentity},
          {"capture_fingerprint", d.captureFingerprint},
          {"dependencies", std::move(children)},
          {"interface_fingerprint", d.interfaceFingerprint},
          {"implementation_fingerprint", d.implementationFingerprint},
          {"paths", std::move(paths)}});
    }
    for (const auto &e : linked.evidence()) {
      static const char *states[] = {"established", "accepted_premise",
                                     "unavailable", "refuted"};
      evidence.push_back(
          json::Object{{"owner", e.facet.owner},
                       {"name", e.facet.name},
                       {"required", e.facet.required},
                       {"state", states[static_cast<unsigned>(e.state)]},
                       {"subject", e.subject},
                       {"owner_version", e.ownerVersion},
                       {"explanation", e.explanation}});
    }
    for (const auto &f : linked.functions()) {
      json::Array layouts, calls;
      for (const auto &[path, call] : f.calls) {
        json::Array indices;
        for (auto index : path)
          indices.push_back(int64_t(index));
        calls.push_back(json::Object{{"path", std::move(indices)},
                                     {"target", call.target},
                                     {"logical", call.logical}});
      }
      for (const auto &[value, layout] : f.values) {
        json::Array leaves;
        for (const auto &leaf : layout.leaves)
          leaves.push_back(layoutLeafView(leaf));
        layouts.push_back(
            json::Object{{"value", int64_t(value)},
                         {"source_type", typeView(layout.sourceType)},
                         {"concrete_type", typeView(layout.concreteType)},
                         {"leaves", std::move(leaves)}});
      }
      functions.push_back(
          json::Object{{"symbol", f.symbol},
                       {"display_name", displayName(f.body.id)},
                       {"exact_subject", f.exactSubject},
                       {"logical_signature", signatureView(f.logicalSignature)},
                       {"body", bodyView(f.body)},
                       {"linked_calls", std::move(calls)},
                       {"layouts", std::move(layouts)}});
    }
    links.push_back(json::Object{{"name", name},
                                 {"display_name", readable(name)},
                                 {"state", "linked"},
                                 {"entry", linked.entry()},
                                 {"fingerprint", linked.fingerprint()},
                                 {"identity", linked.identity()},
                                 {"dependencies", std::move(dependencies)},
                                 {"evidence", std::move(evidence)},
                                 {"functions", std::move(functions)}});
  }
  return json::Object{
      {"associations", std::move(associations)},
      {"query_state", "retained_checked_capabilities"},
      {"interfaces", std::move(interfaces)},
      {"clients", std::move(clients)},
      {"components", std::move(components)},
      {"component_bodies", std::move(componentBodies)},
      {"links", std::move(links)},
      {"unselected_component_conformance", "checked_parametric"},
      {"pir_admission", "not_requested"},
      {"runtime_readiness", "not_requested"},
      {"decision_result_usage", "unavailable_no_decision_metadata"},
      {"acceptance_dependence", "not_analyzed"},
      {"cryptographic_soundness", "not_claimed"},
      {"effect_profile", "local includes all installed primitives, guards and "
                         "provider work; finer effects remain PIR-owned"}};
}

} // namespace zkc::frontend::tooling
