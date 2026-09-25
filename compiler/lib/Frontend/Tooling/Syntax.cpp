#include "../Syntax/Tree.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Source/Codec.h"
using namespace llvm;
namespace zkc::frontend {
Error checkProtocolSyntax(StringRef text, StringRef filename) {
  if (text.ltrim().starts_with("[")) {
    auto document = parseProtocolDocument(text, filename);
    return document ? Error::success() : document.takeError();
  }
  auto content = syntax::parse(text, filename);
  return content ? Error::success() : content.takeError();
}

Expected<json::Value> inspectProtocolSyntax(StringRef text,
                                            StringRef filename) {
  if (text.ltrim().starts_with("[")) {
    auto document = parseProtocolDocument(text, filename);
    if (!document)
      return document.takeError();
    return json::Value(
        json::Object{{"kind", "syntax-inspection"},
                     {"format", "common-source-json"},
                     {"content", source::encode(document->root())}});
  }
  auto content = syntax::parse(text, filename);
  if (!content)
    return content.takeError();
  return syntax::inspect(*content);
}

namespace {
json::Array inspectNames(const source::Names &names) {
  json::Array result;
  for (const auto &name : names)
    result.push_back(name);
  return result;
}
json::Array inspectAssignments(const source::Assignments &pairs) {
  json::Array result;
  for (const auto &[name, value] : pairs)
    result.push_back(json::Object{{"name", name}, {"value", value}});
  return result;
}
json::Array inspectAssignments(const source::ParameterBindings &pairs) {
  json::Array result;
  for (const auto &[name, value] : pairs) {
    if (const auto *constant = std::get_if<std::string>(&value))
      result.push_back(json::Object{{"name", name}, {"value", *constant}});
    else {
      const auto &ingress = std::get<source::FamilyIngress>(value);
      json::Array selectors;
      for (const auto &s : ingress.selectors)
        selectors.push_back(
            json::Object{{"role", s.role},
                         {"function", s.function},
                         {"arguments", inspectNames(s.arguments)}});
      result.push_back(json::Object{
          {"name", name},
          {"ingress", json::Object{{"bound", ingress.bound},
                                   {"selectors", std::move(selectors)}}}});
    }
  }
  return result;
}
json::Object located(json::Object object, const source::Node &node) {
  if (node.location)
    object["span"] = json::Object{{"offset", int64_t(node.location->offset)},
                                  {"length", int64_t(node.location->length)}};
  return object;
}
json::Object inspectType(const syntax::Type &type) {
  json::Array arguments;
  for (const auto &argument : type.arguments)
    arguments.push_back(inspectType(argument));
  return located(
      json::Object{{"kind", type.product ? "product-type" : "type-expression"},
                   {"name", type.name},
                   {"arguments", std::move(arguments)},
                   {"members", inspectNames(type.members)},
                   {"natural", type.natural}},
      type);
}
json::Array inspectTypes(const std::vector<syntax::Type> &types) {
  json::Array result;
  for (const auto &type : types)
    result.push_back(inspectType(type));
  return result;
}
json::Array inspectBody(const syntax::Body &body);
json::Object inspectExpression(const syntax::Expression &expression) {
  json::Array operands;
  for (const auto &operand : expression.operands)
    operands.push_back(inspectExpression(operand));
  auto kind = [](syntax::Expression::Kind kind) -> StringRef {
    using K = syntax::Expression::Kind;
    switch (kind) {
    case K::Name:
      return "name";
    case K::Index:
      return "index";
    case K::Boolean:
      return "boolean";
    case K::Call:
      return "call";
    case K::Vector:
      return "vector";
    case K::Get:
      return "get";
    case K::Length:
      return "length";
    case K::Struct:
      return "struct";
    case K::Product:
      return "product";
    case K::Operator:
      return "operator";
    case K::Map:
      return "map";
    case K::Fold:
      return "fold";
    }
    llvm_unreachable("unhandled expression kind");
  };
  json::Object result{{"kind", kind(expression.kind)},
                      {"name", expression.name},
                      {"qualified", expression.qualified},
                      {"argumentNames", inspectNames(expression.argumentNames)},
                      {"operands", std::move(operands)},
                      {"attributes", inspectNames(expression.attributes)}};
  if (expression.kind == syntax::Expression::Kind::Struct)
    result["fields"] = inspectNames(expression.fields);
  if (expression.traversal)
    result["traversal"] =
        json::Object{{"state", expression.traversal->state},
                     {"element", expression.traversal->element},
                     {"captures", inspectNames(expression.traversal->captures)},
                     {"body", inspectBody(expression.traversal->body)}};
  result["staticArguments"] =
      expression.staticArguments
          ? json::Value(inspectNames(*expression.staticArguments))
          : json::Value(nullptr);
  return located(std::move(result), expression);
}
json::Array inspectBody(const syntax::Body &body) {
  json::Array result;
  for (const auto &instruction : body) {
    json::Object object{{"site", instruction.site}};
    std::visit(
        [&](const auto &value) {
          using T = std::decay_t<decltype(value)>;
          if constexpr (std::is_same_v<T, syntax::Call>) {
            object["kind"] =
                value.isOperator ? "unresolved-operator" : "unresolved-call";
            object["callee"] = value.callee;
            object["destructure"] = value.destructure;
            object["argumentNames"] = inspectNames(value.argumentNames);
            object["qualified"] = value.qualified;
            // Null distinguishes omission from an explicitly authored empty
            // ::<>.
            object["staticArguments"] =
                value.staticArguments
                    ? json::Value(inspectNames(*value.staticArguments))
                    : json::Value(nullptr);
            object["annotation"] =
                value.annotation ? json::Value(inspectTypes(*value.annotation))
                                 : json::Value(nullptr);
            object["role"] =
                value.role ? json::Value(*value.role) : json::Value(nullptr);
            object["inputs"] = inspectNames(value.inputs);
            object["outputs"] = inspectNames(value.outputs);
            object["attributes"] = inspectNames(value.attributes);
            if (value.location)
              object["callSpan"] =
                  json::Object{{"offset", int64_t(value.location->offset)},
                               {"length", int64_t(value.location->length)}};
          } else if constexpr (std::is_same_v<T, syntax::Binding>) {
            object["kind"] = "binding";
            object["outputs"] = inspectNames(value.outputs);
            object["destructure"] = value.destructure;
            object["mutable"] = value.mutableBinding;
            object["assignment"] = value.assignment;
            object["expression"] = inspectExpression(value.expression);
            if (value.annotation) {
              json::Array types;
              for (const auto &type : *value.annotation)
                types.push_back(inspectType(type));
              object["annotation"] = std::move(types);
            }
          } else if constexpr (std::is_same_v<T, syntax::Conditional>) {
            object["kind"] = "if";
            object["condition"] = inspectExpression(value.condition);
            object["explicitRegion"] = value.explicitRegion;
            object["captures"] = inspectNames(value.captures);
            object["outputs"] = inspectNames(value.outputs);
            object["then"] = inspectBody(value.thenBody);
            object["else"] = inspectBody(value.elseBody);
          } else if constexpr (std::is_same_v<T, syntax::For>) {
            object["kind"] = "for";
            object["induction"] = value.induction;
            object["lower"] = inspectExpression(value.lower);
            object["upper"] = inspectExpression(value.upper);
            object["explicitRegion"] = value.explicitRegion;
            object["carried"] = inspectAssignments(value.carried);
            object["captures"] = inspectNames(value.captures);
            object["outputs"] = inspectNames(value.outputs);
            object["body"] = inspectBody(value.body);
          } else if constexpr (std::is_same_v<T, syntax::Match>) {
            object["kind"] = "match";
            object["input"] = value.input;
            object["captures"] = inspectNames(value.captures);
            object["outputs"] = inspectNames(value.outputs);
            json::Array arms;
            for (const auto &arm : value.arms)
              arms.push_back(
                  located(json::Object{{"alternative", arm.alternative},
                                       {"payload", inspectNames(arm.payload)},
                                       {"body", inspectBody(arm.body)}},
                          arm));
            object["arms"] = std::move(arms);
          } else if constexpr (std::is_same_v<T, syntax::ArrayTraversal>) {
            object["kind"] = "array_traversal";
            object["element"] = value.element;
            object["input"] = value.input;
            object["carried"] = inspectAssignments(value.carried);
            object["captures"] = inspectNames(value.captures);
            object["outputs"] = inspectNames(value.outputs);
            object["body"] = inspectBody(value.body);
          } else if constexpr (std::is_same_v<T, syntax::Invocation>) {
            object["kind"] = "invoke";
            object["callee"] = value.callee;
            object["inputs"] = inspectNames(value.inputs);
            object["outputs"] = inspectNames(value.outputs);
            object["resultNames"] = inspectNames(value.resultNames);
          } else if constexpr (std::is_same_v<T, syntax::Finish>) {
            object["kind"] = "finish";
            object["ports"] = inspectAssignments(value.values);
          } else if constexpr (std::is_same_v<T, source::Message>) {
            object["kind"] = "message";
            object["schema"] = value.schema;
            object["sender"] = value.sender;
            object["receiver"] = value.receiver;
            object["input"] = value.input;
            object["output"] = value.output;
          } else if constexpr (std::is_same_v<T, syntax::Placement>) {
            object["kind"] = "placement";
            object["destructure"] = value.destructure;
            object["annotation"] =
                value.annotation ? json::Value(inspectType(*value.annotation))
                                 : json::Value(nullptr);
            object["role"] = value.role;
            object["outputs"] = inspectNames(value.outputs);
            object["body"] = inspectBody(value.body);
          } else if constexpr (std::is_same_v<T, syntax::Exit>) {
            object["kind"] = "return";
            object["expression"] = inspectExpression(value.expression);
          } else if constexpr (std::is_same_v<T, source::Return> ||
                               std::is_same_v<T, source::Yield>) {
            object["kind"] =
                std::is_same_v<T, source::Return> ? "return" : "yield";
            object["values"] = inspectNames(value.values);
          } else if constexpr (std::is_same_v<T, source::Stop>) {
            object["kind"] = "stop";
            object["role"] = value.role;
            object["reason"] = value.reason;
          } else if constexpr (std::is_same_v<T, syntax::Loop>) {
            object["kind"] = "loop";
            object["count"] = json::Object{
                {"kind", value.count.kind == source::LoopCount::Kind::Constant
                             ? "constant"
                             : "parameter"},
                {"value", value.count.value}};
            object["carried"] = inspectAssignments(value.carried);
            object["captures"] = inspectNames(value.captures);
            object["outputs"] = inspectNames(value.outputs);
            object["body"] = inspectBody(value.body);
          }
        },
        instruction.value);
    result.push_back(located(std::move(object), instruction));
  }
  return result;
}
json::Object inspectLibraryTerm(const syntax::LibraryTerm &t) {
  json::Array args;
  for (const auto &a : t.arguments)
    args.push_back(inspectLibraryTerm(a));
  return located(
      json::Object{
          {"root", t.root.value},
          {"rootKind", t.root.kind == syntax::Atom::Kind::Number   ? "natural"
                       : t.root.kind == syntax::Atom::Kind::String ? "identity"
                                                                   : "name"},
          {"applied", t.applied},
          {"arguments", std::move(args)},
          {"members", inspectNames(t.members)}},
      t);
}
json::Object inspectModule(const syntax::Module &module) {
  json::Array modules, dependencies, uses;
  for (const auto &m : module.modules)
    modules.push_back(located(json::Object{{"name", m.name}}, m));
  for (const auto &d : module.dependencies)
    dependencies.push_back(
        located(json::Object{{"alias", d.name},
                             {"namespace", d.identity.nameSpace},
                             {"name", d.identity.name},
                             {"version", d.identity.version},
                             {"resolution", d.identity.resolution}},
                d));
  for (const auto &u : module.uses)
    uses.push_back(located(json::Object{{"path", inspectNames(u.path)},
                                        {"name", u.name},
                                        {"exported", u.exported}},
                           u));
  json::Array libraryIdentities, libraryAssociations, libraryInterfaces,
      libraryComponents, libraryLinks, librarySelections;
  for (const auto &a : module.libraryAssociations)
    libraryAssociations.push_back(
        located(json::Object{{"name", a.name}, {"captured", a.captured}}, a));
  for (const auto &i : module.libraryIdentities)
    libraryIdentities.push_back(
        located(json::Object{{"namespace", i.nameSpace},
                             {"name", i.name},
                             {"version", i.version},
                             {"resolution", i.resolution}},
                i));
  auto libraryMembers = [&](const syntax::LibraryInterface &i) {
    json::Array types, statics, facets;
    for (const auto &f : i.facets)
      facets.push_back(located(json::Object{{"owner", f.owner},
                                            {"name", f.name},
                                            {"required", f.required}},
                               f));
    for (const auto &t : i.types)
      types.push_back(located(
          json::Object{{"name", t.name},
                       {"copy", t.copy},
                       {"drop", t.drop},
                       {"representation",
                        t.representation
                            ? json::Value(inspectType(*t.representation))
                            : json::Value(nullptr)}},
          t));
    for (const auto &m : i.statics)
      statics.push_back(located(
          json::Object{{"name", m.name},
                       {"sort", m.sort},
                       {"domain", m.domain},
                       {"equation", m.equation ? json::Value(inspectLibraryTerm(
                                                     *m.equation))
                                               : json::Value(nullptr)}},
          m));
    syntax::Module functions;
    functions.functions = i.functions;
    auto inspected = inspectModule(functions);
    return located(json::Object{{"name", i.name},
                                {"types", std::move(types)},
                                {"statics", std::move(statics)},
                                {"facets", std::move(facets)},
                                {"functions",
                                 std::move(*inspected.getArray("functions"))}},
                   i);
  };
  for (const auto &i : module.libraryInterfaces)
    libraryInterfaces.push_back(libraryMembers(i));
  for (const auto &c : module.libraryComponents) {
    auto object = libraryMembers(c);
    object["interface"] = c.interface;
    json::Array parameters;
    for (const auto &p : c.parameters)
      parameters.push_back(
          located(json::Object{{"name", p.name},
                               {"sort", p.sort ? json::Value(*p.sort)
                                               : json::Value(nullptr)},
                               {"bounds", inspectNames(p.bounds)}},
                  p));
    object["parameters"] = std::move(parameters);
    libraryComponents.push_back(std::move(object));
  }
  for (const auto &a : module.librarySelections)
    librarySelections.push_back(
        located(json::Object{{"name", a.name},
                             {"sealed", a.sealed},
                             {"target", inspectLibraryTerm(a.target)}},
                a));
  for (const auto &l : module.libraryLinks) {
    json::Array args;
    for (const auto &a : l.arguments)
      args.push_back(inspectLibraryTerm(a));
    libraryLinks.push_back(located(json::Object{{"name", l.name},
                                                {"client", l.client},
                                                {"arguments", std::move(args)}},
                                   l));
  }

  json::Array enums;
  for (const auto &enumeration : module.enums) {
    json::Array alternatives, parameters;
    for (const auto &alternative : enumeration.alternatives)
      alternatives.push_back(json::Object{
          {"name", alternative.name}, {"type", inspectType(alternative.type)}});
    for (const auto &parameter : enumeration.parameters)
      parameters.push_back(
          json::Object{{"name", parameter.name},
                       {"bounds", inspectNames(parameter.bounds)},
                       {"sort", parameter.sort ? json::Value(*parameter.sort)
                                               : json::Value(nullptr)}});
    enums.push_back(
        located(json::Object{{"name", enumeration.name},
                             {"parameters", std::move(parameters)},
                             {"alternatives", std::move(alternatives)}},
                enumeration));
  }
  json::Array bindings, bundles, structs, functions, protocols, configurations,
      instances, entries, imports, views, constants;
  for (const auto &c : module.constants)
    constants.push_back(
        located(json::Object{{"name", c.name},
                             {"expression", inspectExpression(c.expression)}},
                c));
  for (const auto &r : module.imports)
    imports.push_back(located(
        json::Object{{"name", r.name}, {"family", r.family}, {"path", r.path}},
        r));
  for (const auto &v : module.relationViews)
    views.push_back(located(json::Object{{"name", v.name},
                                         {"relation", v.relation},
                                         {"kind", v.kind},
                                         {"staging", v.staging},
                                         {"height", v.height}},
                            v));
  for (const auto &binding : module.bindings)
    bindings.push_back(located(
        json::Object{{"name", binding.name},
                     {"contract", binding.contract},
                     {"staticArguments", inspectNames(binding.arguments)},
                     {"implementation", binding.implementation}},
        binding));
  for (const auto &structure : module.structs) {
    json::Array parameters, fields;
    for (const auto &parameter : structure.parameters)
      parameters.push_back(located(
          json::Object{{"name", parameter.name},
                       {"sort", parameter.sort ? json::Value(*parameter.sort)
                                               : json::Value(nullptr)},
                       {"bounds", inspectNames(parameter.bounds)}},
          parameter));
    for (const auto &field : structure.fields)
      fields.push_back(json::Object{{"name", field.name},
                                    {"type", inspectType(field.type)}});
    structs.push_back(located(
        json::Object{{"name", structure.name},
                     {"checked", structure.checked},
                     {"parameters", std::move(parameters)},
                     {"fields", std::move(fields)},
                     {"constructors", inspectNames(structure.constructors)}},
        structure));
  }
  for (const auto &bundle : module.bundles) {
    json::Array requirements;
    for (const auto &requirement : bundle.requirements)
      requirements.push_back(located(
          json::Object{{"predicate", requirement.predicate},
                       {"arguments", inspectNames(requirement.arguments)}},
          requirement));
    bundles.push_back(
        located(json::Object{{"name", bundle.name},
                             {"parameters", inspectNames(bundle.parameters)},
                             {"requirements", std::move(requirements)}},
                bundle));
  }
  for (const auto &function : module.functions) {
    json::Array parameters, requirements, arguments;
    for (const auto &parameter : function.parameters)
      parameters.push_back(located(
          json::Object{{"name", parameter.name},
                       {"sort", parameter.sort ? json::Value(*parameter.sort)
                                               : json::Value(nullptr)},
                       {"bounds", inspectNames(parameter.bounds)}},
          parameter));
    for (const auto &requirement : function.requirements)
      requirements.push_back(located(
          json::Object{{"predicate", requirement.predicate},
                       {"arguments", inspectNames(requirement.arguments)}},
          requirement));
    for (const auto &argument : function.arguments)
      arguments.push_back(json::Object{{"name", argument.name},
                                       {"type", inspectType(argument.type)}});
    json::Object object{
        {"kind", function.generic ? "generic-function" : "function"},
        {"name", function.name},
        {"parameters", std::move(parameters)},
        {"requirements", std::move(requirements)},
        {"arguments", std::move(arguments)},
        {"results", inspectTypes(function.results)},
        {"effects", inspectNames(function.effects)},
        {"body", function.body ? json::Value(inspectBody(*function.body))
                               : json::Value(nullptr)}};
    object["origin"] =
        function.origin ? json::Value(json::Object{
                              {"definition", function.origin->definition},
                              {"arguments",
                               inspectAssignments(function.origin->arguments)}})
                        : json::Value(nullptr);
    functions.push_back(located(std::move(object), function));
  }
  for (const auto &protocol : module.protocols) {
    json::Array arguments, results, dependencies, staticParameters,
        requirements;
    for (const auto &p : protocol.staticParameters)
      staticParameters.push_back(
          located(json::Object{{"name", p.name},
                               {"sort", p.sort ? json::Value(*p.sort)
                                               : json::Value(nullptr)},
                               {"bounds", inspectNames(p.bounds)}},
                  p));
    for (const auto &r : protocol.requirements)
      requirements.push_back(
          located(json::Object{{"predicate", r.predicate},
                               {"arguments", inspectNames(r.arguments)}},
                  r));
    for (const auto &argument : protocol.arguments)
      arguments.push_back(json::Object{{"name", argument.name},
                                       {"role", argument.role},
                                       {"type", inspectType(argument.type)}});
    for (const auto &result : protocol.results)
      results.push_back(json::Object{{"role", result.role},
                                     {"name", result.name},
                                     {"type", inspectType(result.type)}});
    for (const auto &dependency : protocol.dependencies) {
      json::Object object{
          {"name", dependency.name},
          {"protocol", dependency.protocol},
          {"agreements", inspectAssignments(dependency.agreements)}};
      if (auto it = protocol.dependencyArguments.find(dependency.name);
          it != protocol.dependencyArguments.end())
        object["domainArguments"] = inspectAssignments(it->second.arguments);
      dependencies.push_back(located(std::move(object), dependency));
    }
    protocols.push_back(located(
        json::Object{{"name", protocol.name},
                     {"generic", protocol.generic},
                     {"staticParameters", std::move(staticParameters)},
                     {"requirements", std::move(requirements)},
                     {"roles", inspectNames(protocol.roles)},
                     {"parameters", inspectNames(protocol.parameters)},
                     {"arguments", std::move(arguments)},
                     {"results", std::move(results)},
                     {"dependencies", std::move(dependencies)},
                     {"body", protocol.body
                                  ? json::Value(inspectBody(*protocol.body))
                                  : json::Value(nullptr)}},
        protocol));
  }
  for (const auto &configuration : module.configurations)
    configurations.push_back(located(
        json::Object{{"name", configuration.name},
                     {"base", configuration.base},
                     {"arguments", inspectAssignments(configuration.arguments)},
                     {"implementations",
                      inspectAssignments(configuration.implementations)}},
        configuration));
  for (const auto &instance : module.instances) {
    json::Object object{
        {"name", instance.name},
        {"protocol", instance.protocol},
        {"parameters", inspectAssignments(instance.parameters)},
        {"dependencies", inspectAssignments(instance.dependencies)},
        {"roles", inspectAssignments(instance.roles)}};
    auto term = module.instanceProtocolTerms.find(instance.name);
    if (term != module.instanceProtocolTerms.end() &&
        !term->second.members.empty())
      object["protocolPath"] =
          json::Object{{"root", term->second.root.value},
                       {"members", inspectNames(term->second.members)}};
    instances.push_back(located(std::move(object), instance));
  }
  for (const auto &entry : module.entries) {
    json::Object object{{"name", entry.name}, {"instance", entry.instance}};
    auto args = module.entryArguments.find(entry.name);
    if (args != module.entryArguments.end())
      object["arguments"] = inspectAssignments(args->second.arguments);
    entries.push_back(located(std::move(object), entry));
  }
  return located(
      json::Object{{"kind", "module"},
                   {"carrier", module.carrier},
                   {"modules", std::move(modules)},
                   {"dependencies", std::move(dependencies)},
                   {"uses", std::move(uses)},
                   {"exports", inspectNames(module.exports)},
                   {"libraryIdentities", std::move(libraryIdentities)},
                   {"libraryAssociations", std::move(libraryAssociations)},
                   {"libraryInterfaces", std::move(libraryInterfaces)},
                   {"libraryComponents", std::move(libraryComponents)},
                   {"libraryLinks", std::move(libraryLinks)},
                   {"librarySelections", std::move(librarySelections)},
                   {"constants", std::move(constants)},
                   {"profile", module.profile ? json::Value(*module.profile)
                                              : json::Value(nullptr)},
                   {"bindings", std::move(bindings)},
                   {"relations", std::move(imports)},
                   {"relationViews", std::move(views)},
                   {"bundles", std::move(bundles)},
                   {"structs", std::move(structs)},
                   {"enums", std::move(enums)},
                   {"functions", std::move(functions)},
                   {"protocols", std::move(protocols)},
                   {"configurations", std::move(configurations)},
                   {"instances", std::move(instances)},
                   {"entries", std::move(entries)}},
      module);
}
json::Object inspectConstruction(const source::Construction &construction) {
  json::Array bindings;
  for (const auto &binding : construction.publicBindings)
    bindings.push_back(
        located(json::Object{{"name", binding.name},
                             {"ports", inspectAssignments(binding.ports)}},
                binding));
  return located(
      json::Object{{"kind", "construction"},
                   {"entry", construction.entry},
                   {"identity", construction.identity ==
                                        source::Construction::Identity::Exact
                                    ? "exact"
                                    : "normalized"},
                   {"producer", construction.producer},
                   {"validator", construction.validator},
                   {"publicBindings", std::move(bindings)},
                   {"randomness", construction.randomness},
                   {"draws", inspectAssignments(construction.draws)},
                   {"acceptance", construction.acceptance},
                   {"suite", construction.suite}},
      construction);
}
} // namespace

json::Value syntax::inspect(const Content &content) {
  json::Value value = std::visit(
      [](const auto &item) -> json::Value {
        if constexpr (std::is_same_v<std::decay_t<decltype(item)>,
                                     syntax::Module>)
          return inspectModule(item);
        else
          return inspectConstruction(item);
      },
      content);
  return json::Object{{"kind", "syntax-inspection"},
                      {"format", "pir-text"},
                      {"content", std::move(value)}};
}

} // namespace zkc::frontend
