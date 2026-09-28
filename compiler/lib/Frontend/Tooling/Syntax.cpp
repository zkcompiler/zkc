#include "../Syntax/Tree.h"
#include "zkc/Frontend/Input.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Source/Codec.h"
#include "llvm/Support/FormatVariadic.h"
using namespace llvm;
namespace zkc::frontend {
Error checkProtocolSyntax(StringRef text, StringRef filename) {
  if (isCommonDocument(classifyDocument(text))) {
    auto document = parseProtocolDocument(text, filename);
    return document ? Error::success() : document.takeError();
  }
  auto content = syntax::parse(text, filename);
  return content ? Error::success() : content.takeError();
}

Expected<json::Value> inspectProtocolSyntax(StringRef text,
                                            StringRef filename) {
  const auto form = classifyDocument(text);
  if (isCommonDocument(form)) {
    auto document = parseProtocolDocument(text, filename);
    if (!document)
      return document.takeError();
    return json::Value(json::Object{
        {"kind", "syntax-inspection"},
        {"format", form == SourceForm::CommonJSON ? "common-source-json"
                                                  : "common-source-text"},
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
// Presentation spellings preserve source path separators and exact identities.
// They never serialize unresolved syntax into the common symbol namespace.
std::string written(const syntax::Reference &reference) {
  return syntax::spelling(reference.path);
}
json::Array inspectReferences(const std::vector<syntax::Reference> &references,
                              StringRef separator = "::") {
  json::Array result;
  for (const auto &reference : references)
    result.push_back(llvm::join(reference.path.segments, separator));
  return result;
}
json::Array inspectPlaces(const syntax::Places &places) {
  json::Array result;
  for (const auto &place : places)
    result.push_back(syntax::spelling(place));
  return result;
}
json::Array inspectPlaces(const syntax::PlaceAssignments &pairs) {
  json::Array result;
  for (const auto &[name, place] : pairs)
    result.push_back(
        json::Object{{"name", name}, {"value", syntax::spelling(place)}});
  return result;
}
json::Array inspectAtoms(const std::vector<syntax::Atom> &atoms) {
  json::Array result;
  for (const auto &atom : atoms)
    result.push_back(atom.value);
  return result;
}
std::string written(const syntax::StaticTerm &term) {
  std::string result = term.root.kind == syntax::Atom::Kind::String
                           ? formatv("{0}", json::Value(term.root.value)).str()
                           : term.root.value;
  for (const auto &member : term.members)
    result += "::" + member;
  if (!term.arguments.empty()) {
    result += "<";
    for (const auto &argument : term.arguments) {
      if (result.back() != '<')
        result += ",";
      result += written(argument);
    }
    result += ">";
  }
  return result;
}
json::Array inspectTerms(const syntax::StaticTerms &terms) {
  json::Array result;
  for (const auto &term : terms)
    result.push_back(written(term));
  return result;
}
json::Array inspectTerms(const syntax::StaticAssignments &pairs) {
  json::Array result;
  for (const auto &[name, term] : pairs)
    result.push_back(json::Object{{"name", name}, {"value", written(term)}});
  return result;
}
json::Value inspectStatics(const std::optional<syntax::StaticTerms> &terms) {
  // Null distinguishes omission from an explicitly authored empty ::<>.
  return terms ? json::Value(inspectTerms(*terms)) : json::Value(nullptr);
}
json::Object located(json::Object object, const source::Node &node) {
  if (node.location)
    object["span"] = json::Object{{"offset", int64_t(node.location->offset)},
                                  {"length", int64_t(node.location->length)}};
  return object;
}
json::Array
inspectRequirements(const std::vector<syntax::Requirement> &requirements) {
  json::Array result;
  for (const auto &requirement : requirements)
    result.push_back(located(
        json::Object{
            {"predicate",
             requirement.predicate
                 ? llvm::join(requirement.predicate->path.segments, "::")
                 : std::string("=")},
            {"arguments", inspectTerms(requirement.arguments)}},
        requirement));
  return result;
}
json::Array
inspectParameters(const std::vector<syntax::StaticParameter> &parameters) {
  json::Array result;
  for (const auto &p : parameters)
    result.push_back(
        located(json::Object{{"name", p.name},
                             {"sort", p.sort ? json::Value(*p.sort)
                                             : json::Value(nullptr)},
                             {"bounds", inspectReferences(p.bounds, "::")}},
                p));
  return result;
}
json::Object inspectType(const syntax::Type &type) {
  json::Array arguments;
  for (const auto &argument : type.arguments)
    arguments.push_back(inspectType(argument));
  return located(
      json::Object{{"kind", type.product ? "product-type" : "type-expression"},
                   {"name", type.name},
                   {"rootKind", type.kind == syntax::Atom::Kind::String
                                    ? "identity"
                                : type.natural() ? "natural"
                                                 : "reference"},
                   {"arguments", std::move(arguments)},
                   {"members", inspectNames(type.members)},
                   {"natural", type.natural()}},
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
  using K = syntax::Expression::Kind;
  json::Array operands;
  for (const auto &operand : expression.operands)
    operands.push_back(inspectExpression(operand));
  auto kind = [](K kind) -> StringRef {
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
    case K::Field:
      return "field";
    case K::TupleField:
      return "tuple-field";
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
  const bool reference = expression.kind == K::Name ||
                         expression.kind == K::Call ||
                         expression.kind == K::Struct;
  json::Object result{
      {"kind", kind(expression.kind)},
      {"name", reference ? written(expression.reference) : expression.name},
      {"qualified", reference && expression.reference.path.segments.size() > 1},
      {"argumentNames", inspectNames(expression.argumentNames)},
      {"operands", std::move(operands)},
      {"attributes", inspectAtoms(expression.attributes)}};
  if (expression.kind == K::Struct)
    result["fields"] = inspectNames(expression.fields);
  if (expression.traversal)
    result["traversal"] = json::Object{
        {"state", expression.traversal->state},
        {"element", expression.traversal->element},
        {"captures", inspectPlaces(expression.traversal->captures)},
        {"body", inspectBody(expression.traversal->body)}};
  result["staticArguments"] = inspectStatics(expression.staticArguments);
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
            object["kind"] = value.operatorSymbol ? "unresolved-operator"
                                                  : "unresolved-call";
            object["callee"] = value.operatorSymbol ? *value.operatorSymbol
                                                    : written(value.callee);
            object["destructure"] = value.destructure;
            object["argumentNames"] = inspectNames(value.argumentNames);
            object["qualified"] = value.callee.path.segments.size() > 1;
            object["staticArguments"] = inspectStatics(value.staticArguments);
            object["annotation"] =
                value.annotation ? json::Value(inspectTypes(*value.annotation))
                                 : json::Value(nullptr);
            object["role"] =
                value.role ? json::Value(*value.role) : json::Value(nullptr);
            object["inputs"] = inspectPlaces(value.inputs);
            object["outputs"] = inspectNames(value.outputs);
            object["attributes"] = inspectAtoms(value.attributes);
            if (value.location)
              object["callSpan"] =
                  json::Object{{"offset", int64_t(value.location->offset)},
                               {"length", int64_t(value.location->length)}};
          } else if constexpr (std::is_same_v<T, syntax::Binding>) {
            object["kind"] = "binding";
            object["outputs"] = inspectNames(value.outputs);
            object["destructure"] = value.destructure;
            object["mutable"] = value.mutableBinding;
            object["assignment"] =
                value.assignment
                    ? json::Value(syntax::spelling(*value.assignment))
                    : json::Value(nullptr);
            object["expression"] = inspectExpression(value.expression);
            if (value.annotation)
              object["annotation"] = inspectTypes(*value.annotation);
          } else if constexpr (std::is_same_v<T, syntax::Conditional>) {
            object["kind"] = "if";
            object["condition"] = inspectExpression(value.condition);
            object["explicitRegion"] = value.explicitRegion;
            object["captures"] = inspectPlaces(value.captures);
            object["outputs"] = inspectNames(value.outputs);
            object["then"] = inspectBody(value.thenBody);
            object["else"] = inspectBody(value.elseBody);
          } else if constexpr (std::is_same_v<T, syntax::For>) {
            object["kind"] = "for";
            object["induction"] = value.induction;
            object["lower"] = inspectExpression(value.lower);
            object["upper"] = inspectExpression(value.upper);
            object["explicitRegion"] = value.explicitRegion;
            object["carried"] = inspectPlaces(value.carried);
            object["captures"] = inspectPlaces(value.captures);
            object["outputs"] = inspectNames(value.outputs);
            object["body"] = inspectBody(value.body);
          } else if constexpr (std::is_same_v<T, syntax::Match>) {
            object["kind"] = "match";
            object["input"] = syntax::spelling(value.input);
            object["captures"] = inspectPlaces(value.captures);
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
            object["input"] = syntax::spelling(value.input);
            object["carried"] = inspectPlaces(value.carried);
            object["captures"] = inspectPlaces(value.captures);
            object["outputs"] = inspectNames(value.outputs);
            object["body"] = inspectBody(value.body);
          } else if constexpr (std::is_same_v<T, syntax::Invocation>) {
            object["kind"] = "invoke";
            object["callee"] = value.callee;
            object["inputs"] = inspectPlaces(value.inputs);
            object["outputs"] = inspectNames(value.outputs);
            object["resultNames"] = inspectNames(value.resultNames);
          } else if constexpr (std::is_same_v<T, syntax::Finish>) {
            object["kind"] = "finish";
            object["ports"] = inspectPlaces(value.values);
          } else if constexpr (std::is_same_v<T, syntax::Message>) {
            object["kind"] = "message";
            object["schema"] = value.schema;
            object["sender"] = value.sender;
            object["receiver"] = value.receiver;
            object["input"] = syntax::spelling(value.input);
            object["output"] = value.output;
          } else if constexpr (std::is_same_v<T, syntax::Query>) {
            object["kind"] = "query";
            object["role"] = value.role;
            object["root"] = value.root;
            object["outputs"] = inspectNames(value.outputs);
          } else if constexpr (std::is_same_v<T, syntax::Guard>) {
            object["kind"] = "guard";
            object["role"] = value.role;
            object["condition"] = syntax::spelling(value.condition);
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
          } else if constexpr (std::is_same_v<T, syntax::Return> ||
                               std::is_same_v<T, syntax::Yield>) {
            object["kind"] =
                std::is_same_v<T, syntax::Return> ? "return" : "yield";
            object["values"] = inspectPlaces(value.values);
          } else if constexpr (std::is_same_v<T, source::Stop>) {
            object["kind"] = "stop";
            object["role"] = value.role;
            object["reason"] = value.reason;
          } else if constexpr (std::is_same_v<T, syntax::Loop>) {
            object["kind"] = "loop";
            object["count"] = json::Object{
                {"kind", value.count.kind == syntax::Atom::Kind::Number
                             ? "constant"
                             : "parameter"},
                {"value", value.count.value}};
            object["carried"] = inspectPlaces(value.carried);
            object["captures"] = inspectPlaces(value.captures);
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
    object["interface"] = written(c.interface);
    object["parameters"] = inspectParameters(c.parameters);
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
                                                {"client", written(l.client)},
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
                       {"bounds", inspectReferences(parameter.bounds, "::")},
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
  for (const auto &v : module.relationViews) {
    uint32_t height = 0;
    if (v.height && v.height->kind == syntax::Atom::Kind::Number)
      StringRef(v.height->value).getAsInteger(10, height);
    views.push_back(located(json::Object{{"name", v.name},
                                         {"relation", written(v.relation)},
                                         {"kind", v.kind},
                                         {"staging", v.staging},
                                         {"height", int64_t(height)}},
                            v));
  }
  for (const auto &binding : module.bindings)
    bindings.push_back(located(
        json::Object{
            {"name", binding.name},
            {"contract", binding.application.contract},
            {"staticArguments", inspectNames(binding.application.arguments)},
            {"implementation", binding.application.implementation}},
        binding));
  for (const auto &structure : module.structs) {
    json::Array fields;
    for (const auto &field : structure.fields)
      fields.push_back(json::Object{{"name", field.name},
                                    {"type", inspectType(field.type)}});
    structs.push_back(located(
        json::Object{
            {"name", structure.name},
            {"checked", structure.checked},
            {"parameters", inspectParameters(structure.parameters)},
            {"fields", std::move(fields)},
            {"constructors", inspectReferences(structure.constructors)}},
        structure));
  }
  for (const auto &bundle : module.bundles)
    bundles.push_back(
        located(json::Object{{"name", bundle.name},
                             {"parameters", inspectNames(bundle.parameters)},
                             {"requirements",
                              inspectRequirements(bundle.requirements)}},
                bundle));
  for (const auto &function : module.functions) {
    json::Array arguments;
    for (const auto &argument : function.arguments)
      arguments.push_back(json::Object{{"name", argument.name},
                                       {"type", inspectType(argument.type)}});
    json::Object object{
        {"kind", function.generic ? "generic-function" : "function"},
        {"name", function.name},
        {"parameters", inspectParameters(function.parameters)},
        {"requirements", inspectRequirements(function.requirements)},
        {"arguments", std::move(arguments)},
        {"results", inspectTypes(function.results)},
        {"effects", inspectNames(function.effects)},
        {"operator", function.operatorHook ? json::Value(*function.operatorHook)
                                           : json::Value(nullptr)},
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
    json::Array arguments, results, dependencies, roots;
    const auto *graph =
        std::get_if<syntax::Protocol::MathematicalBody>(&protocol.body);
    if (graph)
      for (const auto &root : graph->roots)
        roots.push_back(
            located(json::Object{{"name", root.name},
                                 {"service", written(root.service)},
                                 {"owners", inspectNames(root.owners)}},
                    root));
    for (const auto &argument : protocol.arguments)
      arguments.push_back(
          json::Object{{"name", argument.name},
                       {"role", argument.role},
                       {"availability", inspectNames(argument.availability)},
                       {"type", inspectType(argument.type)}});
    for (const auto &result : protocol.results)
      results.push_back(
          json::Object{{"role", result.role},
                       {"availability", inspectNames(result.availability)},
                       {"name", result.name},
                       {"type", inspectType(result.type)}});
    for (const auto &dependency : protocol.dependencies) {
      json::Object object{
          {"name", dependency.name},
          {"protocol", written(dependency.protocol)},
          {"agreements", inspectAssignments(dependency.agreements)}};
      if (dependency.arguments)
        object["domainArguments"] = inspectTerms(*dependency.arguments);
      dependencies.push_back(located(std::move(object), dependency));
    }
    protocols.push_back(located(
        json::Object{
            {"name", protocol.name},
            {"kind", graph ? "mathematical" : "located"},
            {"roots", std::move(roots)},
            {"generic", protocol.generic},
            {"staticParameters", inspectParameters(protocol.staticParameters)},
            {"requirements", inspectRequirements(protocol.requirements)},
            {"roles", inspectNames(protocol.roles)},
            {"parameters", inspectNames(protocol.parameters)},
            {"arguments", std::move(arguments)},
            {"results", std::move(results)},
            {"dependencies", std::move(dependencies)},
            {"body", protocol.instructions()
                         ? json::Value(inspectBody(*protocol.instructions()))
                         : json::Value(nullptr)}},
        protocol));
  }
  for (const auto &configuration : module.configurations)
    configurations.push_back(located(
        json::Object{{"name", configuration.name},
                     {"base", written(configuration.base)},
                     {"arguments", inspectTerms(configuration.arguments)},
                     {"implementations",
                      inspectAssignments(configuration.implementations)}},
        configuration));
  for (const auto &instance : module.instances) {
    json::Array parameters, instanceDependencies;
    for (const auto &[name, parameter] : instance.parameters) {
      if (!parameter.ingress) {
        parameters.push_back(
            json::Object{{"name", name}, {"value", parameter.value.value}});
        continue;
      }
      json::Array selectors;
      for (const auto &s : *parameter.ingress)
        selectors.push_back(
            json::Object{{"role", s.role},
                         {"function", written(s.function)},
                         {"arguments", inspectNames(s.arguments)}});
      parameters.push_back(json::Object{
          {"name", name},
          {"ingress", json::Object{{"bound", parameter.value.value},
                                   {"selectors", std::move(selectors)}}}});
    }
    for (const auto &[alias, target] : instance.dependencies)
      instanceDependencies.push_back(
          json::Object{{"name", alias}, {"value", written(target)}});
    const auto &path = instance.protocol.path.segments;
    json::Object object{{"name", instance.name},
                        {"protocol", written(instance.protocol)},
                        {"parameters", std::move(parameters)},
                        {"dependencies", std::move(instanceDependencies)},
                        {"roles", inspectAssignments(instance.roles)}};
    if (path.size() > 1)
      object["protocolPath"] = json::Object{
          {"root", path.front()},
          {"members",
           inspectNames(source::Names(path.begin() + 1, path.end()))}};
    instances.push_back(located(std::move(object), instance));
  }
  for (const auto &entry : module.entries) {
    json::Object object{{"name", entry.name},
                        {"instance", written(entry.instance)}};
    if (entry.arguments)
      object["arguments"] = inspectTerms(*entry.arguments);
    entries.push_back(located(std::move(object), entry));
  }
  return located(
      json::Object{{"kind", "module"},
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
