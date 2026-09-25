#include "Libraries.h"
#include "../Library/Callable.h"
#include "../Library/Diagnostic.h"
#include "../Lowering/LibrarySource.h"
#include "../Resolution/Project.h"
#include "../Syntax/Captures.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Frontend/Diagnostic.h"
#include "zkc/Frontend/Library.h"
#include "zkc/Source/Relations.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
#include <cctype>
#include <functional>
#include <set>

using namespace llvm;
namespace zkc::frontend::semantics {
namespace {
namespace lib = library;
using Terms = std::map<std::string, lib::StaticTerm>;
using Types = std::map<std::string, lib::Type>;

struct ComponentTemplate {
  lib::StaticTerm selection;
  lib::CheckedComponent checked;
};

lib::StaticTerm replace(lib::StaticTerm t, const lib::StaticTerm &from,
                        const lib::StaticTerm &to) {
  if (lib::identity(t) == lib::identity(from))
    return to;
  for (auto &a : t.arguments)
    a = replace(a, from, to);
  return t;
}
lib::Type replace(lib::Type t, const lib::StaticTerm &from,
                  const lib::StaticTerm &to) {
  for (auto &a : t.arguments)
    a = replace(a, from, to);
  for (auto &e : t.elements)
    e = replace(e, from, to);
  return t;
}
lib::Signature replace(lib::Signature s, const lib::StaticTerm &from,
                       const lib::StaticTerm &to) {
  for (auto &p : s.inputs)
    p.type = replace(p.type, from, to);
  for (auto &p : s.outputs)
    p.type = replace(p.type, from, to);
  for (auto *rs : {&s.preconditions, &s.postconditions})
    for (auto &r : *rs)
      for (auto &a : r.arguments)
        a = replace(a, from, to);
  return s;
}
std::string domainSort(StringRef s) {
  if (s.empty())
    return {};
  std::string out = s.str();
  out[0] = static_cast<char>(std::toupper(static_cast<unsigned char>(out[0])));
  return out;
}

class Author {
  const syntax::Module &source;
  StringRef text, filename;
  lib::LibraryId identity;
  lib::Environment environment;
  model::LibraryReport &report;
  Terms capturedAssociations;
  std::map<std::string, std::string> componentBounds;
  std::map<std::string, lib::Interface> interfaces;
  std::map<std::string, const syntax::LibraryComponent *> components;
  std::map<std::string, const syntax::LibrarySelection *> aliases;
  std::map<std::string, lib::CheckedBody> clients;
  std::map<std::string, lib::Callable> callables;
  std::map<std::string, Terms> callableTerms;
  std::set<std::string> externalCallables;
  std::map<std::string, std::vector<std::string>> clientParameters;
  std::map<std::string, std::shared_ptr<const lib::Implementation>> selections;
  std::map<std::string, ComponentTemplate> templates;
  std::set<std::string> active;
  size_t work = 0;

public:
  Author(const syntax::Module &s, StringRef t, StringRef f,
         model::LibraryReport &report)
      : source(s), text(t), filename(f), report(report) {}
  Error locate(Error error, const source::Node &n,
               std::vector<DiagnosticCause> context = {}) {
    Error result = Error::success();
    handleAllErrors(
        std::move(error),
        [&](const SourceDiagnostic &d) {
          auto causes = d.causes;
          causes.insert(causes.end(), context.begin(), context.end());
          if (source.project)
            result = diagnostic(source.project->input,
                                Diagnostic{d.code, d.message, d.location,
                                           d.related, std::move(causes)});
          else {
            auto detail = std::make_unique<SourceDiagnostic>(
                d.code, d.message, d.rendered, d.location);
            detail->related = d.related;
            detail->causes = std::move(causes);
            result = Error(std::move(detail));
          }
        },
        [&](const lib::Diagnostic &d) {
          auto causes = context;
          if (d.obligation) {
            json::Array arguments;
            for (const auto &argument : d.obligation->arguments)
              arguments.push_back(lib::identity(argument));
            // Exact framed static identities preserve natural actuals,
            // applications, projections and their qualified declarations.
            // The relation stays empty for equality, as in the core model.
            auto subject =
                printJson(json::Object{{"relation", d.obligation->relation},
                                       {"arguments", std::move(arguments)}});
            causes.push_back({DiagnosticCause::Kind::UnsatisfiedObligation,
                              std::move(subject),
                              d.message,
                              {}});
          }
          if (!d.checker.empty())
            causes.push_back({DiagnosticCause::Kind::Checker,
                              d.checker,
                              "finite congruence and captured capability "
                              "implication checker",
                              {}});
          result = fail(n, d.code, d.message, std::move(causes));
        },
        [&](const Refusal &e) { result = fail(n, e.code, e.detail, context); });
    return result;
  }
  Error fail(const source::Node &n, StringRef code, const Twine &message,
             std::vector<DiagnosticCause> context = {}) {
    Diagnostic result{code.str(), message.str(), n.location};
    result.causes = std::move(context);
    if (source.project) {
      if (const auto *d = source.project->enclosing(n))
        result.causes.push_back({DiagnosticCause::Kind::Declaration,
                                 lib::identity(d->identity), d->origin,
                                 d->location});
      return diagnostic(source.project->input, result);
    }
    auto error = diagnostic(text, filename, n.location ? n.location->offset : 0,
                            code, message);
    Error located = Error::success();
    handleAllErrors(std::move(error), [&](const SourceDiagnostic &d) {
      auto detail = std::make_unique<SourceDiagnostic>(d.code, d.message,
                                                       d.rendered, d.location);
      detail->causes = std::move(result.causes);
      located = Error(std::move(detail));
    });
    return located;
  }
  lib::QualifiedDecl id(StringRef name, std::vector<std::string> module = {}) {
    lib::QualifiedDecl result =
        source.project ? source.project->qualify(name, module)
                       : lib::QualifiedDecl{identity, module, name.str()};
    if (result.library.name.empty())
      result.library = identity;
    auto owner = llvm::find_if(environment.libraries, [&](const auto &l) {
      return lib::identity({l.id, {}, ""}) ==
             lib::identity({result.library, {}, ""});
    });
    if (owner == environment.libraries.end()) {
      environment.libraries.push_back({result.library, {}});
      owner = std::prev(environment.libraries.end());
    }
    auto &declarations = owner->declarations;
    if (llvm::none_of(declarations, [&](const auto &d) {
          return lib::identity(d) == lib::identity(result);
        }))
      declarations.push_back(result);
    return result;
  }
  DiagnosticCause cause(DiagnosticCause::Kind kind,
                        const lib::QualifiedDecl &subject,
                        StringRef explanation) const {
    const auto *decl =
        source.project ? source.project->lookup(subject) : nullptr;
    return {kind, lib::identity(subject), explanation.str(),
            decl ? decl->location : std::nullopt};
  }
  lib::Environment environmentFor(const lib::QualifiedDecl &owner) const {
    return source.project ? source.project->environment(environment, owner)
                          : environment;
  }
  void declareStatic(lib::QualifiedDecl q, lib::Sort sort,
                     std::map<std::string, lib::Sort> members = {},
                     std::vector<lib::Sort> parameters = {},
                     bool parameter = false) {
    for (const auto &s : environment.statics)
      if (lib::identity(s.id) == lib::identity(q))
        return;
    // The installed domain owner decides associated sorts. The names below
    // are lookup candidates, not user-supplied type facts.
    if (sort.kind == lib::Sort::Kind::Domain)
      for (StringRef member :
           {"Scalar", "BaseField", "PairingG1", "PairingG2", "ValueField",
            "PointField", "EvaluationField", "ChallengeField"}) {
        auto associated = protocol::associatedMemberSort(sort.domain, member);
        if (!associated.empty())
          members.emplace(member.str(), lib::Sort::domainOf(associated.str()));
      }
    lib::StaticDeclaration d;
    d.id = std::move(q);
    d.result = std::move(sort);
    d.members = std::move(members);
    d.parameters = std::move(parameters);
    d.parameter = parameter;
    environment.statics.push_back(std::move(d));
  }
  lib::Sort memberSort(const syntax::LibraryStaticMember &m) {
    if (m.sort == "nat")
      return lib::Sort::natural();
    if (m.sort == "association")
      return lib::Sort::association();
    return lib::Sort::domainOf(domainSort(m.domain));
  }
  Expected<lib::Sort> parameterSort(const syntax::StaticParameter &p) {
    if (p.sort)
      return lib::Sort::domainOf(domainSort(*p.sort));
    if (p.bounds.size() == 1) {
      if (p.bounds[0] == "nat")
        return lib::Sort::natural();
      if (p.bounds[0] == "association")
        return lib::Sort::association();
      for (const auto &interface : source.libraryInterfaces)
        if (interface.name == p.bounds[0])
          return lib::Sort::component();
    }
    return fail(p, "library-source-parameter",
                "component parameters require domain, nat, association or one "
                "interface bound");
  }
  std::map<std::string, lib::Sort>
  parameterMembers(const syntax::StaticParameter &p) {
    if (!p.sort && p.bounds.size() == 1)
      for (const auto &interface : source.libraryInterfaces)
        if (interface.name == p.bounds[0])
          return members(interface);
    return {};
  }
  std::map<std::string, lib::Sort> members(const syntax::LibraryInterface &i) {
    std::map<std::string, lib::Sort> out;
    for (const auto &t : i.types)
      out.emplace(t.name, lib::Sort::type());
    for (const auto &m : i.statics)
      out.emplace(m.name, memberSort(m));
    return out;
  }
  Expected<lib::StaticTerm> root(const syntax::Atom &a, const Terms &terms) {
    if (++work > 262144)
      return fail(a, "library-source-limit",
                  "library elaboration exceeds work budget");
    if (a.kind == syntax::Atom::Kind::Number) {
      uint64_t n;
      if (StringRef(a.value).getAsInteger(10, n))
        return fail(a, "library-source-natural",
                    "natural literal exceeds uint64");
      return lib::StaticTerm::natural(n);
    }
    auto found = terms.find(a.value);
    if (a.kind != syntax::Atom::Kind::String && found != terms.end())
      return found->second;
    if (a.kind == syntax::Atom::Kind::Name) {
      auto captured = capturedAssociations.find(a.value);
      if (captured != capturedAssociations.end())
        return captured->second;
    }
    auto sort = protocol::installedIdentitySort(a.value);
    if (sort.empty())
      return fail(a, "library-source-static",
                  "unknown static root '" + a.value + "'");
    // Installed identities remain exact nominal roots. Their owner supplies
    // sorts.
    const lib::LibraryId installed{"zkc", "installed-contracts", "1",
                                   "builtin"};
    lib::QualifiedDecl q{installed, {"installed"}, a.value};
    auto owner = llvm::find_if(environment.libraries, [&](const auto &l) {
      return lib::identity({l.id, {}, ""}) ==
             lib::identity({installed, {}, ""});
    });
    if (owner == environment.libraries.end()) {
      environment.libraries.push_back({installed, {}});
      owner = std::prev(environment.libraries.end());
    }
    if (llvm::none_of(owner->declarations, [&](const auto &d) {
          return lib::identity(d) == lib::identity(q);
        }))
      owner->declarations.push_back(q);
    declareStatic(q, lib::Sort::domainOf(sort.str()));
    for (auto &d : environment.statics)
      if (lib::identity(d.id) == lib::identity(q))
        d.capturedSubject = a.value;
    auto term = lib::StaticTerm::root(q);
    return term;
  }
  Expected<lib::StaticTerm> term(const syntax::LibraryTerm &s,
                                 const Terms &terms, unsigned depth = 0) {
    if (depth > 64)
      return fail(s, "library-source-cycle",
                  "static selection alias cycle or depth limit");
    lib::StaticTerm result;
    auto alias = aliases.find(s.root.value);
    if (s.root.kind == syntax::Atom::Kind::Name && alias != aliases.end()) {
      if (s.applied)
        return fail(s, "library-source-selection",
                    "selected alias cannot receive arguments");
      auto target = term(alias->second->target, terms, depth + 1);
      if (!target)
        return target.takeError();
      result = *target;
      if (alias->second->sealed) {
        auto sort = lib::sortOf(result, environment);
        if (!sort)
          return sort.takeError();
        if (sort->kind != lib::Sort::Kind::Component)
          return fail(s, "library-source-selection",
                      "seal requires a component selection");
        std::map<std::string, lib::Sort> ms;
        for (const auto &d : environment.statics)
          if (lib::identity(d.id) == lib::identity(result.declaration))
            ms = d.members;
        auto q = id(alias->second->name);
        declareStatic(q, lib::Sort::component(), std::move(ms),
                      {lib::Sort::component()});
        for (auto &d : environment.statics)
          if (lib::identity(d.id) == lib::identity(q))
            d.seal = true;
        result = lib::StaticTerm::seal(q, std::move(result));
      }
    } else if (s.applied) {
      auto component = components.find(s.root.value);
      if (s.root.kind != syntax::Atom::Kind::Name ||
          component == components.end())
        return fail(s, "library-source-selection",
                    "application requires a declared component");
      std::vector<lib::StaticTerm> args;
      for (const auto &a : s.arguments) {
        auto t = term(a, terms, depth + 1);
        if (!t)
          return t.takeError();
        args.push_back(std::move(*t));
      }
      result = lib::StaticTerm::apply(id(s.root.value), std::move(args));
    } else if (s.root.kind == syntax::Atom::Kind::Name &&
               components.count(s.root.value)) {
      if (!components.at(s.root.value)->parameters.empty())
        return fail(s, "library-source-selection",
                    "generic component requires explicit actuals");
      result = lib::StaticTerm::root(id(s.root.value));
    } else {
      auto r = root(s.root, terms);
      if (!r)
        return r.takeError();
      result = *r;
    }
    for (const auto &m : s.members)
      result = lib::StaticTerm::project(std::move(result), m);
    return result;
  }
  Expected<lib::StaticTerm> term(const syntax::StaticTerm &s,
                                 const Terms &terms) {
    syntax::LibraryTerm t;
    t.root = s.root;
    t.members = s.members;
    return term(t, terms);
  }
  Expected<lib::StaticTerm> typeTerm(const syntax::Type &s,
                                     const Terms &terms) {
    if (s.product || !s.arguments.empty())
      return fail(s, "library-source-static",
                  "static argument requires a sorted root or projection");
    syntax::LibraryTerm t;
    t.root.location = s.location;
    t.root.value = s.name;
    t.root.kind = s.natural  ? syntax::Atom::Kind::Number
                  : s.quoted ? syntax::Atom::Kind::String
                             : syntax::Atom::Kind::Name;
    t.members = s.members;
    return term(t, terms);
  }
  Expected<lib::Type> type(const syntax::Type &s, const Terms &terms,
                           const Types &types, unsigned depth = 0) {
    if (depth > 64)
      return fail(s, "library-source-limit",
                  "record/type expansion exceeds depth 64");
    if (++work > 262144)
      return fail(s, "library-source-limit",
                  "library type expansion exceeds work budget");
    if (s.product) {
      std::vector<lib::Type> elements;
      for (const auto &a : s.arguments) {
        auto t = type(a, terms, types, depth + 1);
        if (!t)
          return t.takeError();
        elements.push_back(*t);
      }
      return lib::Type::product(std::move(elements));
    }
    if (!s.quoted && !s.natural && s.arguments.empty() && s.members.empty()) {
      auto local = types.find(s.name);
      if (local != types.end())
        return local->second;
    }
    if (!s.quoted && s.name == "Array" && s.members.empty() &&
        s.arguments.size() == 2) {
      auto element = type(s.arguments[0], terms, types, depth + 1);
      if (!element)
        return element.takeError();
      auto count = typeTerm(s.arguments[1], terms);
      if (!count)
        return count.takeError();
      return lib::Type::array(*element, *count);
    }
    if (!s.members.empty()) {
      if (!s.arguments.empty())
        return fail(s, "library-source-type",
                    "applied type projection is unsupported");
      syntax::Type base = s;
      auto member = base.members.back();
      base.members.pop_back();
      auto subject = typeTerm(base, terms);
      if (!subject)
        return subject.takeError();
      auto sort = lib::sortOf(*subject, environment);
      if (!sort)
        return sort.takeError();
      if (sort->kind == lib::Sort::Kind::Component) {
        auto memberType = lib::sortOf(
            lib::StaticTerm::project(*subject, member), environment);
        if (!memberType)
          return memberType.takeError();
        if (memberType->kind != lib::Sort::Kind::Type)
          return fail(s, "library-source-type",
                      "component member is not a type");
        return lib::Type::abstract(*subject, member);
      }
      if (sort->kind == lib::Sort::Kind::Domain && member == "Element") {
        if (sort->domain == "Field")
          return lib::Type::logical("field", {*subject});
        if (sort->domain == "Group")
          return lib::Type::logical("group", {*subject});
      }
      return fail(s, "library-source-type", "unknown domain type member");
    }
    if (!s.quoted && !s.natural && s.members.empty())
      for (const auto &enumeration : source.enums)
        if (enumeration.name == s.name) {
          if (s.arguments.size() != enumeration.parameters.size())
            return fail(s, "library-source-enum-arity",
                        "enum requires explicit static actuals");
          if (enumeration.alternatives.empty() ||
              enumeration.alternatives.size() > 32)
            return fail(enumeration, "library-source-enum",
                        "enum requires 1 to 32 alternatives");
          Terms captures;
          std::vector<lib::StaticTerm> actuals;
          for (unsigned n = 0; n < s.arguments.size(); ++n) {
            auto expected = parameterSort(enumeration.parameters[n]);
            if (!expected)
              return expected.takeError();
            auto actual = typeTerm(s.arguments[n], terms);
            if (!actual)
              return actual.takeError();
            auto sort = lib::sortOf(*actual, environment);
            if (!sort)
              return sort.takeError();
            if (sort->kind != expected->kind ||
                sort->domain != expected->domain)
              return fail(s, "library-source-enum-actual",
                          "enum actual has wrong static sort");
            // Component bounds are checked against the abstract import, never
            // guessed from a concrete representation or an import's spelling.
            const auto &parameter = enumeration.parameters[n];
            if (expected->kind == lib::Sort::Kind::Component) {
              auto bound = componentBounds.find(lib::identity(*actual));
              bool agrees = bound != componentBounds.end() &&
                            bound->second == parameter.bounds.front();
              if (!agrees)
                return fail(s, "library-source-enum-actual",
                            "enum component actual must have its declared "
                            "interface bound");
            }
            if (!captures.emplace(parameter.name, *actual).second)
              return fail(enumeration, "library-source-duplicate",
                          "duplicate enum parameter");
            actuals.push_back(*actual);
          }
          std::vector<std::string> labels;
          std::vector<lib::Type> payloads;
          for (const auto &alternative : enumeration.alternatives) {
            if (llvm::is_contained(labels, alternative.name))
              return fail(enumeration, "library-source-duplicate",
                          "duplicate enum alternative");
            labels.push_back(alternative.name);
            auto payload = type(alternative.type, captures, {}, depth + 1);
            if (!payload)
              return payload.takeError();
            payloads.push_back(*payload);
          }
          auto result = lib::Type::variant(
              id(enumeration.name), std::move(labels), std::move(payloads));
          result.arguments = std::move(actuals);
          return result;
        }
    if (!s.quoted && s.members.empty())
      for (const auto &record : source.structs)
        if (record.name == s.name) {
          if (!record.parameters.empty() || !s.arguments.empty())
            return fail(s, "library-source-record-generic",
                        "generic record constructors need a sorted nominal "
                        "argument schema");
          std::vector<std::string> fields;
          std::vector<lib::Type> elements;
          std::set<std::string> names;
          for (const auto &field : record.fields) {
            if (!names.insert(field.name).second)
              return fail(record, "library-source-duplicate",
                          "duplicate record field");
            auto t = type(field.type, {}, {}, depth + 1);
            if (!t)
              return t.takeError();
            fields.push_back(field.name);
            elements.push_back(*t);
          }
          return lib::Type::record(id(record.name), std::move(fields),
                                   std::move(elements));
        }
    for (const auto &installed : protocol::boundTypeConstructors()) {
      if (installed.name != s.name || s.quoted || s.natural)
        continue;
      if (s.arguments.size() != installed.parameters.size())
        return fail(s, "library-source-type",
                    "logical type has wrong static arity");
      std::vector<lib::StaticTerm> args;
      for (const auto &a : s.arguments) {
        auto t = typeTerm(a, terms);
        if (!t)
          return t.takeError();
        args.push_back(*t);
      }
      return lib::Type::logical(s.name, std::move(args));
    }
    return fail(s, "library-source-type",
                "unknown checked library type '" + s.name + "'");
  }
  Expected<lib::Signature> signature(const syntax::Function &f,
                                     const Terms &terms, const Types &types) {
    if (f.explicitOrigin)
      return fail(f, "library-source-origin",
                  "checked library identity comes from its captured "
                  "declaration, not an origin clause");
    if (f.generic)
      return fail(f, "library-source-member-generic",
                  "member-local generic parameters are unsupported");
    lib::Signature result;
    for (const auto &effect : f.effects) {
      if (effect != "local" || !result.effects.insert(effect).second)
        return fail(f, "library-source-effect",
                    "supported effect is local, without duplicates");
    }
    for (const auto &p : f.arguments) {
      auto t = type(p.type, terms, types);
      if (!t)
        return t.takeError();
      result.inputs.push_back({*t, {}});
      result.inputLabels.push_back(p.name);
    }
    for (const auto &p : f.results) {
      auto t = type(p, terms, types);
      if (!t)
        return t.takeError();
      result.outputs.push_back({*t, {}});
    }
    // The parser records one typed term list for every requirement it reads.
    if (f.requirements.size() != f.requirementTerms.size())
      report_fatal_error("library requirement syntax lacks its typed terms");
    for (size_t n = 0; n < f.requirements.size(); ++n) {
      lib::Requirement r;
      r.relation =
          f.requirements[n].predicate == "=" ? "" : f.requirements[n].predicate;
      for (const auto &a : f.requirementTerms[n]) {
        auto t = term(a, terms);
        if (!t)
          return t.takeError();
        r.arguments.push_back(*t);
      }
      result.preconditions.push_back(std::move(r));
    }
    return result;
  }

  class BodyBuilder {
    Author &a;
    const syntax::Function &function;
    const Terms &terms;
    const Types &types;
    std::vector<lib::Import> imports;
    lib::Body body;
    std::map<std::string, lib::Place> locals;
    std::map<uint32_t, lib::Type> values;
    uint32_t next = 0;
    bool returned = false;
    lib::Value value(lib::Type t) {
      lib::Value v{{next++}, {std::move(t), {}}};
      values.emplace(v.id.index, v.port.type);
      return v;
    }
    Expected<lib::Type> placeType(const lib::Place &p) {
      auto t = values.at(p.value.index);
      for (auto index : p.path) {
        if (t.kind == lib::Type::Kind::Array) {
          if (t.arguments[0].kind != lib::StaticTerm::Kind::Natural ||
              index >= t.arguments[0].number)
            return a.fail(
                function, "library-source-index",
                "array projection needs a known in-range static index");
          auto child = t.elements[0];
          t = std::move(child);
        } else if ((t.kind == lib::Type::Kind::Product ||
                    t.kind == lib::Type::Kind::Record) &&
                   index < t.elements.size()) {
          auto child = t.elements[index];
          t = std::move(child);
        } else
          return a.fail(function, "library-source-projection",
                        "invalid aggregate projection");
      }
      return t;
    }
    Expected<lib::Place> named(StringRef name, const source::Node &n) {
      auto exact = locals.find(name.str());
      if (exact != locals.end())
        return exact->second;
      auto [root, field] = name.rsplit('.');
      if (!root.empty() && !field.empty()) {
        auto base = named(root, n);
        if (!base)
          return base.takeError();
        auto t = placeType(*base);
        if (!t)
          return t.takeError();
        unsigned index;
        if (field.getAsInteger(10, index)) {
          auto it = llvm::find(t->fields, field.str());
          if (it == t->fields.end())
            return a.fail(n, "library-source-projection",
                          "unknown record field");
          index = it - t->fields.begin();
        }
        auto p = *base;
        p.path.push_back(index);
        auto checked = placeType(p);
        if (!checked)
          return checked.takeError();
        return p;
      }
      return a.fail(n, "library-source-name", "unknown value '" + name + "'");
    }
    Expected<lib::Signature> logical(const generic::Operation &op,
                                     const std::vector<lib::StaticTerm> &args) {
      std::vector<lib::StaticTerm> scope;
      size_t rootIndex = 0;
      for (unsigned n = 0; n < op.signature.scope.terms.size(); ++n) {
        const auto &t = op.signature.scope.terms[n];
        if (t.arguments)
          return a.fail(function, "library-source-operation",
                        "installed constructor applications require a "
                        "supported typed adapter");
        if (t.parent) {
          if (*t.parent >= scope.size())
            return a.fail(function, "library-source-operation",
                          "invalid installed static scope");
          scope.push_back(lib::StaticTerm::project(scope[*t.parent], t.name));
        } else if (auto fixed = op.signature.scope.constants.find(n);
                   fixed != op.signature.scope.constants.end()) {
          syntax::Atom atom;
          atom.kind = syntax::Atom::Kind::String;
          atom.value = fixed->second;
          auto r = a.root(atom, {});
          if (!r)
            return r.takeError();
          scope.push_back(*r);
        } else {
          if (rootIndex >= args.size())
            return a.fail(function, "library-source-operation",
                          "operation requires explicit static actuals");
          scope.push_back(args[rootIndex++]);
        }
      }
      if (rootIndex != args.size())
        return a.fail(function, "library-source-operation",
                      "operation has extra static actuals");
      lib::Signature s;
      s.effects.insert("local");
      auto port = [&](const generic::Type &t) {
        std::vector<lib::StaticTerm> ts;
        for (auto i : t.arguments)
          ts.push_back(scope.at(i));
        return lib::Port{lib::Type::logical(t.constructor, std::move(ts)), {}};
      };
      for (const auto &t : op.signature.inputs)
        s.inputs.push_back(port(t));
      for (const auto &t : op.signature.outputs)
        s.outputs.push_back(port(t));
      return s;
    }
    Expected<std::vector<unsigned>> argumentOrder(const syntax::Expression &e,
                                                  const lib::Signature &s) {
      auto order = lib::bindArguments(s, e.operands.size(), e.argumentNames);
      if (!order)
        return a.locate(order.takeError(), e);
      return order;
    }
    Expected<std::vector<lib::Place>>
    call(const syntax::Expression &e, const lib::Type *expected = nullptr) {
      lib::Call c;
      lib::Signature signature;
      auto [owner, member] = StringRef(e.name).rsplit('.');
      auto component = terms.find(owner.str());
      if (e.qualified && component != terms.end()) {
        if (llvm::any_of(protocol::boundOperationContracts(),
                         [&](const auto &op) { return op.name == e.name; }))
          return a.fail(
              e, "library-source-call-ambiguity",
              "component member conflicts with an installed primitive");
        if (e.staticArguments || !e.attributes.empty())
          return a.fail(
              e, "library-source-call",
              "member call cannot carry static arguments or attributes");
        auto imported = llvm::find_if(imports, [&](const auto &i) {
          return lib::identity(i.parameter) == lib::identity(component->second);
        });
        if (imported == imports.end())
          return a.fail(e, "library-source-call",
                        "member call needs an interface-bound component");
        auto fn =
            imported->interface.declaration().functions.find(member.str());
        if (fn == imported->interface.declaration().functions.end())
          return a.fail(e, "library-source-call",
                        "interface does not export this function");
        signature = replace(fn->second, imported->interface.declaration().self,
                            component->second);
        c.target = lib::MemberCall{component->second, member.str()};
      } else if (!e.quoted && !e.qualified &&
                 llvm::any_of(a.source.functions, [&](const auto &f) {
                   return f.name == e.name;
                 })) {
        const auto &f = *llvm::find_if(a.source.functions, [&](const auto &f) {
          return f.name == e.name;
        });
        if (!e.attributes.empty())
          return a.fail(e, "library-source-call",
                        "source helpers have no attributes");
        if (auto error = a.prepareClient(f))
          return std::move(error);
        const auto &contract = a.callables.at(f.name);
        const auto &d = contract.declaration();
        lib::Substitution arguments;
        if (e.staticArguments) {
          if (e.staticTerms.size() != d.parameters.size())
            return a.fail(e, "library-source-actual",
                          "wrong helper static arity");
          for (size_t i = 0; i < d.parameters.size(); ++i) {
            auto t = a.term(e.staticTerms[i], terms);
            if (!t)
              return t.takeError();
            arguments.statics.push_back(
                {lib::StaticTerm::root(d.parameters[i]), *t});
          }
        } else {
          // Infer only structural, rigid nominal heads/dimensions already
          // present in operand or expected result types. Never search layouts.
          std::map<std::string, lib::StaticTerm> solved;
          std::set<std::string> parameters;
          for (const auto &p : d.parameters)
            parameters.insert(lib::identity(p));
          bool conflict = false;
          std::function<void(const lib::StaticTerm &, const lib::StaticTerm &)>
              term;
          term = [&](const auto &formal, const auto &value) {
            if (formal.kind == lib::StaticTerm::Kind::Root &&
                parameters.count(lib::identity(formal.declaration))) {
              auto [old, fresh] =
                  solved.emplace(lib::identity(formal.declaration), value);
              if (!fresh && lib::identity(old->second) != lib::identity(value))
                conflict = true;
            } else if (formal.kind == value.kind &&
                       formal.member == value.member &&
                       formal.arguments.size() == value.arguments.size()) {
              for (size_t i = 0; i < formal.arguments.size(); ++i)
                term(formal.arguments[i], value.arguments[i]);
            }
          };
          std::function<void(const lib::Type &, const lib::Type &)> infer;
          infer = [&](const auto &formal, const auto &value) {
            if (formal.kind != value.kind || formal.name != value.name ||
                formal.arguments.size() != value.arguments.size() ||
                formal.elements.size() != value.elements.size())
              return;
            for (size_t i = 0; i < formal.arguments.size(); ++i)
              term(formal.arguments[i], value.arguments[i]);
            for (size_t i = 0; i < formal.elements.size(); ++i)
              infer(formal.elements[i], value.elements[i]);
          };
          auto order = argumentOrder(e, d.signature);
          if (!order)
            return order.takeError();
          for (size_t i = 0; i < e.operands.size(); ++i) {
            const auto &operand = e.operands[i];
            if (operand.kind != syntax::Expression::Kind::Name ||
                operand.quoted)
              continue;
            auto p = named(operand.name, operand);
            if (!p)
              return p.takeError();
            auto t = placeType(*p);
            if (!t)
              return t.takeError();
            infer(d.signature.inputs[(*order)[i]].type, *t);
          }
          if (expected && d.signature.outputs.size() == 1)
            infer(d.signature.outputs.front().type, *expected);
          for (const auto &p : d.parameters) {
            auto value = solved.find(lib::identity(p));
            if (conflict || value == solved.end())
              return a.fail(e, "library-source-inference",
                            "helper static arguments conflict or remain "
                            "unsolved; supply explicit actuals");
            arguments.statics.push_back(
                {lib::StaticTerm::root(p), value->second});
          }
        }
        lib::SourceCall target{contract, std::move(arguments)};
        const std::vector<lib::TypeBound> noBounds;
        auto formed = lib::detail::sourceSignature(
            target, {a.environment, imports, noBounds});
        if (!formed)
          return a.locate(formed.takeError(), e);
        signature = std::move(*formed);
        c.target = std::move(target);
      } else {
        std::string operation = e.name;
        std::vector<lib::StaticTerm> args;
        for (const auto &t : e.staticTerms) {
          auto v = a.term(t, terms);
          if (!v)
            return v.takeError();
          args.push_back(*v);
        }
        for (const auto &binding : a.source.bindings)
          if (binding.name == e.name && !e.qualified && !e.quoted) {
            if (e.staticArguments)
              return a.fail(
                  e, "library-source-call",
                  "bound operation cannot receive extra static arguments");
            operation = binding.application.contract;
            for (const auto &s : binding.application.arguments) {
              syntax::Atom atom;
              atom.kind = syntax::Atom::Kind::String;
              atom.value = s;
              auto t = a.root(atom, {});
              if (!t)
                return t.takeError();
              args.push_back(*t);
            }
            if (!binding.application.implementation.empty())
              return a.fail(e, "library-source-implementation",
                            "checked logical calls cannot discard an explicit "
                            "implementation selection");
          }
        auto op =
            llvm::find_if(protocol::boundOperationContracts(),
                          [&](const auto &o) { return o.name == operation; });
        if (op == protocol::boundOperationContracts().end())
          return a.fail(
              e, "library-source-call",
              "call is not an installed operation or interface member");
        auto s = logical(*op, args);
        if (!s)
          return s.takeError();
        signature = *s;
        c.target = lib::LogicalCall{operation, std::move(args)};
        c.attributes = e.attributes;
      }
      auto order = argumentOrder(e, signature);
      if (!order)
        return order.takeError();
      c.inputs.resize(e.operands.size());
      for (unsigned n = 0; n < e.operands.size(); ++n) {
        const auto formal = (*order)[n];
        auto p = expression(e.operands[n], &signature.inputs[formal].type);
        if (!p)
          return p.takeError();
        // Materialize now, in written order, so nested evaluation and affine
        // consumption cannot be delayed until the final argument permutation.
        auto temporary = value(signature.inputs[formal].type);
        body.instructions.push_back(lib::Project{*p, temporary});
        c.inputs[formal] = {temporary.id, {}};
      }
      std::vector<lib::Place> outputs;
      for (const auto &p : signature.outputs) {
        auto v = value(p.type);
        c.outputs.push_back(v);
        outputs.push_back({v.id, {}});
      }
      body.instructions.push_back(std::move(c));
      return outputs;
    }
    Expected<lib::Place> product(std::vector<lib::Place> ps,
                                 const source::Node &n, bool array = false) {
      std::vector<lib::Type> ts;
      for (const auto &p : ps) {
        auto t = placeType(p);
        if (!t)
          return t.takeError();
        ts.push_back(*t);
      }
      lib::Type t;
      if (array) {
        if (ts.empty())
          return a.fail(n, "library-source-array",
                        "empty array requires a typed constructor");
        for (const auto &e : ts)
          if (!lib::sameType(e, ts.front()))
            return a.fail(n, "library-source-array",
                          "array elements have unequal types");
        t = lib::Type::array(ts.front(), lib::StaticTerm::natural(ts.size()));
      } else
        t = lib::Type::product(std::move(ts));
      auto out = value(t);
      body.instructions.push_back(lib::Construct{out, std::move(ps)});
      return lib::Place{out.id, {}};
    }
    Expected<lib::Place> expression(const syntax::Expression &e,
                                    const lib::Type *expected = nullptr) {
      if (++a.work > 262144)
        return a.fail(e, "library-source-limit",
                      "body expansion exceeds work budget");
      using K = syntax::Expression::Kind;
      if (e.kind == K::Map || e.kind == K::Fold)
        return lexicalTraversal(e, expected);
      if (e.kind == K::Index || e.kind == K::Boolean) {
        syntax::Expression constant;
        constant.location = e.location;
        constant.kind = K::Call;
        constant.qualified = true;
        constant.name = "index.constant";
        constant.attributes = {e.kind == K::Index ? e.name : "0"};
        auto left = call(constant);
        if (!left)
          return left.takeError();
        if (e.kind == K::Index)
          return left->front();
        auto right = left->front();
        if (e.name == "false") {
          constant.attributes = {"1"};
          auto other = call(constant);
          if (!other)
            return other.takeError();
          right = other->front();
        }
        auto output = value(lib::Type::logical("bool"));
        lib::Call equality;
        equality.target = lib::LogicalCall{"index.equal", {}};
        equality.inputs = {left->front(), right};
        equality.outputs = {output};
        body.instructions.push_back(std::move(equality));
        return lib::Place{output.id, {}};
      }
      if (e.kind == K::Name && !e.quoted)
        return named(e.name, e);
      if (e.kind == K::Call) {
        auto path = StringRef(e.name).rsplit('.');
        auto owner = path.first;
        auto label = path.second;
        auto enumeration = llvm::find_if(
            a.source.enums, [&](const auto &d) { return d.name == owner; });
        if (e.qualified && !e.quoted && enumeration != a.source.enums.end()) {
          if (!expected || expected->kind != lib::Type::Kind::Variant)
            return a.fail(
                e, "library-source-enum-expected",
                "enum construction requires an explicit expected type");
          if (lib::identity(expected->declaration) !=
              lib::identity(a.id(owner)))
            return a.fail(e, "library-source-enum-nominal",
                          "constructor differs from expected enum declaration");
          auto alternative = llvm::find(expected->fields, label.str());
          if (alternative == expected->fields.end())
            return a.fail(e, "library-source-enum-alternative",
                          "unknown enum alternative");
          if (e.staticArguments || !e.attributes.empty() ||
              !e.argumentNames.empty())
            return a.fail(e, "library-source-enum-constructor",
                          "constructor uses only the expected type and "
                          "positional payload");
          const auto &payloadType =
              expected->elements[alternative - expected->fields.begin()];
          Expected<lib::Place> payload = [&]() -> Expected<lib::Place> {
            if (e.operands.size() == 1)
              return expression(e.operands.front(), &payloadType);
            syntax::Expression tuple;
            tuple.kind = K::Product;
            tuple.operands = e.operands;
            return expression(tuple, &payloadType);
          }();
          if (!payload)
            return payload.takeError();
          auto output = value(*expected);
          body.instructions.push_back(
              lib::VariantConstruct{output, label.str(), *payload});
          return lib::Place{output.id, {}};
        }
        auto ps = call(e, expected);
        if (!ps)
          return ps.takeError();
        if (ps->size() == 1)
          return ps->front();
        return product(std::move(*ps), e);
      }
      if (e.kind == K::Struct) {
        if (e.staticArguments || !e.attributes.empty() || e.qualified ||
            e.quoted)
          return a.fail(
              e, "library-source-record-generic",
              "record construction requires an unapplied nominal record");
        auto declaration = llvm::find_if(
            a.source.structs, [&](const auto &r) { return r.name == e.name; });
        if (declaration == a.source.structs.end())
          return a.fail(e, "library-source-record",
                        "unknown nominal record constructor");
        if (declaration->checked)
          return a.fail(e, "library-source-record-authority",
                        "checked record constructor authority is not imported "
                        "by this library profile");
        syntax::Type spelling;
        spelling.name = e.name;
        auto t = a.type(spelling, terms, types);
        if (!t)
          return t.takeError();
        if (e.fields.size() != e.operands.size() ||
            e.fields.size() != t->fields.size())
          return a.fail(
              e, "library-source-record",
              "record construction must cover every field exactly once");
        std::map<std::string, lib::Place> fields;
        // Evaluate in authored order; only then arrange semantic field paths.
        for (unsigned n = 0; n < e.fields.size(); ++n) {
          if (!llvm::is_contained(t->fields, e.fields[n]) ||
              fields.count(e.fields[n]))
            return a.fail(e, "library-source-record",
                          "unknown or duplicate record field");
          auto index = llvm::find(t->fields, e.fields[n]) - t->fields.begin();
          auto p = expression(e.operands[n], &t->elements[index]);
          if (!p)
            return p.takeError();
          fields.emplace(e.fields[n], *p);
        }
        std::vector<lib::Place> elements;
        for (const auto &name : t->fields)
          elements.push_back(fields.at(name));
        auto output = value(*t);
        body.instructions.push_back(
            lib::Construct{output, std::move(elements)});
        return lib::Place{output.id, {}};
      }
      if (e.kind == K::Product || e.kind == K::Vector) {
        std::vector<lib::Place> ps;
        for (unsigned n = 0; n < e.operands.size(); ++n) {
          const lib::Type *element = nullptr;
          if (expected && e.kind == K::Vector &&
              expected->kind == lib::Type::Kind::Array)
            element = &expected->elements.front();
          else if (expected && e.kind == K::Product &&
                   expected->kind == lib::Type::Kind::Product &&
                   n < expected->elements.size())
            element = &expected->elements[n];
          auto p = expression(e.operands[n], element);
          if (!p)
            return p.takeError();
          ps.push_back(*p);
        }
        if (e.kind == K::Vector && expected &&
            expected->kind == lib::Type::Kind::Array) {
          auto output = value(*expected);
          body.instructions.push_back(lib::Construct{output, std::move(ps)});
          return lib::Place{output.id, {}};
        }
        return product(std::move(ps), e, e.kind == K::Vector);
      }
      if (e.kind == K::Get && e.operands.size() == 2) {
        auto spelling = [&](auto &&self,
                            const syntax::Expression &v) -> std::string {
          if (v.kind == K::Name && !v.quoted)
            return v.name;
          if (v.kind != K::Get || v.operands.size() != 2 ||
              v.operands[1].kind != K::Index)
            return {};
          auto base = self(self, v.operands.front());
          return base.empty() ? std::string{} : base + "." + v.operands[1].name;
        };
        auto captured = locals.find(spelling(spelling, e));
        if (captured != locals.end())
          return captured->second;
        auto p = expression(e.operands[0]);
        if (!p)
          return p.takeError();
        unsigned index;
        if (e.operands[1].kind != K::Index ||
            StringRef(e.operands[1].name).getAsInteger(10, index))
          return a.fail(
              e, "library-source-index",
              "checked aggregate access requires a literal static index");
        p->path.push_back(index);
        auto checked = placeType(*p);
        if (!checked)
          return checked.takeError();
        return *p;
      }
      return a.fail(
          e, "library-source-expression",
          "expression is not supported by the typed library body language");
    }
    Error bind(const source::Names &names, bool destructure,
               const std::optional<std::vector<syntax::Type>> &annotation,
               lib::Place p, const source::Node &n) {
      auto t = placeType(p);
      if (!t)
        return t.takeError();
      if (annotation) {
        if (annotation->size() != 1)
          return a.fail(n, "library-source-annotation",
                        "annotation must name one source type");
        auto expected = a.type(annotation->front(), terms, types);
        if (!expected)
          return expected.takeError();
        if (!lib::sameType(*expected, *t))
          return a.fail(n, "library-source-annotation",
                        "binding annotation differs from inferred type");
      }
      if (names.empty()) {
        body.instructions.push_back(lib::Drop{p});
        return Error::success();
      }
      if (destructure && (t->kind != lib::Type::Kind::Product ||
                          names.size() != t->elements.size()))
        return a.fail(n, "library-source-pattern",
                      "destructuring requires an equal-arity product");
      if (!destructure && names.size() != 1)
        return a.fail(n, "library-source-pattern", "binding needs one name");
      for (unsigned i = 0; i < names.size(); ++i) {
        auto projected = p;
        if (destructure)
          projected.path.push_back(i);
        if (!locals.emplace(names[i], projected).second)
          return a.fail(n, "library-source-duplicate",
                        "duplicate value binding");
      }
      return Error::success();
    }

    Expected<std::optional<lib::Type>>
    annotationType(const std::optional<std::vector<syntax::Type>> &annotation,
                   const source::Node &n) {
      if (!annotation)
        return std::optional<lib::Type>{};
      if (annotation->size() != 1)
        return a.fail(n, "library-source-annotation",
                      "annotation must name one source type");
      auto t = a.type(annotation->front(), terms, types);
      if (!t)
        return t.takeError();
      return std::optional<lib::Type>(*t);
    }
    Expected<std::shared_ptr<const lib::Region>>
    region(const syntax::Body &syntaxBody, std::vector<lib::Value> inputs,
           std::map<std::string, lib::Place> names, bool lexical = false,
           const lib::Type *expected = nullptr) {
      // Swap only lexical state. The allocation table and counter remain global
      // so sibling arms cannot accidentally share a ValueId.
      auto oldInstructions = std::move(body.instructions);
      auto oldReturns = std::move(body.returns);
      auto oldLocals = std::move(locals);
      bool oldReturned = returned;
      auto restore = llvm::scope_exit([&] {
        body.instructions = std::move(oldInstructions);
        body.returns = std::move(oldReturns);
        locals = std::move(oldLocals);
        returned = oldReturned;
      });
      body.instructions.clear();
      body.returns.clear();
      locals = std::move(names);
      returned = false;
      if (auto err = instructions(syntaxBody, true, lexical, expected))
        return std::move(err);
      return std::shared_ptr<const lib::Region>(std::make_shared<lib::Region>(
          lib::Region{std::move(inputs), std::move(body.instructions),
                      std::move(body.returns)}));
    }
    Error addRegionInput(const std::string &name, const lib::Type &type,
                         std::vector<lib::Value> &inputs,
                         std::map<std::string, lib::Place> &names,
                         const source::Node &n) {
      auto v = value(type);
      inputs.push_back(v);
      if (!names.emplace(name, lib::Place{v.id, {}}).second)
        return a.fail(n, "library-source-duplicate",
                      "duplicate region input name");
      return Error::success();
    }
    struct CapturePlan {
      std::vector<lib::Place> places;
      std::vector<lib::Type> types;
      std::vector<source::Names> aliases;
    };
    Expected<CapturePlan> capturePlan(const source::Names &names,
                                      bool explicitCaptures,
                                      const source::Node &n) {
      CapturePlan plan;
      std::map<std::pair<uint32_t, std::vector<unsigned>>, unsigned> seen;
      for (const auto &name : names) {
        auto p = named(name, n);
        if (!p)
          return p.takeError();
        auto t = placeType(*p);
        if (!t)
          return t.takeError();
        auto key = std::make_pair(p->value.index, p->path);
        auto found = seen.find(key);
        if (!explicitCaptures && found != seen.end()) {
          plan.aliases[found->second].push_back(name);
          continue;
        }
        seen.emplace(std::move(key), plan.places.size());
        plan.places.push_back(*p);
        plan.types.push_back(*t);
        plan.aliases.push_back({name});
      }
      return plan;
    }
    Error captureInputs(const CapturePlan &plan,
                        std::vector<lib::Value> &inputs,
                        std::map<std::string, lib::Place> &names,
                        const source::Node &n) {
      for (unsigned i = 0; i < plan.places.size(); ++i) {
        auto v = value(plan.types[i]);
        inputs.push_back(v);
        for (const auto &name : plan.aliases[i])
          if (!names.emplace(name, lib::Place{v.id, {}}).second)
            return a.fail(n, "library-source-duplicate",
                          "duplicate region capture name");
      }
      return Error::success();
    }
    Error conditionalRegion(const syntax::Conditional &c,
                            const source::Node &n) {
      if (!c.explicitRegion)
        return a.fail(
            n, "library-source-control",
            "checked conditional requires explicit captures and yields");
      auto input = expression(c.condition);
      if (!input)
        return input.takeError();
      auto t = placeType(*input);
      if (!t)
        return t.takeError();
      if (!lib::sameType(*t, lib::Type::logical("bool")))
        return a.fail(n, "library-condition",
                      "conditional requires a Bool condition");
      lib::Conditional conditional;
      auto &join = conditional.branches;
      join.input = *input;
      auto captures = capturePlan(c.captures, c.explicitCaptures, n);
      if (!captures)
        return captures.takeError();
      join.captures = captures->places;
      for (unsigned index = 0; index < 2; ++index) {
        std::vector<lib::Value> inputs;
        std::map<std::string, lib::Place> names;
        if (auto err = captureInputs(*captures, inputs, names, n))
          return err;
        auto nested = region(index == 0 ? c.thenBody : c.elseBody,
                             std::move(inputs), std::move(names));
        if (!nested)
          return nested.takeError();
        if (auto err = inferJoinOutputs(join, **nested, c.outputs, n))
          return err;
        join.arms.push_back({index == 0 ? "then" : "else", *nested});
      }
      if (auto err = bindJoinOutputs(join, c.outputs, n))
        return err;
      body.instructions.push_back(std::move(conditional));
      returned = lib::terminal(body.instructions);
      return Error::success();
    }
    Error inferJoinOutputs(lib::LocalBranches &join, const lib::Region &region,
                           const source::Names &names, const source::Node &n,
                           StringRef code = "library-source-branch-output") {
      if (lib::terminal(region.instructions))
        return Error::success();
      if (region.returns.size() != names.size())
        return a.fail(n, code, "yield has wrong output arity");
      if (join.outputs.empty())
        for (const auto &p : region.returns) {
          auto t = placeType(p);
          if (!t)
            return t.takeError();
          join.outputs.push_back(value(*t));
        }
      return Error::success();
    }
    Error bindJoinOutputs(const lib::LocalBranches &join,
                          const source::Names &names, const source::Node &n,
                          StringRef code = "library-stop") {
      if (join.outputs.size() != names.size())
        return a.fail(n, code, "all stopping arms cannot produce outputs");
      for (unsigned i = 0; i < names.size(); ++i)
        if (!locals.emplace(names[i], lib::Place{join.outputs[i].id, {}})
                 .second)
          return a.fail(n, "library-source-duplicate",
                        "duplicate branch output binding");
      return Error::success();
    }
    Error matchRegion(const syntax::Match &syntaxMatch, const source::Node &n) {
      auto input = named(syntaxMatch.input, n);
      if (!input)
        return input.takeError();
      auto type = placeType(*input);
      if (!type)
        return type.takeError();
      if (type->kind != lib::Type::Kind::Variant)
        return a.fail(n, "library-source-match",
                      "match requires a finite enum value");
      lib::Match match;
      match.input = *input;
      auto captures =
          capturePlan(syntaxMatch.captures, syntaxMatch.explicitCaptures, n);
      if (!captures)
        return captures.takeError();
      match.captures = captures->places;
      std::map<std::string, const syntax::MatchArm *> arms;
      for (const auto &arm : syntaxMatch.arms) {
        if (!llvm::is_contained(type->fields, arm.alternative))
          return a.fail(arm, "library-source-match-arm",
                        "unknown match alternative");
        if (!arms.emplace(arm.alternative, &arm).second)
          return a.fail(arm, "library-source-match-arm",
                        "duplicate match alternative");
      }
      if (arms.size() != type->fields.size())
        return a.fail(n, "library-source-match-arm",
                      "match must cover every alternative exactly once");
      // Canonical arm order is declaration order; authored order does not
      // change active-arm behavior or descriptor identity.
      for (unsigned index = 0; index < type->fields.size(); ++index) {
        const auto &arm = *arms.at(type->fields[index]);
        std::vector<lib::Value> inputs;
        std::map<std::string, lib::Place> names;
        auto payload = value(type->elements[index]);
        inputs.push_back(payload);
        if (arm.payload.size() == 1)
          names.emplace(arm.payload.front(), lib::Place{payload.id, {}});
        else {
          if (payload.port.type.kind != lib::Type::Kind::Product ||
              arm.payload.size() != payload.port.type.elements.size())
            return a.fail(
                arm, "library-source-match-payload",
                "payload pattern must bind one value or every product field");
          for (unsigned i = 0; i < arm.payload.size(); ++i)
            if (!names.emplace(arm.payload[i], lib::Place{payload.id, {i}})
                     .second)
              return a.fail(arm, "library-source-duplicate",
                            "duplicate payload binding");
        }
        if (auto err = captureInputs(*captures, inputs, names, arm))
          return err;
        auto nested = region(arm.body, std::move(inputs), std::move(names));
        if (!nested)
          return nested.takeError();
        if (auto err = inferJoinOutputs(match, **nested, syntaxMatch.outputs,
                                        arm, "library-source-match-output"))
          return err;
        match.arms.push_back({arm.alternative, *nested});
      }
      if (auto err = bindJoinOutputs(match, syntaxMatch.outputs, n,
                                     "library-source-match-output"))
        return err;
      body.instructions.push_back(std::move(match));
      returned = lib::terminal(body.instructions);
      return Error::success();
    }
    Error traversal(const syntax::ArrayTraversal &loop, const source::Node &n) {
      auto input = named(loop.input, n);
      if (!input)
        return input.takeError();
      auto type = placeType(*input);
      if (!type)
        return type.takeError();
      if (type->kind != lib::Type::Kind::Array)
        return a.fail(n, "library-source-traversal",
                      "traversal requires a typed finite array");
      if (loop.carried.size() != loop.outputs.size())
        return a.fail(n, "library-source-traversal",
                      "traversal output arity must equal carried state arity");
      lib::ArrayTraversal traversal;
      traversal.input = *input;
      std::vector<lib::Value> inputs;
      std::map<std::string, lib::Place> names;
      if (auto err = addRegionInput(loop.element, type->elements.front(),
                                    inputs, names, n))
        return err;
      for (const auto &[name, initial] : loop.carried) {
        auto p = named(initial, n);
        if (!p)
          return p.takeError();
        auto t = placeType(*p);
        if (!t)
          return t.takeError();
        traversal.initial.push_back(*p);
        traversal.outputs.push_back(value(*t));
        if (auto err = addRegionInput(name, *t, inputs, names, n))
          return err;
      }
      auto captures = capturePlan(loop.captures, loop.explicitCaptures, n);
      if (!captures)
        return captures.takeError();
      traversal.captures = captures->places;
      if (auto err = captureInputs(*captures, inputs, names, n))
        return err;
      auto nested = region(loop.body, std::move(inputs), std::move(names));
      if (!nested)
        return nested.takeError();
      traversal.body = *nested;
      for (unsigned i = 0; i < traversal.outputs.size(); ++i)
        if (!locals
                 .emplace(loop.outputs[i],
                          lib::Place{traversal.outputs[i].id, {}})
                 .second)
          return a.fail(n, "library-source-duplicate",
                        "duplicate traversal output binding");
      body.instructions.push_back(std::move(traversal));
      returned = lib::terminal(body.instructions);
      return Error::success();
    }
    Expected<lib::Place> lexicalTraversal(const syntax::Expression &e,
                                          const lib::Type *expected) {
      bool fold = e.kind == syntax::Expression::Kind::Fold;
      if (!e.traversal || e.operands.size() != (fold ? 2u : 1u))
        return a.fail(e, "library-source-traversal",
                      "malformed lexical traversal");
      const auto &step = *e.traversal;
      auto input = expression(e.operands.front());
      if (!input)
        return input.takeError();
      auto inputType = placeType(*input);
      if (!inputType)
        return inputType.takeError();
      if (inputType->kind != lib::Type::Kind::Array)
        return a.fail(e, "library-source-traversal",
                      "traversal requires a finite array");
      lib::ArrayTraversal traversal;
      traversal.input = *input;
      std::vector<lib::Value> inputs;
      std::map<std::string, lib::Place> names;
      if (auto err = addRegionInput(step.element, inputType->elements.front(),
                                    inputs, names, e))
        return std::move(err);
      std::optional<lib::Type> resultType;
      if (fold) {
        auto initial = expression(e.operands[1], expected);
        if (!initial)
          return initial.takeError();
        auto t = placeType(*initial);
        if (!t)
          return t.takeError();
        resultType = *t;
        traversal.initial.push_back(*initial);
        traversal.outputs.push_back(value(*t));
        if (auto err = addRegionInput(step.state, *t, inputs, names, e))
          return std::move(err);
      } else if (expected && expected->kind == lib::Type::Kind::Array)
        resultType = expected->elements.front();
      auto captures = capturePlan(step.captures, false, e);
      if (!captures)
        return captures.takeError();
      traversal.captures = captures->places;
      if (auto err = captureInputs(*captures, inputs, names, e))
        return std::move(err);
      auto nested = region(step.body, std::move(inputs), std::move(names), true,
                           resultType ? &*resultType : nullptr);
      if (!nested)
        return nested.takeError();
      traversal.body = *nested;
      if (!lib::terminal(traversal.body->instructions)) {
        if (traversal.body->returns.size() != 1)
          return a.fail(e, "library-source-traversal",
                        "step must yield one value");
        auto t = placeType(traversal.body->returns.front());
        if (!t)
          return t.takeError();
        if (resultType && !lib::sameType(*resultType, *t))
          return a.fail(e, "library-source-traversal",
                        "step result type differs");
        resultType = *t;
      }
      if (!resultType)
        return a.fail(e, "library-source-traversal",
                      "terminal map requires an expected array type");
      if (!fold)
        traversal.collected =
            value(lib::Type::array(*resultType, inputType->arguments.front()));
      auto result =
          fold ? traversal.outputs.front().id : traversal.collected->id;
      body.instructions.push_back(std::move(traversal));
      return lib::Place{result, {}};
    }
    Error instructions(const syntax::Body &syntaxBody, bool region,
                       bool lexical = false,
                       const lib::Type *stepExpected = nullptr) {
      for (const auto &instruction : syntaxBody) {
        if (instruction.explicitSite)
          return a.fail(
              instruction, "library-source-site",
              "authored occurrence labels need a retained typed site carrier");
        if (returned)
          return a.fail(instruction, "library-source-return",
                        "instruction follows return");
        if (const auto *e = std::get_if<syntax::Exit>(&instruction.value)) {
          if (region && !lexical)
            return a.fail(
                instruction, "library-source-yield",
                "local region must end with yield, not function return");
          const lib::Type *expected = region ? stepExpected
                                      : body.signature.outputs.size() == 1
                                          ? &body.signature.outputs.front().type
                                          : nullptr;
          auto p = expression(e->expression, expected);
          if (!p)
            return p.takeError();
          body.returns.push_back(*p);
          returned = true;
        } else if (const auto *b =
                       std::get_if<syntax::Binding>(&instruction.value)) {
          if (b->assignment || b->mutableBinding)
            return a.fail(instruction, "library-source-control",
                          "mutable binding is unsupported in checked bodies");
          auto expected = annotationType(b->annotation, instruction);
          if (!expected)
            return expected.takeError();
          auto p = expression(b->expression, *expected ? &**expected : nullptr);
          if (!p)
            return p.takeError();
          if (auto err = bind(b->outputs, b->destructure, b->annotation, *p,
                              instruction))
            return err;
        } else if (const auto *c =
                       std::get_if<syntax::Call>(&instruction.value)) {
          if (c->isOperator || c->role)
            return a.fail(instruction, "library-source-call",
                          "operator inference and role-local calls require "
                          "explicit supported nodes");
          syntax::Expression e;
          e.location = c->location;
          e.kind = syntax::Expression::Kind::Call;
          e.name = c->callee;
          e.quoted = c->quoted;
          e.qualified = c->qualified;
          e.staticTerms = c->staticTerms;
          e.staticArguments = c->staticArguments;
          e.attributes = c->attributes;
          e.argumentNames = c->argumentNames;
          for (unsigned i = 0; i < c->inputs.size(); ++i) {
            syntax::Expression v;
            v.name = c->inputs[i];
            v.quoted = i < c->inputAtoms.size() &&
                       c->inputAtoms[i].kind == syntax::Atom::Kind::String;
            e.operands.push_back(v);
          }
          auto expected = annotationType(c->annotation, instruction);
          if (!expected)
            return expected.takeError();
          auto p = expression(e, *expected ? &**expected : nullptr);
          if (!p)
            return p.takeError();
          if (auto err = bind(c->outputs, c->destructure, c->annotation, *p,
                              instruction))
            return err;
        } else if (const auto *stop =
                       std::get_if<source::Stop>(&instruction.value)) {
          if (!stop->role.empty())
            return a.fail(instruction, "library-source-role",
                          "local stop names no participant");
          body.instructions.push_back(lib::Stop{stop->reason});
          returned = true;
        } else if (const auto *yield =
                       std::get_if<source::Yield>(&instruction.value)) {
          if (!region)
            return a.fail(instruction, "library-source-yield",
                          "yield requires a local region");
          for (const auto &name : yield->values) {
            auto p = named(name, instruction);
            if (!p)
              return p.takeError();
            body.returns.push_back(*p);
          }
          returned = true;
        } else if (const auto *conditional =
                       std::get_if<syntax::Conditional>(&instruction.value)) {
          if (auto err = conditionalRegion(*conditional, instruction))
            return err;
        } else if (const auto *match =
                       std::get_if<syntax::Match>(&instruction.value)) {
          if (auto err = matchRegion(*match, instruction))
            return err;
        } else if (const auto *loop = std::get_if<syntax::ArrayTraversal>(
                       &instruction.value)) {
          if (auto err = traversal(*loop, instruction))
            return err;
        } else
          return a.fail(instruction, "library-source-control",
                        "control or protocol instruction is unsupported in "
                        "checked local bodies");
      }
      if (!returned)
        return a.fail(function, "library-source-return",
                      region ? "local region requires an explicit yield"
                             : "checked body requires an explicit return or "
                               "final expression");
      return Error::success();
    }

  public:
    BodyBuilder(Author &a, const syntax::Function &f, const Terms &terms,
                const Types &types, lib::QualifiedDecl id, lib::Signature sig,
                std::vector<lib::Import> imports)
        : a(a), function(f), terms(terms), types(types),
          imports(std::move(imports)) {
      body.id = std::move(id);
      body.signature = std::move(sig);
    }
    Expected<lib::CheckedBody> run() {
      if (!function.body)
        return a.fail(function, "library-source-body",
                      "checked function requires a concrete body");
      for (unsigned i = 0; i < function.arguments.size(); ++i) {
        auto v = value(body.signature.inputs[i].type);
        body.inputs.push_back(v);
        if (!locals.emplace(function.arguments[i].name, lib::Place{v.id, {}})
                 .second)
          return a.fail(function, "library-source-duplicate",
                        "duplicate function argument");
      }
      if (auto error = instructions(*function.body, false))
        return std::move(error);
      auto ownerEnvironment = a.environmentFor(body.id);
      auto checked = lib::checkBody(
          std::move(body), std::move(ownerEnvironment), std::move(imports));
      if (!checked)
        return a.locate(checked.takeError(), function);
      return checked;
    }
  };
  Error form(const syntax::LibraryInterface &s) {
    lib::InterfaceDecl d;
    d.id = id(s.name);
    d.self = lib::StaticTerm::root(id("Self", {s.name}));
    declareStatic(d.self.declaration, lib::Sort::component(), members(s), {},
                  true);
    Terms terms{{"Self", d.self}};
    Types types;
    for (const auto &t : s.types) {
      d.types.push_back({t.name, {t.copy, t.drop}});
      types.emplace(t.name, lib::Type::abstract(d.self, t.name));
    }
    for (const auto &m : s.statics)
      terms.emplace(m.name, lib::StaticTerm::project(d.self, m.name));
    for (const auto &m : s.statics) {
      lib::StaticMember member{m.name, memberSort(m), std::nullopt};
      if (m.equation) {
        auto t = term(*m.equation, terms);
        if (!t)
          return t.takeError();
        member.equation = *t;
      }
      d.statics.push_back(std::move(member));
    }
    for (const auto &facet : s.facets)
      d.facets.push_back({facet.owner, facet.name, facet.required});
    for (const auto &f : s.functions) {
      auto sig = signature(f, terms, types);
      if (!sig)
        return sig.takeError();
      if (!d.functions.emplace(f.name, *sig).second)
        return fail(f, "library-source-duplicate",
                    "duplicate interface function");
    }
    auto ownerEnvironment = environmentFor(d.id);
    auto formed = lib::formInterface(std::move(d), std::move(ownerEnvironment));
    if (!formed)
      return locate(formed.takeError(), s);
    interfaces.emplace(s.name, std::move(*formed));
    report.interfaces.emplace_back(s.name, interfaces.at(s.name));
    return Error::success();
  }
  Expected<lib::CheckedComponent>
  checkComponent(const syntax::LibraryComponent &s, Terms terms) {
    auto interface = interfaces.find(s.interface);
    if (interface == interfaces.end())
      return fail(s, "library-source-interface", "unknown component interface");
    // Retain every declared bound independently of method use. The core owns
    // parametric conformance; a well-typed body alone is not that judgment.
    Types types;
    std::vector<lib::Import> imports;
    for (const auto &parameter : s.parameters)
      if (!parameter.sort && parameter.bounds.size() == 1) {
        auto bound = interfaces.find(parameter.bounds[0]);
        if (bound != interfaces.end())
          imports.push_back({terms.at(parameter.name), bound->second});
      }
    lib::ComponentDecl result{interface->second,  {}, {}, {},
                              std::move(imports), {}, {}};
    // This source profile has no ordinary type parameters or declaration-level
    // requirements. Do not promote method preconditions to template
    // assumptions.
    terms.emplace("Self", interface->second.declaration().self);
    for (const auto &m : s.statics) {
      auto expected =
          llvm::find_if(interface->second.declaration().statics,
                        [&](const auto &x) { return x.name == m.name; });
      if (expected == interface->second.declaration().statics.end() ||
          expected->sort.kind != memberSort(m).kind ||
          expected->sort.domain != memberSort(m).domain)
        return fail(m, "library-source-static",
                    "component static member has unknown name or unequal sort");
      if (!m.equation)
        return fail(m, "library-source-static",
                    "component static member needs an equation");
      auto t = term(*m.equation, terms);
      if (!t)
        return t.takeError();
      if (!result.statics.emplace(m.name, *t).second ||
          !terms.emplace(m.name, *t).second)
        return fail(m, "library-source-duplicate",
                    "duplicate component static member");
    }
    for (const auto &m : s.types) {
      // The parser requires `= type` on every component type member.
      if (!m.representation)
        report_fatal_error("component type member reached checking without a "
                           "representation");
      auto t = type(*m.representation, terms, types);
      if (!t)
        return t.takeError();
      if (!result.representations.emplace(m.name, *t).second ||
          !types.emplace(m.name, *t).second)
        return fail(m, "library-source-duplicate", "duplicate component type");
    }
    for (const auto &f : s.functions) {
      auto sig = signature(f, terms, types);
      if (!sig)
        return sig.takeError();
      auto checked = BodyBuilder(*this, f, terms, types, id(f.name, {s.name}),
                                 *sig, result.imports)
                         .run();
      if (!checked)
        return checked.takeError();
      report.componentBodies.emplace_back(s.name + "::" + f.name, *checked);
      if (!result.functions.emplace(f.name, std::move(*checked)).second)
        return fail(f, "library-source-duplicate",
                    "duplicate component function");
    }
    return lib::checkComponent(std::move(result), environmentFor(id(s.name)));
  }
  Expected<std::shared_ptr<const lib::Implementation>>
  select(const syntax::LibraryTerm &s) {
    if (!s.members.empty() || s.root.kind != syntax::Atom::Kind::Name)
      return fail(s, "library-source-selection",
                  "link actual must select a declared component");
    if (auto alias = aliases.find(s.root.value); alias != aliases.end()) {
      auto selected = term(s, {});
      if (!selected)
        return selected.takeError();
      auto key = lib::selectionIdentity(*selected, environment);
      if (!key)
        return key.takeError();
      auto cached = selections.find(*key);
      if (cached != selections.end())
        return cached->second;
      // term() already bounded and rejected alias cycles before recursive
      // selection.
      auto target = select(alias->second->target);
      if (!target)
        return target.takeError();
      if (!alias->second->sealed)
        return *target;
      auto result = std::make_shared<lib::Implementation>(**target);
      result->selection = *selected;
      selections.emplace(*key, result);
      return std::shared_ptr<const lib::Implementation>(std::move(result));
    }
    auto found = components.find(s.root.value);
    if (found == components.end())
      return fail(s, "library-source-selection", "unknown selected component");
    auto selected = term(s, {});
    if (!selected)
      return selected.takeError();
    auto key = lib::selectionIdentity(*selected, environment);
    if (!key)
      return key.takeError();
    auto cached = selections.find(*key);
    if (cached != selections.end())
      return cached->second;
    if (active.size() >= 64 || !active.insert(*key).second ||
        selections.size() >= 1024)
      return fail(s, "library-source-cycle",
                  "component selection cycle or expansion limit");
    const auto &definition = *found->second;
    if (definition.parameters.size() != selected->arguments.size())
      return fail(s, "library-source-selection",
                  "wrong component actual arity");
    const auto &component = templates.at(definition.name);
    const auto &d = component.checked.declaration();
    auto result = std::make_shared<lib::Implementation>(
        lib::Implementation{component.selection,
                            d.interface,
                            d.representations,
                            d.statics,
                            d.functions,
                            {},
                            {},
                            d.imports,
                            d.typeBounds,
                            d.requirements,
                            component.checked.environment()});
    for (unsigned n = 0; n < definition.parameters.size(); ++n) {
      const auto &parameter = definition.parameters[n];
      auto formal =
          lib::StaticTerm::root(id(parameter.name, {definition.name}));
      auto sort = parameterSort(parameter);
      if (!sort)
        return sort.takeError();
      if (sort->kind == lib::Sort::Kind::Component) {
        auto dependency = select(s.arguments[n]);
        if (!dependency)
          return dependency.takeError();
        result->dependencies.push_back(
            {formal, *dependency, definition.name + "/" + parameter.name});
      } else
        result->arguments.statics.push_back({formal, selected->arguments[n]});
    }
    active.erase(*key);
    selections.emplace(*key, result);
    return std::shared_ptr<const lib::Implementation>(std::move(result));
  }
  Error prepareClient(const syntax::Function &f) {
    if (callables.count(f.name))
      return Error::success();
    Terms terms;
    std::vector<lib::Import> imports;
    std::vector<std::string> names;
    std::vector<lib::QualifiedDecl> parameters;
    for (const auto &p : f.parameters) {
      auto sort = parameterSort(p);
      if (!sort)
        return sort.takeError();
      auto q = id(p.name, {f.name});
      declareStatic(q, *sort, parameterMembers(p), {}, true);
      auto t = lib::StaticTerm::root(q);
      if (!terms.emplace(p.name, t).second)
        return fail(p, "library-source-duplicate",
                    "duplicate helper parameter");
      if (sort->kind == lib::Sort::Kind::Component) {
        componentBounds[lib::identity(t)] = p.bounds.front();
        imports.push_back({t, interfaces.at(p.bounds.front())});
      }
      names.push_back(p.name);
      parameters.push_back(q);
    }
    auto ordinary = f;
    ordinary.generic = false;
    auto sig = signature(ordinary, terms, {});
    if (!sig)
      return sig.takeError();
    auto callable =
        lib::formCallable({id(f.name), *sig, parameters, {}, imports},
                          environmentFor(id(f.name)));
    if (!callable)
      return callable.takeError();
    callables.emplace(f.name, std::move(*callable));
    callableTerms.emplace(f.name, std::move(terms));
    clientParameters.emplace(f.name, std::move(names));
    return Error::success();
  }
  Error checkClient(const syntax::Function &f) {
    if (clients.count(f.name))
      return Error::success();
    if (auto error = prepareClient(f))
      return error;
    if (!f.body) {
      externalCallables.insert(f.name);
      return Error::success();
    }
    const auto &d = callables.at(f.name).declaration();
    const Types types;
    auto checked = BodyBuilder(*this, f, callableTerms.at(f.name), types, d.id,
                               d.signature, d.imports)
                       .run();
    if (!checked)
      return checked.takeError();
    clients.emplace(f.name, std::move(*checked));
    report.clients.emplace_back(f.name, clients.at(f.name));
    return Error::success();
  }
  Error checkHelpers() {
    // Calls may discover further ordinary or generic helpers. Each receives
    // the same checked-body judgment; an unchecked body is never trusted.
    while (clients.size() + externalCallables.size() != callables.size()) {
      if (callables.size() > environment.expansionLimit)
        return fail(source, "library-source-limit", "too many source helpers");
      for (const auto &f : source.functions)
        if (callables.count(f.name) && !clients.count(f.name) &&
            !externalCallables.count(f.name))
          if (auto error = checkClient(f))
            return error;
    }
    std::map<std::string, unsigned> colors;
    std::function<Error(const lib::CheckedBody &, unsigned)> visit;
    visit = [&](const lib::CheckedBody &body, unsigned depth) -> Error {
      auto &color = colors[lib::identity(body.body().id)];
      if (color == 2)
        return Error::success();
      if (color == 1 || depth > 128)
        return fail(source, "library-call-cycle",
                    "recursive or excessive source helper graph");
      color = 1;
      std::function<Error(const std::vector<lib::Instruction> &)> walk;
      walk = [&](const auto &instructions) -> Error {
        for (const auto &i : instructions) {
          if (auto *c = std::get_if<lib::Call>(&i)) {
            if (auto *s = std::get_if<lib::SourceCall>(&c->target)) {
              auto found = llvm::find_if(clients, [&](const auto &entry) {
                return lib::identity(entry.second.body().id) ==
                       lib::identity(s->callable.declaration().id);
              });
              if (found != clients.end())
                if (auto error = visit(found->second, depth + 1))
                  return error;
            }
          } else if (auto *b = lib::branches(i)) {
            for (const auto &arm : b->arms)
              if (auto error = walk(arm.body->instructions))
                return error;
          } else if (auto *t = std::get_if<lib::ArrayTraversal>(&i))
            if (auto error = walk(t->body->instructions))
              return error;
        }
        return Error::success();
      };
      if (auto error = walk(body.body().instructions))
        return error;
      color = 2;
      return Error::success();
    };
    for (const auto &body : clients)
      if (auto error = visit(body.second, 0))
        return error;
    return Error::success();
  }
  Expected<lowering::LibrarySource> run();
};

// This bridge is deliberately after core checking, linking and representation
// selection. It does not reparse text or specialize an unchecked generic body.
Expected<lowering::LibrarySource> Author::run() {
  if (!source.project && source.libraryIdentities.size() != 1)
    return fail(
        source, "library-source-identity",
        "checked libraries require exactly one explicit captured identity");
  if (source.profile)
    return fail(source, "library-source-profile",
                "checked libraries require an explicit-binding module");
  if (source.project) {
    identity = source.project->owners.front().identity;
    for (const auto &owner : source.project->owners)
      environment.libraries.push_back({owner.identity, {}});
    for (const auto &d : source.project->declarations)
      id(d.symbol);
  } else {
    const auto &i = source.libraryIdentities.front();
    identity = {i.nameSpace, i.name, i.version, i.resolution};
    environment.libraries.push_back({identity, {}});
  }
  // Installed contracts are one fixed environment, not a caller-discovered
  // subset. An unrelated dependent cannot change a library's judgment identity.
  auto captureInstalled = [&](StringRef name) -> Error {
    syntax::Atom atom;
    atom.kind = syntax::Atom::Kind::String;
    atom.value = name.str();
    auto value = root(atom, {});
    return value ? Error::success() : value.takeError();
  };
  for (const auto &d : protocol::installedDomains().allDomains())
    if (auto error = captureInstalled(d.identity))
      return error;
  for (const auto &c : protocol::installedDomains().allCodecs())
    if (auto error = captureInstalled(c.identity))
      return error;
  for (const auto &t : protocol::boundTypeConstructors())
    environment.logicalTypes.push_back({t, true});
  for (const auto &op : protocol::boundOperationContracts())
    environment.operations.push_back({op, {"local"}});
  for (const auto &rule : protocol::boundCapabilityRules())
    environment.implications.push_back(rule);
  std::set<std::string> names;
  auto reserve = [&](const auto &items) -> Error {
    for (const auto &d : items)
      if (!names.insert(d.name).second)
        return fail(d, "library-source-duplicate",
                    "duplicate module declaration '" + d.name + "'");
    return Error::success();
  };
  if (auto e = reserve(source.libraryInterfaces))
    return e;
  if (auto e = reserve(source.libraryAssociations))
    return e;
  if (auto e = reserve(source.libraryComponents))
    return e;
  if (auto e = reserve(source.librarySelections))
    return e;
  if (auto e = reserve(source.libraryLinks))
    return e;
  if (auto e = reserve(source.functions))
    return e;
  if (auto e = reserve(source.bindings))
    return e;
  if (auto e = reserve(source.protocols))
    return e;
  if (auto e = reserve(source.structs))
    return e;
  if (auto e = reserve(source.enums))
    return e;
  if (auto e = reserve(source.bundles))
    return e;
  if (auto e = reserve(source.constants))
    return e;
  if (auto e = reserve(source.relations))
    return e;
  if (auto e = reserve(source.instances))
    return e;
  if (auto e = reserve(source.entries))
    return e;
  if (auto e = reserve(source.configurations))
    return e;
  for (const auto &s : source.libraryAssociations) {
    auto q = id(s.name);
    declareStatic(q, lib::Sort::association());
    environment.statics.back().capturedSubject = s.captured;
    capturedAssociations.emplace(s.name, lib::StaticTerm::root(q));
    report.associations.push_back({s.name, "opaque", s.captured});
  }
  for (const auto &r : source.relations) {
    if (!std::visit([](const auto &value) { return bool(value); }, r.value))
      return fail(r, "relation-unresolved",
                  "relation association requires a resolved descriptor");
    auto descriptor =
        std::visit([](const auto &value) { return value->encode(); }, r.value);
    auto canonical = zkc::printJson(descriptor);
    auto q = id(r.name);
    declareStatic(q, lib::Sort::association());
    environment.statics.back().capturedSubject = canonical;
    capturedAssociations.emplace(r.name, lib::StaticTerm::root(q));
    report.associations.push_back(
        {r.name, r.value.index() == 0 ? "r1cs" : "air", std::move(canonical)});
  }
  // Validate every enum declaration, including unused and phantom parameters,
  // in its own abstract scope before any client is selected.
  for (const auto &enumeration : source.enums) {
    Terms terms;
    syntax::Type spelling;
    spelling.name = enumeration.name;
    for (const auto &parameter : enumeration.parameters) {
      auto sort = parameterSort(parameter);
      if (!sort)
        return sort.takeError();
      auto q = id(parameter.name, {enumeration.name});
      declareStatic(q, *sort, parameterMembers(parameter), {}, true);
      auto formal = lib::StaticTerm::root(q);
      if (!terms.emplace(parameter.name, formal).second)
        return fail(parameter, "library-source-duplicate",
                    "duplicate enum parameter");
      if (sort->kind == lib::Sort::Kind::Component)
        componentBounds[lib::identity(formal)] = parameter.bounds.front();
      syntax::Type argument;
      argument.name = parameter.name;
      spelling.arguments.push_back(std::move(argument));
    }
    auto checked = type(spelling, terms, {});
    if (!checked)
      return checked.takeError();
  }
  for (const auto &s : source.libraryComponents)
    components.emplace(s.name, &s);
  for (const auto &s : source.librarySelections)
    aliases.emplace(s.name, &s);
  // Capture installed domain descriptors from actuals without selecting any
  // implementation or making its representation available to client checking.
  std::function<Error(const syntax::LibraryTerm &)> capture =
      [&](const auto &t) -> Error {
    if (!protocol::installedIdentitySort(t.root.value).empty()) {
      auto captured = root(t.root, {});
      if (!captured)
        return captured.takeError();
    }
    for (const auto &arg : t.arguments)
      if (auto e = capture(arg))
        return e;
    return Error::success();
  };
  for (const auto &link : source.libraryLinks)
    for (const auto &arg : link.arguments)
      if (auto e = capture(arg))
        return e;
  for (const auto &alias : source.librarySelections)
    if (auto e = capture(alias.target))
      return e;
  // Capture public constructor signatures before freezing interfaces. This
  // also lets a component with only type/static members link without relying
  // on a method body's environment to carry its constructor declaration.
  for (const auto &s : source.libraryComponents) {
    auto interface =
        llvm::find_if(source.libraryInterfaces,
                      [&](const auto &x) { return x.name == s.interface; });
    if (interface == source.libraryInterfaces.end())
      return fail(s, "library-source-interface", "unknown component interface");
    std::vector<lib::Sort> sorts;
    for (const auto &p : s.parameters) {
      auto sort = parameterSort(p);
      if (!sort)
        return sort.takeError();
      sorts.push_back(*sort);
      declareStatic(id(p.name, {s.name}), *sort, parameterMembers(p), {}, true);
    }
    declareStatic(id(s.name), lib::Sort::component(), members(*interface),
                  std::move(sorts));
  }
  for (const auto &alias : source.librarySelections) {
    syntax::LibraryTerm selected;
    selected.location = alias.location; // Refusals inside name the alias.
    selected.root.value = alias.name;
    auto t = term(selected, {});
    if (!t)
      return t.takeError();
    auto sort = lib::sortOf(*t, environment);
    if (!sort)
      return sort.takeError();
    if (sort->kind != lib::Sort::Kind::Component)
      return fail(alias, "library-source-selection",
                  "selection alias must name a component");
  }
  for (const auto &s : source.libraryInterfaces)
    declareStatic(id("Self", {s.name}), lib::Sort::component(), members(s), {},
                  true);
  for (const auto &s : source.libraryComponents)
    for (const auto &f : s.functions)
      id(f.name, {s.name});
  for (const auto &f : source.functions) {
    id(f.name);
    for (const auto &p : f.parameters) {
      auto sort = parameterSort(p);
      if (!sort) {
        // Ordinary polymorphic declarations use their own checker until they
        // are called on the checked library path, which validates its sorts.
        consumeError(sort.takeError());
        continue;
      }
      declareStatic(id(p.name, {f.name}), *sort, parameterMembers(p), {}, true);
    }
  }
  for (const auto &s : source.libraryInterfaces)
    if (auto e = form(s))
      return e;
  // Interface-generic clients and explicit link roots take the checked path.
  // Other helpers enter on demand; unrelated ordinary generics keep their
  // route.
  for (const auto &f : source.functions) {
    bool client =
        (f.body && syntax::hasLexicalTraversals(*f.body)) ||
        llvm::any_of(f.parameters,
                     [&](const auto &p) {
                       return llvm::any_of(p.bounds, [&](const auto &b) {
                         return interfaces.count(b);
                       });
                     }) ||
        llvm::any_of(source.libraryLinks,
                     [&](const auto &link) { return link.client == f.name; });
    if (client)
      if (auto e = checkClient(f))
        return e;
  }
  for (const auto &s : source.libraryComponents) {
    auto interface =
        llvm::find_if(source.libraryInterfaces,
                      [&](const auto &x) { return x.name == s.interface; });
    if (interface == source.libraryInterfaces.end())
      return fail(s, "library-source-interface", "unknown component interface");
    std::vector<lib::Sort> sorts;
    Terms terms;
    for (const auto &p : s.parameters) {
      auto sort = parameterSort(p);
      if (!sort)
        return sort.takeError();
      sorts.push_back(*sort);
      auto q = id(p.name, {s.name});
      declareStatic(q, *sort, parameterMembers(p), {}, true);
      if (sort->kind == lib::Sort::Kind::Component)
        componentBounds[lib::identity(lib::StaticTerm::root(q))] = p.bounds[0];
      if (!terms.emplace(p.name, lib::StaticTerm::root(q)).second)
        return fail(p, "library-source-duplicate",
                    "duplicate component parameter");
    }
    auto q = id(s.name);
    declareStatic(q, lib::Sort::component(), members(*interface), sorts);
    std::vector<lib::StaticTerm> args;
    for (const auto &p : s.parameters)
      args.push_back(terms.at(p.name));
    auto selection = args.empty() ? lib::StaticTerm::root(q)
                                  : lib::StaticTerm::apply(q, std::move(args));
    auto checked = checkComponent(s, std::move(terms));
    if (!checked)
      return locate(
          checked.takeError(), s,
          {cause(DiagnosticCause::Kind::ImportedInterface,
                 interfaces.at(s.interface).declaration().id,
                 "component must implement this exact interface"),
           cause(DiagnosticCause::Kind::SelectedComponent, q,
                 "component declaration under conformance checking")});
    report.components.emplace_back(s.name, *checked);
    templates.emplace(
        s.name, ComponentTemplate{std::move(selection), std::move(*checked)});
  }
  if (auto error = checkHelpers())
    return std::move(error);
  // A caller of an abstract checked helper needs the same checked call path.
  // Closed helpers keep ordinary aliases below, so they do not force unrelated
  // ordinary functions onto that path.
  if (source.project) {
    bool changed = true;
    while (changed) {
      changed = false;
      for (const auto &f : source.functions) {
        if (callables.count(f.name))
          continue;
        bool required =
            llvm::any_of(source.project->references, [&](const auto &edge) {
              return !edge.signature && edge.source == f.name &&
                     callables.count(edge.target) &&
                     !clientParameters.at(edge.target).empty();
            });
        if (required) {
          if (auto error = checkClient(f))
            return error;
          changed = true;
        }
      }
      if (auto error = checkHelpers())
        return std::move(error);
    }
  }
  syntax::Module out = source;
  out.enums.clear();
  out.libraryIdentities.clear();
  out.libraryAssociations.clear();
  out.libraryInterfaces.clear();
  out.libraryComponents.clear();
  out.libraryLinks.clear();
  out.librarySelections.clear();
  llvm::erase_if(out.functions,
                 [&](const auto &f) { return callables.count(f.name); });
  std::vector<lib::LinkedProgram> programs;
  std::map<std::string, source::Names> entryAliases;
  auto requestedLinks = source.libraryLinks;
  // configure is the ordinary spelling for a closed named static selection.
  // Reuse the checked linker when its target owns a checked callable, retaining
  // source terms (quotation and projections) rather than decoding strings.
  for (const auto &config : source.configurations) {
    if (!callables.count(config.base))
      continue;
    if (!config.implementations.empty())
      return fail(config, "library-source-configuration",
                  "checked helper configuration does not select primitive "
                  "implementations");
    const auto &parameters = clientParameters.at(config.base);
    const auto metadata = source.configurationTerms.find(config.name);
    if (config.arguments.size() != parameters.size() ||
        metadata == source.configurationTerms.end() ||
        metadata->second.size() != config.arguments.size())
      return fail(
          config, "library-source-configuration",
          "configuration must supply every checked static parameter once");
    syntax::LibraryLink link;
    link.location = config.location;
    link.name = config.name;
    link.client = config.base;
    std::set<std::string> bound;
    for (const auto &parameter : parameters) {
      auto found = llvm::find_if(config.arguments, [&](const auto &arg) {
        return arg.first == parameter;
      });
      if (found == config.arguments.end() ||
          !bound.insert(found->first).second ||
          llvm::count_if(config.arguments, [&](const auto &arg) {
            return arg.first == parameter;
          }) != 1)
        return fail(config, "library-source-configuration",
                    "unknown, duplicate or missing checked static parameter");
      const auto &term = metadata->second[found - config.arguments.begin()];
      syntax::LibraryTerm actual;
      actual.root = term.root;
      actual.members = term.members;
      link.arguments.push_back(std::move(actual));
    }
    requestedLinks.push_back(std::move(link));
    out.configurationTerms.erase(config.name);
  }
  llvm::erase_if(out.configurations,
                 [&](const auto &c) { return callables.count(c.base); });
  // A checked closed helper remains callable under its authored name. This
  // applies equally to a lexical traversal and to an ordinary helper reached
  // from a checked client; checking it must not erase the public callable.
  for (const auto &[name, body] : clients)
    if (clientParameters.at(name).empty()) {
      syntax::LibraryLink link;
      link.name = name;
      link.client = name;
      if (source.project)
        if (const auto *d = source.project->lookup(name))
          link.location = d->location;
      requestedLinks.push_back(std::move(link));
    }
  for (const auto &link : requestedLinks) {
    auto client = clients.find(link.client);
    if (client == clients.end())
      return fail(link,
                  externalCallables.count(link.client) ? "library-open-call"
                                                       : "library-source-link",
                  "link requires a checked source client body");
    if (link.arguments.size() != clientParameters.at(link.client).size())
      return fail(link, "library-source-link",
                  "link has wrong component arity");
    std::vector<DiagnosticCause> context;
    context.push_back(cause(DiagnosticCause::Kind::Declaration,
                            callables.at(link.client).declaration().id,
                            "checked client selected by this link"));
    lib::LinkRequest request{client->second, {}, {}};
    request.selectionEnvironment = environmentFor(id(link.name));
    for (const auto &helper : clients)
      request.helpers.push_back(helper.second);
    for (unsigned n = 0; n < link.arguments.size(); ++n) {
      auto formal = lib::StaticTerm::root(
          callables.at(link.client).declaration().parameters[n]);
      auto sort = lib::sortOf(formal, environment);
      if (!sort)
        return sort.takeError();
      if (sort->kind == lib::Sort::Kind::Component) {
        auto selected = select(link.arguments[n]);
        if (!selected)
          return locate(selected.takeError(), link, context);
        auto actual = term(link.arguments[n], {});
        if (!actual)
          return locate(actual.takeError(), link, context);
        context.push_back({DiagnosticCause::Kind::SelectedComponent,
                           lib::identity(*actual),
                           "exact component selected for this static parameter",
                           link.location});
        context.push_back(
            cause(DiagnosticCause::Kind::ImportedInterface,
                  (*selected)->interface.declaration().id,
                  "selected component's checked public interface"));
        request.bindings.push_back(
            {formal, *selected,
             link.name + "/" + clientParameters.at(link.client)[n]});
      } else {
        auto selected = term(link.arguments[n], {});
        if (!selected)
          return selected.takeError();
        if (sort->kind == lib::Sort::Kind::Association)
          context.push_back(
              {DiagnosticCause::Kind::CapturedSubject, lib::identity(*selected),
               "captured association supplied to this link", link.location});
        request.arguments.statics.push_back({formal, *selected});
      }
    }
    auto linked = lib::link(std::move(request));
    if (!linked)
      return locate(linked.takeError(), link, std::move(context));
    report.links.emplace_back(link.name, *linked);
    entryAliases[linked->entry()].push_back(link.name);
    programs.push_back(std::move(*linked));
  }
  auto emitted = lowering::emitLibrarySource(std::move(out), environment,
                                             programs, entryAliases, names);
  if (!emitted)
    return locate(emitted.takeError(), source);
  return std::move(*emitted);
}
} // namespace
bool hasLibraries(const syntax::Module &m) {
  return !m.libraryIdentities.empty() || !m.libraryAssociations.empty() ||
         !m.libraryInterfaces.empty() || !m.libraryComponents.empty() ||
         !m.libraryLinks.empty() || !m.librarySelections.empty() ||
         !m.enums.empty() || llvm::any_of(m.functions, [](const auto &f) {
           return f.body && syntax::hasLexicalTraversals(*f.body);
         });
}
LibraryElaboration elaborateLibraries(const syntax::Module &m, StringRef text,
                                      StringRef filename) {
  if (!hasLibraries(m))
    return {lowering::LibrarySource{m, {}}, {}};
  auto report = std::make_unique<model::LibraryReport>();
  auto result = Author(m, text, filename, *report).run();
  if (result)
    return {std::move(result), std::move(report)};
  Error error = Error::success();
  handleAllErrors(
      result.takeError(),
      [&](const SourceDiagnostic &d) {
        error = m.project ? diagnostic(m.project->input,
                                       Diagnostic{d.code, d.message, d.location,
                                                  d.related, d.causes})
                          : diagnostic(text, filename, d.location.offset,
                                       d.code, d.message);
      },
      [&](const lib::Diagnostic &d) {
        error = diagnostic(text, filename, m.location ? m.location->offset : 0,
                           d.code, d.message);
      },
      [&](const Refusal &e) {
        // A check of the lowered library source keeps its own identifier; the
        // module is the only location it has.
        error = diagnostic(text, filename, m.location ? m.location->offset : 0,
                           e.code, e.detail);
      });
  return {std::move(error), std::move(report)};
}
} // namespace zkc::frontend::semantics
