#include "LinkInternal.h"
#include <algorithm>

namespace zkc::frontend::library {
namespace {
using namespace detail;
// The only representation authority here is the current implementation's Self.
// Imported abstract types stay opaque, even if a concrete selection is known.
struct TemplateScope {
  const ComponentDecl &component;
  llvm::Expected<StaticTerm> term(const StaticTerm &t,
                                  unsigned depth = 0) const {
    if (depth > 128)
      return fail("library-substitution-cycle", "component static cycle");
    if (t.kind == StaticTerm::Kind::Project && t.arguments.size() == 1 &&
        identity(t.arguments[0]) ==
            identity(component.interface.declaration().self)) {
      auto found = component.statics.find(t.member);
      if (found != component.statics.end())
        return term(found->second, depth + 1);
    }
    StaticTerm out = t;
    for (auto &a : out.arguments) {
      auto v = term(a, depth + 1);
      if (!v)
        return v.takeError();
      a = *v;
    }
    return out;
  }
  llvm::Expected<Type> type(const Type &t, unsigned depth = 0) const {
    if (depth > 128)
      return fail("library-representation-cycle", "component type cycle");
    if (t.kind == Type::Kind::Abstract && t.arguments.size() == 1 &&
        identity(t.arguments[0]) ==
            identity(component.interface.declaration().self)) {
      auto found = component.representations.find(t.name);
      if (found == component.representations.end())
        return fail("library-representation", "missing own type member");
      return type(found->second, depth + 1);
    }
    Type out = t;
    for (auto &a : out.arguments) {
      auto v = term(a);
      if (!v)
        return v.takeError();
      a = *v;
    }
    for (auto &a : out.elements) {
      auto v = type(a, depth + 1);
      if (!v)
        return v.takeError();
      a = *v;
    }
    return out;
  }
  llvm::Expected<std::vector<Requirement>>
  requirements(std::vector<Requirement> rs) const {
    for (auto &r : rs)
      for (auto &a : r.arguments) {
        auto v = term(a);
        if (!v)
          return v.takeError();
        a = *v;
      }
    return rs;
  }
  llvm::Expected<Signature> signature(Signature s) const {
    for (auto *ps : {&s.inputs, &s.outputs})
      for (auto &p : *ps) {
        auto t = type(p.type);
        if (!t)
          return t.takeError();
        p.type = *t;
      }
    auto pre = requirements(s.preconditions);
    if (!pre)
      return pre.takeError();
    s.preconditions = *pre;
    auto post = requirements(s.postconditions);
    if (!post)
      return post.takeError();
    s.postconditions = *post;
    return s;
  }
};
llvm::Error signatureConformance(const Signature &promised,
                                 const Signature &provided,
                                 const std::vector<Requirement> &global,
                                 const Environment &environment) {
  if (promised.inputs.size() != provided.inputs.size() ||
      promised.outputs.size() != provided.outputs.size())
    return fail("library-conformance", "member port arity mismatch");
  auto ports = [&](const auto &as, const auto &bs) -> llvm::Error {
    for (size_t i = 0; i < as.size(); ++i) {
      if (as[i].role != bs[i].role)
        return fail("library-role", "implementation role mismatch");
      if (auto err = equalTypes(as[i].type, bs[i].type, global, environment))
        return err;
    }
    return llvm::Error::success();
  };
  if (auto err = ports(promised.inputs, provided.inputs))
    return err;
  if (auto err = ports(promised.outputs, provided.outputs))
    return err;
  if (!std::includes(promised.effects.begin(), promised.effects.end(),
                     provided.effects.begin(), provided.effects.end()))
    return fail("library-effect",
                "implementation strengthens effect requirements");
  auto facts = global;
  facts.insert(facts.end(), promised.preconditions.begin(),
               promised.preconditions.end());
  if (auto err = prove(facts, provided.preconditions, environment))
    return fail("library-precondition", llvm::toString(std::move(err)));
  facts.insert(facts.end(), provided.postconditions.begin(),
               provided.postconditions.end());
  if (auto err = prove(facts, promised.postconditions, environment))
    return fail("library-postcondition", llvm::toString(std::move(err)));
  return llvm::Error::success();
}
} // namespace
struct CheckedComponent::Data {
  ComponentDecl declaration;
  Environment environment;
  std::string identity, fingerprint;
};
CheckedComponent::CheckedComponent(std::shared_ptr<const Data> d)
    : data(std::move(d)) {}
const ComponentDecl &CheckedComponent::declaration() const {
  return data->declaration;
}
const Environment &CheckedComponent::environment() const {
  return data->environment;
}
const std::string &CheckedComponent::identity() const { return data->identity; }
const std::string &CheckedComponent::fingerprint() const {
  return data->fingerprint;
}
llvm::Expected<CheckedComponent> checkComponent(ComponentDecl d,
                                                Environment e) {
  using namespace detail;
  if (auto err = validateEnvironment(e))
    return err;
  if (auto err = importsInterface(d.interface, e))
    return err;
  const auto &iface = d.interface.declaration();
  if (d.representations.size() != iface.types.size() ||
      d.statics.size() != iface.statics.size() ||
      d.functions.size() != iface.functions.size())
    return fail("library-conformance",
                "implementation member set differs from interface");
  // Bodies and components authenticate assumptions through the same owner.
  auto formed = assumptions(d.typeBounds, d.imports, d.requirements, e);
  if (!formed)
    return formed.takeError();
  for (const auto &i : d.imports)
    if (library::identity(i.parameter) == library::identity(iface.self))
      return fail("library-import", "dependency shadows component Self");
  TypeContext ctx{e, d.imports, d.typeBounds};
  auto bounds = [&](const std::vector<TypeBound> &bs) -> llvm::Error {
    for (const auto &b : bs) {
      auto p = permissions(Type::parameter(b.parameter), ctx);
      if (!p)
        return p.takeError();
      if ((b.permissions.copy && !p->copy) || (b.permissions.drop && !p->drop))
        return fail("library-permission-bound",
                    "member assumes stronger type bound");
    }
    return llvm::Error::success();
  };
  if (auto err = bounds(iface.typeBounds))
    return err;
  TemplateScope scope{d};
  auto facts = std::move(*formed);
  for (const auto &slot : iface.types) {
    auto rep = d.representations.find(slot.name);
    if (rep == d.representations.end())
      return fail("library-representation", "missing type member " + slot.name);
    auto formedType = permissions(
        rep->second, TypeContext{e, d.imports, d.typeBounds, &iface});
    if (!formedType)
      return formedType.takeError();
    auto t = scope.type(rep->second);
    if (!t)
      return t.takeError();
    auto p = permissions(*t, ctx);
    if (!p)
      return p.takeError();
    if ((slot.permissions.copy && !p->copy) ||
        (slot.permissions.drop && !p->drop))
      return fail("library-permission-bound",
                  "representation violates copy/drop bound on " + slot.name);
  }
  for (const auto &m : iface.statics) {
    auto found = d.statics.find(m.name);
    if (found == d.statics.end())
      return fail("library-static-member", "missing static member " + m.name);
    auto actual = scope.term(found->second);
    if (!actual)
      return actual.takeError();
    auto sort = sortOf(*actual, e);
    if (!sort)
      return sort.takeError();
    if (!sameSort(*sort, m.sort))
      return fail("library-static-sort", "associated member sort mismatch");
    if (m.equation) {
      auto expected = scope.term(*m.equation);
      if (!expected)
        return expected.takeError();
      if (auto err = prove(facts, {{"", {*actual, *expected}}}, e))
        return err;
    }
  }
  auto required = scope.requirements(iface.requirements);
  if (!required)
    return required.takeError();
  if (auto err = prove(facts, *required, e))
    return err;
  for (const auto &member : iface.functions) {
    auto found = d.functions.find(member.first);
    if (found == d.functions.end())
      return fail("library-conformance", "missing function " + member.first);
    const auto &body = found->second;
    if (auto err = extends(body.environment(), e))
      return err;
    for (const auto &import : body.imports()) {
      auto declared = std::find_if(d.imports.begin(), d.imports.end(),
                                   [&](const Import &i) {
                                     return library::identity(i.parameter) ==
                                            library::identity(import.parameter);
                                   });
      if (declared == d.imports.end() ||
          declared->interface.identity() != import.interface.identity())
        return fail("library-interface-drift",
                    "body import has no exact persistent component bound");
    }
    if (auto err = bounds(body.body().typeBounds))
      return err;
    auto promised = scope.signature(member.second);
    if (!promised)
      return promised.takeError();
    auto provided = scope.signature(body.body().signature);
    if (!provided)
      return provided.takeError();
    if (auto err = signature(*promised, ctx))
      return err;
    if (auto err = signature(*provided, ctx))
      return err;
    if (auto err = signatureConformance(*promised, *provided, facts, e))
      return err;
  }
  for (const auto &f : iface.facets)
    if (f.required && !(f.owner == "zkc.frontend.library" &&
                        (f.name == "resources" || f.name == "effects")))
      return fail("library-required-facet",
                  "unsupported required facet " + f.owner + "/" + f.name);
  Writer content;
  content.add(d.interface.identity());
  content.add(encode(e));
  content.list(d.representations, [&](const auto &p) {
    content.add(p.first);
    content.add(library::identity(p.second));
  });
  content.list(d.statics, [&](const auto &p) {
    content.add(p.first);
    content.add(library::identity(p.second));
  });
  content.list(d.functions, [&](const auto &p) {
    content.add(p.first);
    content.add(p.second.identity());
  });
  std::map<std::string, std::string> imports;
  for (const auto &i : d.imports)
    imports.emplace(library::identity(i.parameter), i.interface.identity());
  content.list(imports, [&](const auto &p) {
    content.add(p.first);
    content.add(p.second);
  });
  Body obligations;
  obligations.typeBounds = d.typeBounds;
  obligations.signature.preconditions = d.requirements;
  content.add(encode(obligations));
  auto data = std::make_shared<CheckedComponent::Data>(CheckedComponent::Data{
      std::move(d), std::move(e), content.bytes, hash(content.bytes)});
  return CheckedComponent(std::move(data));
}
} // namespace zkc::frontend::library

namespace zkc::frontend::library::detail {
llvm::Error World::conform(Selection &node) {
  const auto &impl = node.implementation;
  const auto &iface = impl.interface.declaration();
  if (impl.representations.size() != iface.types.size() ||
      impl.statics.size() != iface.statics.size() ||
      impl.functions.size() != iface.functions.size())
    return fail("library-conformance",
                "implementation member set differs from interface");
  if (auto err = bounds(impl.typeBounds, node.scope))
    return err;
  auto templateRequirements = requirements(impl.requirements, node.scope);
  if (!templateRequirements)
    return templateRequirements.takeError();
  if (auto err = prove({}, *templateRequirements, environment))
    return err;
  if (auto err = bounds(iface.typeBounds, node.scope))
    return err;
  for (const auto &slot : iface.types) {
    auto representation = impl.representations.find(slot.name);
    if (representation == impl.representations.end())
      return fail("library-representation", "missing type member " + slot.name);
    // The shared template checker already validated exported permissions using
    // only public dependency bounds. Layout may now unfold private storage.
    auto plan = layout(Type::abstract(iface.self, slot.name), node.scope);
    if (!plan)
      return plan.takeError();
  }
  for (const auto &m : iface.statics) {
    auto actual = impl.statics.find(m.name);
    if (actual == impl.statics.end())
      return fail("library-static-member", "missing static member " + m.name);
    auto selected = term(actual->second, node.scope);
    if (!selected)
      return selected.takeError();
    auto sort = sortOf(*selected, environment);
    if (!sort)
      return sort.takeError();
    if (!sameSort(*sort, m.sort))
      return fail("library-static-sort", "associated member sort mismatch");
    if (m.equation) {
      auto expected = term(*m.equation, node.scope);
      if (!expected)
        return expected.takeError();
      if (auto err = prove({}, {{"", {*selected, *expected}}}, environment))
        return err;
    }
  }
  auto global = requirements(iface.requirements, node.scope);
  if (!global)
    return global.takeError();
  if (auto err = prove({}, *global, environment))
    return err;
  // Signatures, roles, effects and nominal types were checked parametrically
  // by checkComponent in select(). Do not re-establish that judgment by
  // comparing expanded layouts here: imported abstraction must remain opaque.
  for (const auto &member : impl.functions)
    if (auto err = bounds(member.second.body().typeBounds, node.scope))
      return err;
  for (const auto &facet : iface.facets) {
    Evidence ev{facet,
                Evidence::State::Unavailable,
                node.artifact,
                {},
                "no supported owner checker"};
    if (facet.owner == "zkc.frontend.library" &&
        (facet.name == "resources" || facet.name == "effects")) {
      ev.state = Evidence::State::Established;
      ev.ownerVersion = "1";
      ev.explanation = "finite typed body and conformance checks; no "
                       "cryptographic or behavioral equivalence claim";
    }
    if (facet.required && ev.state != Evidence::State::Established)
      return fail("library-required-facet", "unsupported required facet " +
                                                facet.owner + "/" + facet.name);
    evidence.push_back(std::move(ev));
  }
  return llvm::Error::success();
}
} // namespace zkc::frontend::library::detail
