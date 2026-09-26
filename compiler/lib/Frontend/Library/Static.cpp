#include "Diagnostic.h"
#include "Internal.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Support/Json.h"
#include <algorithm>

namespace zkc::frontend::library {
char Diagnostic::ID = 0;
namespace detail {
llvm::Error fail(llvm::StringRef code, llvm::Twine text) {
  return llvm::make_error<Diagnostic>(code.str(), text.str());
}
bool sameSort(const Sort &a, const Sort &b) {
  return a.kind == b.kind && a.domain == b.domain;
}
llvm::Error validateSort(const Sort &s) {
  switch (s.kind) {
  case Sort::Kind::Domain:
    if (!s.domain.empty())
      return llvm::Error::success();
    break;
  case Sort::Kind::Type:
  case Sort::Kind::Natural:
  case Sort::Kind::Association:
  case Sort::Kind::Component:
    if (s.domain.empty())
      return llvm::Error::success();
    break;
  }
  return fail("library-sort", "invalid sort or domain qualifier");
}
const StaticDeclaration *findStatic(const QualifiedDecl &id,
                                    const Environment &e) {
  for (const auto &d : e.statics)
    if (identity(d.id) == identity(id))
      return &d;
  return nullptr;
}
llvm::Expected<std::string>
installedDomain(const StaticTerm &t, const Environment &e, unsigned depth) {
  if (depth > 128)
    return fail("library-limit", "installed domain projection depth");
  std::string domain;
  if (t.kind == StaticTerm::Kind::Root ||
      (t.kind == StaticTerm::Kind::Apply && t.arguments.empty())) {
    const auto *d = findStatic(t.declaration, e);
    if (!d || d->parameter || d->result.kind != Sort::Kind::Domain)
      return std::string{};
    auto ownerSort =
        protocol::installedDomains().identitySort(d->capturedSubject);
    if (ownerSort.empty())
      return std::string{};
    if (ownerSort != d->result.domain)
      return fail("library-domain-sort",
                  "captured installed domain has another sort");
    if (!d->capturedDependencies.empty() || !d->parameters.empty() || d->seal)
      return fail("library-domain-capture",
                  "installed domain root has hidden captures or parameters");
    domain = d->capturedSubject;
  } else if (t.kind == StaticTerm::Kind::Project && t.arguments.size() == 1) {
    auto parent = installedDomain(t.arguments[0], e, depth + 1);
    if (!parent)
      return parent.takeError();
    if (parent->empty())
      return std::string{};
    domain = protocol::installedDomains()
                 .associatedIdentity(*parent, t.member)
                 .str();
  }
  if (!domain.empty()) {
    auto sort = sortOf(t, e);
    if (!sort)
      return sort.takeError();
    if (sort->kind != Sort::Kind::Domain ||
        protocol::installedDomains().identitySort(domain) != sort->domain)
      return fail("library-domain-sort",
                  "installed domain interpretation sort mismatch");
  }
  return domain;
}
llvm::Error captured(const QualifiedDecl &id, const Environment &e) {
  if (id.library.nameSpace.empty() || id.library.name.empty() ||
      id.library.version.empty() || id.name.empty())
    return fail("library-identity", "incomplete qualified declaration");
  for (const auto &m : id.module)
    if (m.empty())
      return fail("library-identity", "empty module segment");
  for (const auto &l : e.libraries) {
    QualifiedDecl owner{l.id, id.module, id.name};
    if (identity(owner) != identity(id))
      continue;
    for (const auto &d : l.declarations)
      if (identity(d) == identity(id))
        return llvm::Error::success();
  }
  return fail("library-capture",
              "declaration is absent from captured library: " + id.name);
}
llvm::Error validateEnvironment(const Environment &e) {
  if (!e.expansionLimit || e.expansionLimit > 1000000)
    return fail("library-limit", "expansion limit must be in 1..1000000");
  std::set<std::string> libraries, declarations, statics, types, operations;
  for (const auto &l : e.libraries) {
    if (!libraries.insert(identity(QualifiedDecl{l.id, {}, ""})).second)
      return fail("library-capture", "duplicate captured library identity");
    for (const auto &d : l.declarations) {
      if (identity(QualifiedDecl{l.id, d.module, d.name}) != identity(d) ||
          !declarations.insert(identity(d)).second)
        return fail("library-capture",
                    "inconsistent or duplicate captured declaration");
      if (auto err = captured(d, e))
        return err;
    }
  }
  for (const auto &d : e.statics) {
    if (auto err = captured(d.id, e))
      return err;
    if (!statics.insert(identity(d.id)).second)
      return fail("library-static", "duplicate static declaration");
    if (auto err = validateSort(d.result))
      return err;
    for (const auto &s : d.parameters)
      if (auto err = validateSort(s))
        return err;
    for (const auto &m : d.members) {
      if (m.first.empty())
        return fail("library-static", "empty member");
      if (auto err = validateSort(m.second))
        return err;
    }
    if (!d.parameter && d.result.kind == Sort::Kind::Domain) {
      auto installed = installedDomain(StaticTerm::root(d.id), e);
      if (!installed)
        return installed.takeError();
    }
    if (d.parameter &&
        (!d.parameters.empty() || d.seal || !d.capturedSubject.empty() ||
         !d.capturedDependencies.empty()))
      return fail("library-static", "parameter carries definition payload");
    if (d.seal &&
        (!sameSort(d.result, Sort::component()) || d.parameters.size() != 1 ||
         !sameSort(d.parameters[0], Sort::component())))
      return fail("library-static", "seal must take and return component");
  }
  for (const auto &t : e.logicalTypes) {
    if (t.contract.name.empty() || !types.insert(t.contract.name).second)
      return fail("library-logical-type",
                  "duplicate or empty installed constructor");
    bool installed = false;
    for (const auto &owner : protocol::boundTypeConstructors())
      installed |= owner.name == t.contract.name &&
                   owner.parameters == t.contract.parameters &&
                   owner.affine == t.contract.affine;
    if (!installed || !t.droppable)
      return fail(
          "library-logical-type",
          "constructor permissions/signature differ from installed owner");
    for (const auto &s : t.contract.parameters)
      if (s.empty())
        return fail("library-sort", "empty logical constructor domain sort");
  }
  for (const auto &o : e.operations) {
    if (o.contract.name.empty() || !operations.insert(o.contract.name).second)
      return fail("library-operation",
                  "duplicate or empty installed operation");
    // Installed operations can perform provider work or stop even when they
    // return no values. Capturing a caller-supplied empty effect set must not
    // manufacture a purity judgment. Additional labels may only restrict use.
    if (!o.effects.count("local") || o.effects.count(""))
      return fail("library-operation-effect",
                  "installed operations require the local effect allowance");
    bool installed = false;
    Environment declared;
    declared.operations.push_back(o);
    for (const auto &owner : protocol::boundOperationContracts())
      if (owner.name == o.contract.name) {
        Environment canonical;
        canonical.operations.push_back({owner, o.effects});
        installed = encode(declared) == encode(canonical);
      }
    if (!installed)
      return fail("library-operation",
                  "logical signature differs from installed owner");
  }
  for (const auto &rule : e.implications) {
    bool installed = false;
    for (const auto &owner : protocol::boundCapabilityRules())
      installed |=
          owner.premise == rule.premise && owner.conclusion == rule.conclusion;
    if (!installed)
      return fail("library-implication", "implication has no supported owner");
  }
  for (const auto &d : e.statics)
    for (const auto &t : d.capturedDependencies) {
      auto sort = sortOf(t, e);
      if (!sort)
        return sort.takeError();
      auto key = selectionIdentity(t, e);
      if (!key)
        return key.takeError();
    }
  return llvm::Error::success();
}
} // namespace detail
namespace {
bool emptyDecl(const QualifiedDecl &d) {
  return d.name.empty() && d.module.empty() && d.library.name.empty() &&
         d.library.nameSpace.empty() && d.library.version.empty() &&
         d.library.resolution.empty();
}
llvm::Expected<Sort> termSort(const StaticTerm &t, const Environment &e,
                              unsigned depth) {
  using namespace detail;
  if (depth > 128)
    return fail("library-limit", "static term depth exceeds 128");
  if (t.kind != StaticTerm::Kind::Natural && t.number)
    return fail("library-static", "inactive natural payload");
  if (t.kind != StaticTerm::Kind::Project && !t.member.empty())
    return fail("library-static", "inactive projection member");
  switch (t.kind) {
  case StaticTerm::Kind::Natural:
    if (!emptyDecl(t.declaration) || !t.arguments.empty() ||
        t.number > e.expansionLimit)
      return fail("library-limit", "malformed or excessive static natural");
    return Sort::natural();
  case StaticTerm::Kind::Project: {
    if (!emptyDecl(t.declaration) || t.arguments.size() != 1 ||
        t.member.empty())
      return fail("library-static", "malformed projection");
    auto p = termSort(t.arguments[0], e, depth + 1);
    if (!p)
      return p.takeError();
    if (p->kind == Sort::Kind::Domain) {
      auto associated = protocol::associatedMemberSort(p->domain, t.member);
      if (associated.empty())
        return fail("library-member", "unknown associated domain member " +
                                          p->domain + "::" + t.member);
      return Sort::domainOf(associated.str());
    }
    const auto &base = t.arguments[0];
    // Associated-member signatures belong to the explicitly captured head.
    // Projecting further from an unregistered result cannot invent a signature.
    const auto *d = findStatic(base.declaration, e);
    if (!d)
      return fail("library-member",
                  "projection parent has no member signature");
    auto m = d->members.find(t.member);
    if (m == d->members.end())
      return fail("library-member", "unknown static member " + t.member);
    return m->second;
  }
  case StaticTerm::Kind::Root:
  case StaticTerm::Kind::Apply:
  case StaticTerm::Kind::Seal: {
    const auto *d = findStatic(t.declaration, e);
    if (!d)
      return fail("library-static",
                  "unknown static declaration " + t.declaration.name);
    if (auto err = captured(d->id, e))
      return err;
    if (auto err = validateSort(d->result))
      return err;
    if (t.kind == StaticTerm::Kind::Root &&
        (!t.arguments.empty() || !d->parameters.empty() || d->seal))
      return fail("library-static", "constructor used as root");
    if (t.kind == StaticTerm::Kind::Apply && (d->parameter || d->seal))
      return fail("library-static",
                  "parameter/seal used as ordinary constructor");
    if ((t.kind == StaticTerm::Kind::Seal) != d->seal)
      return fail("library-static", "incorrect seal constructor");
    if (t.arguments.size() != d->parameters.size())
      return fail("library-static-arity", "static argument count");
    for (size_t i = 0; i < t.arguments.size(); ++i) {
      auto a = termSort(t.arguments[i], e, depth + 1);
      if (!a)
        return a.takeError();
      if (!sameSort(*a, d->parameters[i]))
        return fail("library-static-sort", "static argument sort mismatch");
    }
    return d->result;
  }
  }
  return fail("library-static", "unknown static term kind");
}
llvm::Expected<std::string> key(const StaticTerm &t, const Environment &e,
                                std::set<std::string> &active, unsigned depth) {
  using namespace detail;
  if (depth > 128)
    return fail("library-limit", "selection dependency depth exceeds 128");
  // Installed domain roots/projections have the owner's exact identity,
  // independent of a captured source alias. Other roots stay nominal.
  auto domain = installedDomain(t, e);
  if (!domain)
    return domain.takeError();
  if (!domain->empty()) {
    Writer canonical;
    canonical.add("zkc.installed-domain/1");
    canonical.add(*domain);
    return canonical.bytes;
  }
  Writer w;
  // Zero-argument application and nominal root denote the same pure selection.
  w.add(t.kind == StaticTerm::Kind::Apply && t.arguments.empty()
            ? unsigned(StaticTerm::Kind::Root)
            : unsigned(t.kind));
  w.add(t.member);
  w.add(t.number);
  w.add(identity(t.declaration));
  w.add(t.arguments.size());
  for (const auto &a : t.arguments) {
    auto k = key(a, e, active, depth + 1);
    if (!k)
      return k.takeError();
    w.add(*k);
  }
  if (const auto *d = findStatic(t.declaration, e)) {
    std::string id = identity(d->id);
    if (!active.insert(id).second)
      return fail("library-selection-cycle",
                  "captured dependency cycle at " + d->id.name);
    w.add(d->capturedSubject);
    w.add(d->capturedDependencies.size());
    for (const auto &a : d->capturedDependencies) {
      auto k = key(a, e, active, depth + 1);
      if (!k)
        return k.takeError();
      w.add(*k);
    }
    active.erase(id);
  }
  return w.bytes;
}
} // namespace
llvm::Expected<Sort> sortOf(const StaticTerm &t, const Environment &e) {
  return termSort(t, e, 0);
}
llvm::Expected<std::string> resolvedDomain(const StaticTerm &t,
                                           const Environment &e) {
  auto sort = sortOf(t, e);
  if (!sort)
    return sort.takeError();
  auto domain = detail::installedDomain(t, e);
  if (!domain)
    return domain.takeError();
  if (domain->empty())
    return detail::fail("library-logical-domain",
                        "term has no captured installed domain interpretation");
  return *domain;
}
llvm::Expected<std::string> selectionIdentity(const StaticTerm &t,
                                              const Environment &e) {
  auto s = sortOf(t, e);
  if (!s)
    return s.takeError();
  std::set<std::string> active;
  return key(t, e, active, 0);
}

namespace detail {
llvm::Expected<std::string> normalizedTypeIdentity(const Type &t,
                                                   const Environment &e) {
  Writer w;
  w.add(unsigned(t.kind));
  w.add(t.name);
  w.add(identity(t.declaration));
  w.list(t.fields, [&](const auto &f) { w.add(f); });
  w.add(t.arguments.size());
  for (const auto &a : t.arguments) {
    auto key = selectionIdentity(a, e);
    if (!key)
      return key.takeError();
    w.add(*key);
  }
  w.add(t.elements.size());
  for (const auto &child : t.elements) {
    auto key = normalizedTypeIdentity(child, e);
    if (!key)
      return key.takeError();
    w.add(*key);
  }
  return w.bytes;
}
// Preserve every semantic identity field. The portable DAG shares exact trees
// and subjects rather than replacing opaque members with their physical leaves.
llvm::Expected<std::string> normalizedTypeTree(const Type &type,
                                               const Environment &env) {
  using llvm::json::Array;
  using llvm::json::Value;
  size_t work = 0;
  std::set<std::string> active;
  std::function<llvm::Expected<Value>(const StaticTerm &, unsigned)> term;
  term = [&](const StaticTerm &t, unsigned depth) -> llvm::Expected<Value> {
    if (++work > env.expansionLimit || depth > 128)
      return fail("library-limit", "nominal identity expansion exceeds limit");
    auto domain = installedDomain(t, env);
    if (!domain)
      return domain.takeError();
    if (!domain->empty())
      return Value(Array{"installed-domain", *domain});
    Array arguments;
    for (const auto &a : t.arguments) {
      auto child = term(a, depth + 1);
      if (!child)
        return child.takeError();
      arguments.push_back(std::move(*child));
    }
    Array capture;
    if (const auto *d = findStatic(t.declaration, env)) {
      auto id = identity(d->id);
      if (!active.insert(id).second)
        return fail("library-selection-cycle", "cyclic captured identity");
      Array dependencies;
      for (const auto &dependency : d->capturedDependencies) {
        auto child = term(dependency, depth + 1);
        if (!child)
          return child.takeError();
        dependencies.push_back(std::move(*child));
      }
      active.erase(id);
      capture.push_back(d->capturedSubject);
      capture.push_back(std::move(dependencies));
    }
    auto kind = t.kind == StaticTerm::Kind::Apply && t.arguments.empty()
                    ? StaticTerm::Kind::Root
                    : t.kind;
    return Value(Array{std::to_string(unsigned(kind)), t.member,
                       std::to_string(t.number), identity(t.declaration),
                       std::move(arguments), std::move(capture)});
  };
  std::function<llvm::Expected<Value>(const Type &, unsigned)> visit;
  visit = [&](const Type &t, unsigned depth) -> llvm::Expected<Value> {
    if (++work > env.expansionLimit || depth > 128)
      return fail("library-limit", "nominal type expansion exceeds limit");
    Array fields, arguments, elements;
    for (const auto &f : t.fields)
      fields.push_back(f);
    for (const auto &a : t.arguments) {
      auto child = term(a, depth + 1);
      if (!child)
        return child.takeError();
      arguments.push_back(std::move(*child));
    }
    for (const auto &a : t.elements) {
      auto child = visit(a, depth + 1);
      if (!child)
        return child.takeError();
      elements.push_back(std::move(*child));
    }
    return Value(Array{std::to_string(unsigned(t.kind)), t.name,
                       identity(t.declaration), std::move(fields),
                       std::move(arguments), std::move(elements)});
  };
  auto result = visit(type, 0);
  if (!result)
    return result.takeError();
  return printJson(*result);
}
llvm::Error validateRequirements(const std::vector<Requirement> &rs,
                                 const Environment &e) {
  for (const auto &r : rs) {
    if (r.arguments.empty() || (r.relation.empty() && r.arguments.size() != 2))
      return fail("library-requirement", "malformed predicate");
    std::optional<Sort> first;
    for (const auto &a : r.arguments) {
      auto s = sortOf(a, e);
      if (!s)
        return s.takeError();
      if (r.relation.empty() && first && !sameSort(*first, *s))
        return fail("library-static-sort", "equality relates different sorts");
      first = *s;
    }
  }
  return llvm::Error::success();
}
llvm::Error prove(const std::vector<Requirement> &assumptions,
                  const std::vector<Requirement> &goals, const Environment &e) {
  if (auto err = validateRequirements(assumptions, e))
    return err;
  if (auto err = validateRequirements(goals, e))
    return err;
  std::vector<requirements::Term> terms;
  std::map<std::string, unsigned> ids;
  std::function<llvm::Expected<unsigned>(const StaticTerm &)> intern =
      [&](const StaticTerm &t) -> llvm::Expected<unsigned> {
    auto k = selectionIdentity(t, e);
    if (!k)
      return k.takeError();
    auto old = ids.find(*k);
    if (old != ids.end())
      return old->second;
    requirements::Term out;
    if (t.kind == StaticTerm::Kind::Project) {
      auto p = intern(t.arguments[0]);
      if (!p)
        return p.takeError();
      out.name = t.member;
      out.parent = *p;
    } else if (t.kind == StaticTerm::Kind::Apply ||
               t.kind == StaticTerm::Kind::Seal) {
      // Include exact hidden dependency capture in the constructor head, while
      // retaining visible arguments for application congruence.
      StaticTerm head = t;
      head.arguments.clear();
      std::set<std::string> active;
      auto h = key(head, e, active, 0);
      if (!h)
        return h.takeError();
      out.name = *h;
      out.arguments = std::vector<unsigned>{};
      for (const auto &a : t.arguments) {
        auto id = intern(a);
        if (!id)
          return id.takeError();
        out.arguments->push_back(*id);
      }
    } else
      out.name = *k;
    unsigned id = terms.size();
    terms.push_back(std::move(out));
    ids.emplace(*k, id);
    return id;
  };
  auto predicates = [&](const std::vector<Requirement> &rs)
      -> llvm::Expected<std::vector<requirements::Predicate>> {
    std::vector<requirements::Predicate> out;
    for (const auto &r : rs) {
      std::vector<unsigned> as;
      for (const auto &a : r.arguments) {
        auto id = intern(a);
        if (!id)
          return id.takeError();
        as.push_back(*id);
      }
      out.push_back(r.relation.empty()
                        ? requirements::Predicate::equal(as[0], as[1])
                        : requirements::Predicate::holds(r.relation, as));
    }
    return out;
  };
  // Installed nominal facts are supplied by their existing owner, never by
  // user-written evidence labels or the mere name of a generic parameter.
  std::vector<Requirement> known = assumptions;
  for (const auto &goal : goals) {
    std::vector<std::string> ids;
    for (const auto &a : goal.arguments) {
      auto domain = installedDomain(a, e);
      if (!domain)
        return domain.takeError();
      ids.push_back(*domain);
    }
    if (std::none_of(ids.begin(), ids.end(),
                     [](const auto &id) { return id.empty(); }) &&
        (goal.relation.empty()
             ? ids.size() == 2 && ids[0] == ids[1]
             : protocol::installedDomains().hasFact(goal.relation, ids)))
      known.push_back(goal);
  }
  auto as = predicates(known);
  if (!as)
    return as.takeError();
  auto gs = predicates(goals);
  if (!gs)
    return gs.takeError();
  auto proof = requirements::derive(terms, *as, e.implications, *gs);
  if (!proof)
    return proof.takeError();
  for (size_t i = 0; i < proof->goals.size(); ++i)
    if (!proof->goals[i])
      return llvm::make_error<Diagnostic>(
          "library-bound",
          "required predicate not derivable: " + (goals[i].relation.empty()
                                                      ? std::string("equality")
                                                      : goals[i].relation),
          goals[i], "zkc::requirements::derive");
  return llvm::Error::success();
}
StaticTerm replace(const StaticTerm &t, const StaticTerm &from,
                   const StaticTerm &to) {
  if (identity(t) == identity(from))
    return to;
  StaticTerm out = t;
  for (auto &a : out.arguments)
    a = replace(a, from, to);
  return out;
}
Type replace(const Type &t, const StaticTerm &from, const StaticTerm &to) {
  Type out = t;
  for (auto &a : out.arguments)
    a = replace(a, from, to);
  for (auto &a : out.elements)
    a = replace(a, from, to);
  return out;
}
Requirement replace(const Requirement &r, const StaticTerm &from,
                    const StaticTerm &to) {
  Requirement out = r;
  for (auto &a : out.arguments)
    a = replace(a, from, to);
  return out;
}
Signature replace(const Signature &s, const StaticTerm &from,
                  const StaticTerm &to) {
  Signature out = s;
  for (auto &p : out.inputs)
    p.type = replace(p.type, from, to);
  for (auto &p : out.outputs)
    p.type = replace(p.type, from, to);
  for (auto &r : out.preconditions)
    r = replace(r, from, to);
  for (auto &r : out.postconditions)
    r = replace(r, from, to);
  return out;
}
} // namespace detail
} // namespace zkc::frontend::library
