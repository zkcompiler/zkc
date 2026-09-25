#include "Internal.h"
#include "llvm/ADT/STLExtras.h"

namespace zkc::frontend::library {
struct Interface::Data {
  InterfaceDecl declaration;
  Environment environment;
  std::string identity, fingerprint;
};
Interface::Interface(std::shared_ptr<const Data> d) : data(std::move(d)) {}
const InterfaceDecl &Interface::declaration() const {
  return data->declaration;
}
const Environment &Interface::environment() const { return data->environment; }
const std::string &Interface::identity() const { return data->identity; }
const std::string &Interface::fingerprint() const { return data->fingerprint; }
namespace detail {
llvm::Error importsInterface(const Interface &interface, const Environment &e) {
  const auto &d = interface.declaration();
  auto needed = interface.environment();
  std::set<std::string> reached;
  size_t work = 0;
  std::function<llvm::Error(const QualifiedDecl &)> declaration;
  std::function<llvm::Error(const StaticTerm &)> term;
  term = [&](const StaticTerm &t) -> llvm::Error {
    if (++work > e.expansionLimit)
      return fail("library-limit", "interface public closure exceeds limit");
    if (t.kind == StaticTerm::Kind::Root || t.kind == StaticTerm::Kind::Apply ||
        t.kind == StaticTerm::Kind::Seal)
      if (auto error = declaration(t.declaration))
        return error;
    for (const auto &a : t.arguments)
      if (auto error = term(a))
        return error;
    return llvm::Error::success();
  };
  declaration = [&](const QualifiedDecl &q) -> llvm::Error {
    if (!reached.insert(identity(q)).second)
      return llvm::Error::success();
    if (const auto *s = findStatic(q, needed))
      for (const auto &dependency : s->capturedDependencies)
        if (auto error = term(dependency))
          return error;
    return llvm::Error::success();
  };
  std::function<llvm::Error(const Type &)> type =
      [&](const Type &t) -> llvm::Error {
    if (t.kind == Type::Kind::Record || t.kind == Type::Kind::Variant ||
        t.kind == Type::Kind::Parameter)
      if (auto error = declaration(t.declaration))
        return error;
    for (const auto &a : t.arguments)
      if (auto error = term(a))
        return error;
    for (const auto &a : t.elements)
      if (auto error = type(a))
        return error;
    return llvm::Error::success();
  };
  auto requirements = [&](const auto &rs) -> llvm::Error {
    for (const auto &r : rs)
      for (const auto &a : r.arguments)
        if (auto error = term(a))
          return error;
    return llvm::Error::success();
  };
  if (auto error = declaration(d.id))
    return error;
  if (auto error = term(d.self))
    return error;
  for (const auto &b : d.typeBounds)
    if (auto error = declaration(b.parameter))
      return error;
  for (const auto &s : d.statics)
    if (s.equation)
      if (auto error = term(*s.equation))
        return error;
  if (auto error = requirements(d.requirements))
    return error;
  for (const auto &[name, signature] : d.functions) {
    for (const auto *ports : {&signature.inputs, &signature.outputs})
      for (const auto &p : *ports)
        if (auto error = type(p.type))
          return error;
    if (auto error = requirements(signature.preconditions))
      return error;
    if (auto error = requirements(signature.postconditions))
      return error;
  }
  for (auto &owner : needed.libraries)
    llvm::erase_if(owner.declarations,
                   [&](const auto &q) { return !reached.count(identity(q)); });
  llvm::erase_if(needed.libraries,
                 [](const auto &l) { return l.declarations.empty(); });
  llvm::erase_if(needed.statics,
                 [&](const auto &s) { return !reached.count(identity(s.id)); });
  return extends(needed, e);
}
} // namespace detail
llvm::Expected<Interface> formInterface(InterfaceDecl d, Environment e) {
  using namespace detail;
  if (auto err = validateEnvironment(e))
    return err;
  if (auto err = captured(d.id, e))
    return err;
  auto self = sortOf(d.self, e);
  if (!self)
    return self.takeError();
  if (!sameSort(*self, Sort::component()) ||
      d.self.kind != StaticTerm::Kind::Root)
    return fail("library-interface-self",
                "interface self must be a component parameter root");
  const auto *root = findStatic(d.self.declaration, e);
  if (!root || !root->parameter)
    return fail("library-interface-self", "self is not a parameter");
  std::set<std::string> names, bounds;
  for (const auto &b : d.typeBounds) {
    if (!bounds.insert(library::identity(b.parameter)).second)
      return fail("library-type-bound", "duplicate type bound");
    auto s = sortOf(StaticTerm::root(b.parameter), e);
    if (!s)
      return s.takeError();
    if (!sameSort(*s, Sort::type()))
      return fail("library-type-bound", "bound is not a type");
  }
  auto member = [&](const std::string &name, const Sort &sort) -> llvm::Error {
    if (name.empty() || !names.insert(name).second)
      return fail("library-interface-member",
                  "duplicate or empty interface member");
    auto s = sortOf(StaticTerm::project(d.self, name), e);
    if (!s)
      return s.takeError();
    if (!sameSort(*s, sort))
      return fail("library-interface-member", "captured member sort mismatch");
    return llvm::Error::success();
  };
  for (const auto &t : d.types)
    if (auto err = member(t.name, Sort::type()))
      return err;
  for (const auto &s : d.statics) {
    if (auto err = validateSort(s.sort))
      return err;
    if (s.sort.kind == Sort::Kind::Type || s.sort.kind == Sort::Kind::Component)
      return fail("library-interface-member",
                  "type uses TypeMember; nested components unsupported");
    if (auto err = member(s.name, s.sort))
      return err;
    if (s.equation) {
      auto actual = sortOf(*s.equation, e);
      if (!actual)
        return actual.takeError();
      if (!sameSort(*actual, s.sort))
        return fail("library-interface-equation",
                    "member equation sort mismatch");
    }
  }
  if (root->members.size() != d.types.size() + d.statics.size())
    return fail("library-interface-member",
                "captured self has undeclared members");
  const std::vector<Import> none;
  TypeContext ctx{e, none, d.typeBounds, &d};
  for (const auto &f : d.functions) {
    if (f.first.empty() || !names.insert(f.first).second)
      return fail("library-interface-member", "duplicate or empty function");
    if (auto err = signature(f.second, ctx))
      return err;
  }
  if (auto err = validateRequirements(d.requirements, e))
    return err;
  std::set<std::pair<std::string, std::string>> facets;
  for (const auto &f : d.facets) {
    if (f.owner.empty() || f.name.empty() ||
        !facets.emplace(f.owner, f.name).second)
      return fail("library-facet", "empty or duplicate facet");
  }
  // The exact environment is an assumption, not an implementation choice.
  // Conservative invalidation is intentional: no unrelated edits can silently
  // change installed operation or domain contracts used by this check.
  auto data = std::make_shared<Interface::Data>();
  data->identity = encode(d) + encode(e);
  data->fingerprint = hash(data->identity);
  data->declaration = std::move(d);
  data->environment = std::move(e);
  return Interface(std::move(data));
}
} // namespace zkc::frontend::library
