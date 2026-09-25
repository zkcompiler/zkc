#include "Internal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

namespace zkc::frontend::library {
namespace {
using detail::Writer;
void put(Writer &w, const LibraryId &x) {
  w.add(x.nameSpace);
  w.add(x.name);
  w.add(x.version);
  w.add(x.resolution);
}
void put(Writer &w, const QualifiedDecl &x) {
  put(w, x.library);
  w.list(x.module, [&](const auto &s) { w.add(s); });
  w.add(x.name);
}
void put(Writer &w, const Sort &x) {
  w.add(unsigned(x.kind));
  w.add(x.domain);
}
void put(Writer &w, const StaticTerm &x) {
  w.add(unsigned(x.kind));
  put(w, x.declaration);
  w.add(x.member);
  w.add(x.number);
  w.list(x.arguments, [&](const auto &a) { put(w, a); });
}
void put(Writer &w, const Type &x) {
  w.add(unsigned(x.kind));
  w.add(x.name);
  put(w, x.declaration);
  w.list(x.arguments, [&](const auto &a) { put(w, a); });
  w.list(x.elements, [&](const auto &a) { put(w, a); });
  w.list(x.fields, [&](const auto &a) { w.add(a); });
}
void put(Writer &w, Permissions p) {
  w.add(p.copy);
  w.add(p.drop);
}
void put(Writer &w, const Requirement &x) {
  w.add(x.relation);
  w.list(x.arguments, [&](const auto &a) { put(w, a); });
}
void put(Writer &w, const Port &x) {
  put(w, x.type);
  w.add(x.role);
}
void put(Writer &w, const Signature &x) {
  w.list(x.inputs, [&](const auto &a) { put(w, a); });
  w.list(x.outputs, [&](const auto &a) { put(w, a); });
  w.list(x.preconditions, [&](const auto &a) { put(w, a); });
  w.list(x.postconditions, [&](const auto &a) { put(w, a); });
  w.list(x.effects, [&](const auto &a) { w.add(a); });
  w.list(x.inputLabels, [&](const auto &a) { w.add(a); });
}
void put(Writer &w, const TypeBound &x) {
  put(w, x.parameter);
  put(w, x.permissions);
}
void put(Writer &w, const Value &x) {
  w.add(x.id.index);
  put(w, x.port);
}
void put(Writer &w, const Place &x) {
  w.add(x.value.index);
  w.list(x.path, [&](auto a) { w.add(a); });
}
void put(Writer &w, const generic::Signature &x) {
  w.list(x.scope.terms, [&](const auto &t) {
    w.add(t.name);
    w.add(t.parent.has_value());
    if (t.parent)
      w.add(*t.parent);
    w.add(t.arguments.has_value());
    if (t.arguments)
      w.list(*t.arguments, [&](auto a) { w.add(a); });
  });
  w.list(x.scope.sorts, [&](const auto &s) { w.add(s); });
  w.list(x.scope.constants, [&](const auto &c) {
    w.add(c.first);
    w.add(c.second);
  });
  auto type = [&](const auto &t) {
    w.add(t.constructor);
    w.list(t.arguments, [&](auto a) { w.add(a); });
  };
  w.list(x.inputs, type);
  w.list(x.outputs, type);
  w.list(x.requirements, [&](const auto &p) {
    w.add(unsigned(p.kind));
    w.add(p.relation);
    w.list(p.arguments, [&](auto a) { w.add(a); });
  });
}
} // namespace

std::string identity(const QualifiedDecl &x) {
  Writer w;
  put(w, x);
  return w.bytes;
}
std::string identity(const StaticTerm &x) {
  Writer w;
  put(w, x);
  return w.bytes;
}
std::string identity(const Type &x) {
  Writer w;
  put(w, x);
  return w.bytes;
}
bool sameType(const Type &a, const Type &b) {
  return identity(a) == identity(b);
}
const LocalBranches *branches(const Instruction &i) {
  if (const auto *c = std::get_if<Conditional>(&i))
    return &c->branches;
  return std::get_if<Match>(&i);
}
LocalBranches *branches(Instruction &i) {
  if (auto *c = std::get_if<Conditional>(&i))
    return &c->branches;
  return std::get_if<Match>(&i);
}
bool stopped(const std::vector<Instruction> &instructions) {
  return !instructions.empty() &&
         std::holds_alternative<Stop>(instructions.back());
}
namespace {
bool cannotContinue(const std::vector<Instruction> &instructions,
                    unsigned depth) {
  if (instructions.empty() || depth > 128)
    return false;
  if (stopped(instructions))
    return true;
  const auto *m = branches(instructions.back());
  if (!m || m->arms.empty())
    return false;
  for (const auto &arm : m->arms)
    if (!arm.body || !cannotContinue(arm.body->instructions, depth + 1))
      return false;
  return true;
}
} // namespace
bool terminal(const std::vector<Instruction> &instructions) {
  return cannotContinue(instructions, 0);
}

namespace detail {
std::string hash(llvm::StringRef text) {
  return llvm::toHex(llvm::SHA256::hash(llvm::arrayRefFromStringRef(text)),
                     true);
}
std::string encode(const Environment &x) {
  Writer w;
  w.add("zkc.checked-library.environment/1");
  w.list(x.libraries, [&](const auto &l) {
    put(w, l.id);
    w.list(l.declarations, [&](const auto &d) { put(w, d); });
  });
  w.list(x.statics, [&](const auto &d) {
    put(w, d.id);
    put(w, d.result);
    w.list(d.parameters, [&](const auto &s) { put(w, s); });
    w.list(d.members, [&](const auto &m) {
      w.add(m.first);
      put(w, m.second);
    });
    w.add(d.capturedSubject);
    w.list(d.capturedDependencies, [&](const auto &t) { put(w, t); });
    w.add(d.parameter);
    w.add(d.seal);
  });
  w.list(x.logicalTypes, [&](const auto &t) {
    w.add(t.contract.name);
    w.add(t.contract.affine);
    w.add(t.droppable);
    w.list(t.contract.parameters, [&](const auto &s) { w.add(s); });
  });
  w.list(x.operations, [&](const auto &o) {
    w.add(o.contract.name);
    put(w, o.contract.signature);
    w.list(o.effects, [&](const auto &s) { w.add(s); });
  });
  w.list(x.implications, [&](const auto &i) {
    w.add(i.premise);
    w.add(i.conclusion);
  });
  w.add(x.expansionLimit);
  return w.bytes;
}
std::string encode(const InterfaceDecl &x) {
  Writer w;
  w.add("zkc.checked-library.interface/1");
  put(w, x.id);
  put(w, x.self);
  w.list(x.types, [&](const auto &t) {
    w.add(t.name);
    put(w, t.permissions);
  });
  w.list(x.statics, [&](const auto &s) {
    w.add(s.name);
    put(w, s.sort);
    w.add(s.equation.has_value());
    if (s.equation)
      put(w, *s.equation);
  });
  w.list(x.functions, [&](const auto &f) {
    w.add(f.first);
    put(w, f.second);
  });
  w.list(x.typeBounds, [&](const auto &b) { put(w, b); });
  w.list(x.requirements, [&](const auto &r) { put(w, r); });
  w.list(x.facets, [&](const auto &f) {
    w.add(f.owner);
    w.add(f.name);
    w.add(f.required);
  });
  return w.bytes;
}
std::string encode(const Body &x) {
  Writer w;
  w.add("zkc.checked-library.body/3");
  put(w, x.id);
  put(w, x.signature);
  w.list(x.typeBounds, [&](const auto &b) { put(w, b); });
  w.list(x.inputs, [&](const auto &v) { put(w, v); });
  std::function<void(const Region &)> region;
  region = [&](const Region &r) {
    w.list(r.inputs, [&](const auto &v) { put(w, v); });
    w.list(r.instructions, [&](const auto &i) {
      w.add(i.index());
      if (const auto *c = std::get_if<Call>(&i)) {
        w.add(c->target.index());
        if (const auto *m = std::get_if<MemberCall>(&c->target)) {
          put(w, m->component);
          w.add(m->member);
        } else if (const auto *source = std::get_if<SourceCall>(&c->target)) {
          w.add(source->callable.identity());
          w.list(source->arguments.statics, [&](const auto &a) {
            put(w, a.first);
            put(w, a.second);
          });
          w.list(source->arguments.types, [&](const auto &a) {
            put(w, a.first);
            put(w, a.second);
          });
        } else {
          const auto &l = std::get<LogicalCall>(c->target);
          w.add(l.operation);
          w.list(l.arguments, [&](const auto &a) { put(w, a); });
        }
        w.add(c->role);
        w.list(c->inputs, [&](const auto &a) { put(w, a); });
        w.list(c->outputs, [&](const auto &a) { put(w, a); });
        w.list(c->attributes, [&](const auto &a) { w.add(a); });
      } else if (const auto *c = std::get_if<Construct>(&i)) {
        put(w, c->output);
        w.list(c->elements, [&](const auto &a) { put(w, a); });
      } else if (const auto *p = std::get_if<Project>(&i)) {
        put(w, p->input);
        put(w, p->output);
      } else if (const auto *d = std::get_if<Drop>(&i)) {
        put(w, d->input);
      } else if (const auto *c = std::get_if<VariantConstruct>(&i)) {
        put(w, c->output);
        w.add(c->alternative);
        put(w, c->payload);
      } else if (const auto *s = std::get_if<Stop>(&i)) {
        w.add(s->reason);
      } else if (const auto *m = branches(i)) {
        put(w, m->input);
        w.add(m->role);
        w.list(m->captures, [&](const auto &p) { put(w, p); });
        w.list(m->outputs, [&](const auto &v) { put(w, v); });
        w.list(m->arms, [&](const auto &a) {
          w.add(a.alternative);
          region(*a.body);
        });
      } else {
        const auto &a = std::get<ArrayTraversal>(i);
        put(w, a.input);
        w.add(a.role);
        w.list(a.initial, [&](const auto &p) { put(w, p); });
        w.list(a.captures, [&](const auto &p) { put(w, p); });
        w.list(a.outputs, [&](const auto &v) { put(w, v); });
        w.add(bool(a.collected));
        if (a.collected)
          put(w, *a.collected);
        region(*a.body);
      }
    });
    w.list(r.returns, [&](const auto &p) { put(w, p); });
  };
  region(Region{{}, x.instructions, x.returns});
  return w.bytes;
}
} // namespace detail

Sort Sort::type() { return {Kind::Type, {}}; }
Sort Sort::domainOf(std::string s) { return {Kind::Domain, std::move(s)}; }
Sort Sort::natural() { return {Kind::Natural, {}}; }
Sort Sort::association() { return {Kind::Association, {}}; }
Sort Sort::component() { return {Kind::Component, {}}; }
StaticTerm StaticTerm::root(QualifiedDecl d) {
  StaticTerm t;
  t.declaration = std::move(d);
  return t;
}
StaticTerm StaticTerm::project(StaticTerm p, std::string m) {
  StaticTerm t;
  t.kind = Kind::Project;
  t.arguments.push_back(std::move(p));
  t.member = std::move(m);
  return t;
}
StaticTerm StaticTerm::apply(QualifiedDecl d, std::vector<StaticTerm> a) {
  StaticTerm t;
  t.kind = Kind::Apply;
  t.declaration = std::move(d);
  t.arguments = std::move(a);
  return t;
}
StaticTerm StaticTerm::natural(uint64_t n) {
  StaticTerm t;
  t.kind = Kind::Natural;
  t.number = n;
  return t;
}
StaticTerm StaticTerm::seal(QualifiedDecl d, StaticTerm p) {
  StaticTerm t;
  t.kind = Kind::Seal;
  t.declaration = std::move(d);
  t.arguments.push_back(std::move(p));
  return t;
}
Type Type::logical(std::string n, std::vector<StaticTerm> a) {
  Type t;
  t.kind = Kind::Logical;
  t.name = std::move(n);
  t.arguments = std::move(a);
  return t;
}
Type Type::parameter(QualifiedDecl d) {
  Type t;
  t.kind = Kind::Parameter;
  t.declaration = std::move(d);
  return t;
}
Type Type::abstract(StaticTerm c, std::string m) {
  Type t;
  t.kind = Kind::Abstract;
  t.name = std::move(m);
  t.arguments.push_back(std::move(c));
  return t;
}
Type Type::product(std::vector<Type> e) {
  Type t;
  t.elements = std::move(e);
  return t;
}
Type Type::record(QualifiedDecl d, std::vector<std::string> f,
                  std::vector<Type> e) {
  Type t;
  t.kind = Kind::Record;
  t.declaration = std::move(d);
  t.fields = std::move(f);
  t.elements = std::move(e);
  return t;
}
Type Type::array(Type e, StaticTerm n) {
  Type t;
  t.kind = Kind::Array;
  t.elements.push_back(std::move(e));
  t.arguments.push_back(std::move(n));
  return t;
}
Type Type::variant(QualifiedDecl d, std::vector<std::string> alternatives,
                   std::vector<Type> payloads) {
  Type t;
  t.kind = Kind::Variant;
  t.declaration = std::move(d);
  t.fields = std::move(alternatives);
  t.elements = std::move(payloads);
  return t;
}
} // namespace zkc::frontend::library
