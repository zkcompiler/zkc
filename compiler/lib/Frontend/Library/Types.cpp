#include "Internal.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Kernels.h"
#include <algorithm>

namespace zkc::frontend::library {
llvm::Expected<std::vector<unsigned>>
bindArguments(const Signature &signature, size_t count,
              const std::vector<std::string> &names) {
  using detail::fail;
  if (count != signature.inputs.size())
    return fail(names.empty() ? "library-call-arity"
                              : "library-source-argument-name",
                "supply every declared input exactly once");
  std::vector<unsigned> result;
  if (names.empty()) {
    for (unsigned i = 0; i < count; ++i)
      result.push_back(i);
    return result;
  }
  if (signature.inputLabels.size() != count || names.size() != count)
    return fail("library-source-argument-name",
                "callee has no public labels or arguments mix named and "
                "positional forms");
  std::set<std::string> seen;
  for (const auto &name : names) {
    auto formal = std::find(signature.inputLabels.begin(),
                            signature.inputLabels.end(), name);
    if (name.empty() || formal == signature.inputLabels.end() ||
        !seen.insert(name).second)
      return fail("library-source-argument-name",
                  "unknown, duplicate, or mixed named argument");
    result.push_back(formal - signature.inputLabels.begin());
  }
  return result;
}
} // namespace zkc::frontend::library
namespace zkc::frontend::library::detail {
namespace {
bool emptyDecl(const QualifiedDecl &d) {
  return identity(d) == identity(QualifiedDecl{});
}
const InterfaceDecl *interfaceFor(const StaticTerm &t, const TypeContext &ctx) {
  if (ctx.forming && identity(t) == identity(ctx.forming->self))
    return ctx.forming;
  for (const auto &i : ctx.imports)
    if (identity(i.parameter) == identity(t))
      return &i.interface.declaration();
  return nullptr;
}
} // namespace
llvm::Expected<Permissions> permissions(const Type &t, const TypeContext &ctx,
                                        unsigned depth) {
  if (depth > 128)
    return fail("library-limit", "type depth exceeds 128");
  if (t.kind != Type::Kind::Record && t.kind != Type::Kind::Variant &&
      !t.fields.empty())
    return fail("library-type", "inactive record fields");
  if (t.kind != Type::Kind::Logical && t.kind != Type::Kind::Abstract &&
      !t.name.empty())
    return fail("library-type", "inactive type name");
  if (t.kind != Type::Kind::Record && t.kind != Type::Kind::Variant &&
      t.kind != Type::Kind::Parameter && !emptyDecl(t.declaration))
    return fail("library-type", "inactive nominal declaration");
  switch (t.kind) {
  case Type::Kind::Logical: {
    if (!t.elements.empty())
      return fail("library-type", "logical type has structural elements");
    for (const auto &c : ctx.environment.logicalTypes)
      if (c.contract.name == t.name) {
        if (c.contract.parameters.size() != t.arguments.size())
          return fail("library-type-arity", "logical type argument count");
        for (size_t i = 0; i < t.arguments.size(); ++i) {
          auto s = sortOf(t.arguments[i], ctx.environment);
          if (!s)
            return s.takeError();
          if (!sameSort(*s, Sort::domainOf(c.contract.parameters[i])))
            return fail("library-type-sort",
                        "logical domain argument mismatch");
        }
        return Permissions{!c.contract.affine, c.droppable};
      }
    return fail("library-logical-type",
                "uninstalled logical constructor " + t.name);
  }
  case Type::Kind::Parameter: {
    if (!t.arguments.empty() || !t.elements.empty())
      return fail("library-type", "malformed type parameter");
    auto s = sortOf(StaticTerm::root(t.declaration), ctx.environment);
    if (!s)
      return s.takeError();
    if (!sameSort(*s, Sort::type()))
      return fail("library-type-sort", "parameter is not a type");
    for (const auto &b : ctx.bounds)
      if (identity(b.parameter) == identity(t.declaration))
        return b.permissions;
    return fail("library-type-bound",
                "type parameter has no explicit permission bound");
  }
  case Type::Kind::Abstract: {
    if (t.arguments.size() != 1 || !t.elements.empty())
      return fail("library-type", "malformed abstract member");
    auto s =
        sortOf(StaticTerm::project(t.arguments[0], t.name), ctx.environment);
    if (!s)
      return s.takeError();
    if (!sameSort(*s, Sort::type()))
      return fail("library-type-sort", "abstract member is not a type");
    const auto *i = interfaceFor(t.arguments[0], ctx);
    if (i)
      for (const auto &m : i->types)
        if (m.name == t.name)
          return m.permissions;
    return fail("library-abstract-type",
                "abstract member is not in an assumed interface: " + t.name);
  }
  case Type::Kind::Product:
  case Type::Kind::Record:
  case Type::Kind::Array:
  case Type::Kind::Variant: {
    if (t.kind == Type::Kind::Record || t.kind == Type::Kind::Variant) {
      if (t.kind == Type::Kind::Variant && t.elements.empty())
        return fail("library-variant",
                    "finite variant must name at least one alternative");
      if (auto err = captured(t.declaration, ctx.environment))
        return err;
      if (t.fields.size() != t.elements.size() ||
          (t.kind == Type::Kind::Record && !t.arguments.empty()))
        return fail("library-record", "record field count");
      // A finite variant keeps the exact static actuals of its declaration,
      // including captures no alternative payload mentions. They decide
      // identity, so every one is checked against the captured environment
      // here rather than trusted from the builder.
      for (const auto &a : t.arguments) {
        auto sort = sortOf(a, ctx.environment);
        if (!sort)
          return sort.takeError();
        if (auto err = validateSort(*sort))
          return err;
      }
      std::set<std::string> names;
      for (const auto &f : t.fields)
        if (f.empty() || !names.insert(f).second)
          return fail(t.kind == Type::Kind::Variant ? "library-variant"
                                                    : "library-record",
                      "duplicate or empty field/alternative");
    } else if (t.kind == Type::Kind::Product && !t.arguments.empty())
      return fail("library-type", "product has static arguments");
    if (t.kind == Type::Kind::Array) {
      if (t.arguments.size() != 1 || t.elements.size() != 1)
        return fail("library-array", "array needs one element and count");
      auto s = sortOf(t.arguments[0], ctx.environment);
      if (!s)
        return s.takeError();
      if (!sameSort(*s, Sort::natural()))
        return fail("library-array", "array count is not natural");
    }
    Permissions p{true, true};
    for (const auto &c : t.elements) {
      auto cp = permissions(c, ctx, depth + 1);
      if (!cp)
        return cp.takeError();
      p.copy &= cp->copy;
      p.drop &= cp->drop;
    }
    return p;
  }
  }
  return fail("library-type", "unknown type kind");
}
llvm::Error signature(const Signature &s, const TypeContext &ctx) {
  if (!s.inputLabels.empty()) {
    if (s.inputLabels.size() != s.inputs.size())
      return fail("library-parameter-label",
                  "label count differs from input arity");
    std::set<std::string> labels;
    for (const auto &label : s.inputLabels)
      if (label.empty() || !labels.insert(label).second)
        return fail("library-parameter-label",
                    "empty or duplicate public label");
  }
  for (const auto &p : s.inputs) {
    auto r = permissions(p.type, ctx);
    if (!r)
      return r.takeError();
  }
  for (const auto &p : s.outputs) {
    auto r = permissions(p.type, ctx);
    if (!r)
      return r.takeError();
  }
  if (auto err = validateRequirements(s.preconditions, ctx.environment))
    return err;
  if (auto err = validateRequirements(s.postconditions, ctx.environment))
    return err;
  for (const auto &effect : s.effects)
    if (effect.empty())
      return fail("library-effect", "empty effect name");
  return llvm::Error::success();
}
llvm::Expected<std::vector<Type>> children(const Type &t,
                                           const Environment &e) {
  if (t.kind == Type::Kind::Product || t.kind == Type::Kind::Record)
    return t.elements;
  if (t.kind == Type::Kind::Array && t.elements.size() == 1 &&
      t.arguments.size() == 1) {
    const auto &n = t.arguments[0];
    if (n.kind != StaticTerm::Kind::Natural)
      return fail("library-array-unresolved",
                  "static array expansion needs a selected natural");
    if (n.number > e.expansionLimit)
      return fail("library-limit", "array expansion exceeds limit");
    return std::vector<Type>(n.number, t.elements[0]);
  }
  return fail("library-projection",
              "opaque or logical value has no public structural fields");
}
llvm::Expected<Type> placeType(const Type &t, llvm::ArrayRef<unsigned> path,
                               const TypeContext &ctx) {
  const Type *out = &t;
  for (unsigned index : path) {
    if (out->kind == Type::Kind::Array && out->elements.size() == 1 &&
        out->arguments.size() == 1) {
      const auto &count = out->arguments[0];
      if (count.kind != StaticTerm::Kind::Natural)
        return fail("library-array-unresolved",
                    "static array projection needs a selected natural");
      if (count.number > ctx.environment.expansionLimit)
        return fail("library-limit", "array expansion exceeds limit");
      if (index >= count.number)
        return fail("library-projection", "static projection out of bounds");
      out = &out->elements.front();
    } else if (out->kind == Type::Kind::Product ||
               out->kind == Type::Kind::Record) {
      if (index >= out->elements.size())
        return fail("library-projection", "static projection out of bounds");
      out = &out->elements[index];
    } else {
      return fail("library-projection",
                  "opaque or logical value has no public structural fields");
    }
  }
  return *out;
}
llvm::Error equalTypes(const Type &a, const Type &b,
                       const std::vector<Requirement> &facts,
                       const Environment &e) {
  if (sameType(a, b))
    return llvm::Error::success();
  if (a.kind != b.kind || a.name != b.name ||
      identity(a.declaration) != identity(b.declaration) ||
      a.elements.size() != b.elements.size() || a.fields != b.fields ||
      a.arguments.size() != b.arguments.size())
    return fail("library-type-mismatch", "nominal source types differ");
  std::vector<Requirement> goals;
  for (size_t i = 0; i < a.arguments.size(); ++i)
    goals.push_back({"", {a.arguments[i], b.arguments[i]}});
  if (auto err = prove(facts, goals, e))
    return fail("library-type-mismatch", llvm::toString(std::move(err)));
  for (size_t i = 0; i < a.elements.size(); ++i)
    if (auto err = equalTypes(a.elements[i], b.elements[i], facts, e))
      return err;
  return llvm::Error::success();
}
llvm::Error checkAttributes(const LogicalCall &call,
                            const std::vector<std::string> &attributes,
                            const Environment &e) {
  std::string field = "bls12-381.fr";
  if (call.operation == "field.constant" ||
      call.operation == "vector.constant") {
    field.clear();
    if (!call.arguments.empty()) {
      auto domain = installedDomain(call.arguments[0], e);
      if (!domain)
        return domain.takeError();
      field = *domain;
    }
    if (field.empty()) {
      // 0 and 1 are canonical in every field. Other literals require a
      // selected characteristic or a future owner-supported bound judgment.
      for (const auto &a : attributes)
        if (a != "0" && a != "1")
          return fail("library-attribute-bound",
                      "generic field literal needs a selected characteristic");
      field = "bls12-381.fr";
    }
  }
  if (auto err = protocol::checkParameters(call.operation, attributes, field))
    return fail("library-operation-attributes", llvm::toString(std::move(err)));
  return llvm::Error::success();
}
llvm::Expected<Signature> logicalSignature(const LogicalCall &call,
                                           const Environment &e) {
  const LogicalOperation *op = nullptr;
  for (const auto &o : e.operations)
    if (o.contract.name == call.operation)
      op = &o;
  if (!op)
    return fail("library-operation",
                "uninstalled logical operation " + call.operation);
  const auto &s = op->contract.signature;
  if (s.scope.sorts.size() != s.scope.terms.size())
    return fail("library-operation", "malformed installed scope");
  std::vector<StaticTerm> actuals;
  size_t formal = 0;
  for (size_t i = 0; i < s.scope.terms.size(); ++i) {
    const auto &t = s.scope.terms[i];
    if (t.parent && t.arguments)
      return fail("library-operation", "ambiguous static term");
    if (t.parent) {
      if (*t.parent >= actuals.size())
        return fail("library-operation", "non-topological projection");
      actuals.push_back(StaticTerm::project(actuals[*t.parent], t.name));
    } else if (t.arguments) {
      // Installed application heads must resolve to captured declarations;
      // names alone do not resolve across library namespaces.
      const StaticDeclaration *head = nullptr;
      for (const auto &d : e.statics)
        if (identity(d.id) == t.name)
          head = &d;
      if (!head)
        return fail("library-operation",
                    "uncaptured installed application head");
      std::vector<StaticTerm> args;
      for (unsigned a : *t.arguments) {
        if (a >= actuals.size())
          return fail("library-operation", "non-topological application");
        args.push_back(actuals[a]);
      }
      actuals.push_back(StaticTerm::apply(head->id, std::move(args)));
    } else if (auto fixed = s.scope.constants.find(i);
               fixed != s.scope.constants.end()) {
      const StaticDeclaration *root = nullptr;
      for (const auto &d : e.statics)
        if (identity(d.id) == fixed->second ||
            d.capturedSubject == fixed->second) {
          if (root)
            return fail("library-operation", "ambiguous installed fixed root");
          root = &d;
        }
      if (!root)
        return fail("library-operation", "uncaptured installed fixed root");
      actuals.push_back(StaticTerm::root(root->id));
    } else {
      if (formal == call.arguments.size())
        return fail("library-operation-arity", "missing static argument");
      actuals.push_back(call.arguments[formal++]);
    }
    auto sort = sortOf(actuals.back(), e);
    if (!sort)
      return sort.takeError();
    if (!sameSort(*sort, Sort::domainOf(s.scope.sorts[i])))
      return fail("library-static-sort",
                  "installed operation domain sort mismatch");
  }
  if (formal != call.arguments.size())
    return fail("library-operation-arity", "extra static arguments");
  Signature out;
  out.effects = op->effects;
  auto ports = [&](const std::vector<generic::Type> &ts,
                   std::vector<Port> &ps) -> llvm::Error {
    for (const auto &t : ts) {
      std::vector<StaticTerm> args;
      for (unsigned a : t.arguments) {
        if (a >= actuals.size())
          return fail("library-operation", "bad installed type argument");
        args.push_back(actuals[a]);
      }
      ps.push_back({Type::logical(t.constructor, std::move(args)), ""});
    }
    return llvm::Error::success();
  };
  if (auto err = ports(s.inputs, out.inputs))
    return err;
  if (auto err = ports(s.outputs, out.outputs))
    return err;
  for (const auto &r : s.requirements) {
    Requirement req;
    switch (r.kind) {
    case requirements::Predicate::Kind::Equal:
      if (!r.relation.empty() || r.arguments.size() != 2)
        return fail("library-operation", "malformed equality");
      break;
    case requirements::Predicate::Kind::Relation:
      if (r.relation.empty())
        return fail("library-operation", "empty relation");
      req.relation = r.relation;
      break;
    default:
      return fail("library-operation", "unknown predicate kind");
    }
    for (unsigned a : r.arguments) {
      if (a >= actuals.size())
        return fail("library-operation", "bad installed requirement argument");
      req.arguments.push_back(actuals[a]);
    }
    out.preconditions.push_back(std::move(req));
  }
  return out;
}
} // namespace zkc::frontend::library::detail
