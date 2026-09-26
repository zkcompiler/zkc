#include "LinkInternal.h"
#include "Work.h"
#include "zkc/Contracts/Domains.h"

namespace zkc::frontend::library::detail {
// Substitute actuals without crossing any abstract representation boundary.
llvm::Expected<Type> World::publicType(const Type &t, const LinkScope &scope,
                                       unsigned depth) {
  if (depth > 128)
    return fail("library-substitution-cycle", "public type substitution cycle");
  if (t.kind == Type::Kind::Parameter) {
    for (const auto &a : scope.arguments.types)
      if (identity(a.first) == identity(t.declaration))
        return publicType(a.second, scope, depth + 1);
    return fail("library-open-type",
                "unselected type parameter " + t.declaration.name);
  }
  Type out = t;
  if (t.kind == Type::Kind::Abstract) {
    if (t.arguments.size() != 1)
      return fail("library-type", "malformed abstract member");
    auto node = component(t.arguments[0], scope);
    if (!node)
      return node.takeError();
    out.arguments[0] = (*node)->selected;
  } else {
    for (auto &a : out.arguments) {
      auto v = term(a, scope);
      if (!v)
        return v.takeError();
      a = *v;
    }
  }
  for (auto &a : out.elements) {
    auto v = publicType(a, scope, depth + 1);
    if (!v)
      return v.takeError();
    a = *v;
  }
  return out;
}
llvm::Expected<Permissions> World::publicPermissions(const Type &t,
                                                     const LinkScope &scope) {
  auto actual = publicType(t, scope);
  if (!actual)
    return actual.takeError();
  std::vector<Import> imports;
  for (const auto &node : selections)
    imports.push_back({node->selected, node->implementation.interface});
  const std::vector<TypeBound> noBounds;
  return permissions(*actual, TypeContext{environment, imports, noBounds});
}
llvm::Expected<Type> World::type(const Type &t, const LinkScope &scope,
                                 unsigned depth) {
  if (depth > 128)
    return fail("library-representation-cycle",
                "cyclic or excessive type substitution");
  if (t.kind == Type::Kind::Parameter) {
    for (const auto &a : scope.arguments.types)
      if (identity(a.first) == identity(t.declaration))
        return type(a.second, scope, depth + 1);
    return fail("library-open-type",
                "unselected ordinary type parameter " + t.declaration.name);
  }
  if (t.kind == Type::Kind::Abstract) {
    if (t.arguments.size() != 1)
      return fail("library-type", "malformed abstract member");
    auto node = component(t.arguments[0], scope);
    if (!node)
      return node.takeError();
    auto rep = (*node)->implementation.representations.find(t.name);
    if (rep == (*node)->implementation.representations.end())
      return fail("library-representation",
                  "missing private representation " + t.name);
    return type(rep->second, (*node)->scope, depth + 1);
  }
  Type out = t;
  for (auto &a : out.arguments) {
    auto v = term(a, scope);
    if (!v)
      return v.takeError();
    a = *v;
  }
  for (auto &a : out.elements) {
    auto v = type(a, scope, depth + 1);
    if (!v)
      return v.takeError();
    a = *v;
  }
  const std::vector<Import> imports;
  const std::vector<TypeBound> bounds;
  TypeContext ctx{environment, imports, bounds};
  auto p = permissions(out, ctx);
  if (!p)
    return p.takeError();
  if (out.kind == Type::Kind::Logical) {
    for (const auto &a : out.arguments) {
      auto domain = resolvedDomain(a, environment);
      if (!domain)
        return domain.takeError();
    }
  }
  return out;
}
llvm::Expected<std::vector<Requirement>>
World::requirements(const std::vector<Requirement> &rs,
                    const LinkScope &scope) {
  std::vector<Requirement> result = rs;
  for (auto &r : result)
    for (auto &a : r.arguments) {
      auto t = term(a, scope);
      if (!t)
        return t.takeError();
      a = *t;
    }
  if (auto err = validateRequirements(result, environment))
    return err;
  return result;
}
llvm::Expected<Signature> World::signature(const Signature &s,
                                           const LinkScope &scope) {
  Signature out = s;
  for (auto &p : out.inputs) {
    auto t = type(p.type, scope);
    if (!t)
      return t.takeError();
    p.type = *t;
  }
  for (auto &p : out.outputs) {
    auto t = type(p.type, scope);
    if (!t)
      return t.takeError();
    p.type = *t;
  }
  auto pre = requirements(s.preconditions, scope);
  if (!pre)
    return pre.takeError();
  out.preconditions = *pre;
  auto post = requirements(s.postconditions, scope);
  if (!post)
    return post.takeError();
  out.postconditions = *post;
  return out;
}
llvm::Error World::bounds(const std::vector<TypeBound> &bs,
                          const LinkScope &scope) {
  for (const auto &b : bs) {
    auto p = publicPermissions(Type::parameter(b.parameter), scope);
    if (!p)
      return p.takeError();
    if ((b.permissions.copy && !p->copy) || (b.permissions.drop && !p->drop))
      return fail("library-permission-bound",
                  "selected type does not support bound on " +
                      b.parameter.name);
  }
  return llvm::Error::success();
}
llvm::Expected<Layout> World::layout(const Type &source, const LinkScope &scope,
                                     unsigned depth) {
  if (auto error = chargeType(budget, source))
    return error;
  if (!depth)
    layoutSteps = 0;
  if (++layoutSteps > environment.expansionLimit)
    return fail("library-limit", "layout expansion work exceeds limit");
  if (depth > 128)
    return fail("library-representation-cycle",
                "layout recursion exceeds limit");

  auto concrete = type(source, scope);
  if (!concrete)
    return concrete.takeError();
  Layout result{source, *concrete, {}};
  if (source.kind == Type::Kind::Parameter) {
    for (const auto &a : scope.arguments.types)
      if (identity(a.first) == identity(source.declaration)) {
        auto l = layout(a.second, scope, depth + 1);
        if (!l)
          return l.takeError();
        result.leaves = l->leaves;
        return result;
      }
    return fail("library-open-type", "type parameter layout is unresolved");
  }
  if (source.kind == Type::Kind::Abstract) {
    auto node = component(source.arguments[0], scope);
    if (!node)
      return node.takeError();
    const auto &impl = (*node)->implementation;
    auto rep = impl.representations.find(source.name);
    if (rep == impl.representations.end())
      return fail("library-representation", "missing representation");
    auto l = layout(rep->second, (*node)->scope, depth + 1);
    if (!l)
      return l.takeError();
    result.leaves = l->leaves;
    result.sourceType = Type::abstract((*node)->selected, source.name);
    const TypeMember *member = nullptr;
    for (const auto &m : impl.interface.declaration().types)
      if (m.name == source.name)
        member = &m;
    if (!member)
      return fail("library-representation", "unknown public type slot");
    if (result.leaves.empty() &&
        (!member->permissions.copy || !member->permissions.drop)) {
      if (member->permissions.copy || !member->permissions.drop)
        return fail(
            "library-resource-profile",
            "zero-storage resource requires supported affine/drop profile");
      Writer slot;
      slot.add((*node)->key);
      slot.add(source.name);
      result.leaves.push_back({LayoutLeaf::Kind::ResourceUnit,
                               result.sourceType,
                               slot.bytes,
                               member->permissions,
                               {}});
    }
    return result;
  }
  if (source.kind == Type::Kind::Logical) {
    const std::vector<Import> none;
    const std::vector<TypeBound> noBounds;
    auto p = permissions(*concrete, TypeContext{environment, none, noBounds});
    if (!p)
      return p.takeError();
    result.leaves.push_back({LayoutLeaf::Kind::Logical, *concrete, {}, *p, {}});
    return result;
  }
  if (source.kind == Type::Kind::Variant) {
    auto nominal = publicType(source, scope);
    if (!nominal)
      return nominal.takeError();
    auto permission = publicPermissions(source, scope);
    if (!permission)
      return permission.takeError();
    auto exact = normalizedTypeTree(*nominal, environment);
    if (!exact)
      return exact.takeError();
    LayoutLeaf leaf{LayoutLeaf::Kind::Variant, *nominal, {}, *permission, {}};
    leaf.variantIdentity = *exact;
    for (const auto &payload : source.elements) {
      auto child = layout(payload, scope, depth + 1);
      if (!child)
        return child.takeError();
      leaf.alternatives.push_back(std::move(child->leaves));
    }
    result.leaves.push_back(std::move(leaf));
    return result;
  }
  Type shape = source;
  // Select array extent without erasing the source element's opaque identity.
  if (source.kind == Type::Kind::Array) {
    auto count = term(source.arguments[0], scope);
    if (!count)
      return count.takeError();
    shape.arguments[0] = *count;
  }
  if (shape.kind == Type::Kind::Array) {
    const auto &count = shape.arguments.front();
    if (count.kind == StaticTerm::Kind::Natural)
      if (auto error = chargeType(budget, shape.elements.front(), count.number))
        return error;
  } else {
    for (const auto &element : shape.elements)
      if (auto error = chargeType(budget, element))
        return error;
  }
  auto elements = children(shape, environment);
  if (!elements)
    return elements.takeError();
  for (size_t i = 0; i < elements->size(); ++i) {
    auto child = layout((*elements)[i], scope, depth + 1);
    if (!child)
      return child.takeError();
    if (auto error = work::charge(budget, WorkAccount::LibraryFormation,
                                  child->leaves.size()))
      return error;
    for (auto leaf : child->leaves) {
      leaf.path.insert(leaf.path.begin(), i);
      result.leaves.push_back(std::move(leaf));
      if (result.leaves.size() > environment.expansionLimit)
        return fail("library-limit", "layout leaf count exceeds limit");
    }
  }
  return result;
}
} // namespace zkc::frontend::library::detail
