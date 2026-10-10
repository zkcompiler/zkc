#include "BodyCheck.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/Services.h"
#include <algorithm>
#include <cassert>
using namespace llvm;
namespace zkc::language::detail {
std::optional<ValueId> BodyChecker::expression(uint32_t id,
                                               std::optional<Type> expected,
                                               unsigned depth,
                                               bool allowUntypedStop) {
  assert((!protocol() || placement) &&
         "protocol expression requires a statement inference scope");
  TypeScope types(*this, id, expected);
  if (!types)
    return {};
  if (!expected)
    expected = inferredType(id);
  auto result = evaluate(id, expected, depth, allowUntypedStop);
  const auto &expr = syntax.expressions[id];
  if (!result && body.stopped && !checker.types.diagnostic &&
      expr.kind != Expression::Kind::Block &&
      expr.kind != Expression::Kind::If && expr.kind != Expression::Kind::Match)
    fail("source.unreachable", "operation follows an operand that always stops",
         expr.span);
  return result;
}
std::optional<ValueId> BodyChecker::evaluate(uint32_t id,
                                             std::optional<Type> expected,
                                             unsigned depth,
                                             bool allowUntypedStop) {
  const auto &expr = syntax.expressions[id];
  if (depth > checker.work.limits.expressionDepth ||
      !checker.types.charge(1, expr.span)) {
    if (!checker.types.diagnostic)
      fail("source.limit", "expression depth limit exceeded", expr.span);
    return {};
  }
  using K = Expression::Kind;
  using T = Type::Kind;
  std::optional<ValueId> result;
  if (expr.kind == K::FinishIf) {
    fail("source.mode", "protocol action requires a complete let statement",
         expr.span);
    return {};
  }
  if (expr.kind == K::And || expr.kind == K::Or) {
    result = boolean(expr, depth);
  } else if (expr.kind == K::Kernel) {
    result = kernel(expr, depth);
  } else if (expr.kind == K::Intrinsic) {
    result = intrinsic(expr, depth);
  } else if (expr.kind == K::Map) {
    result = bulk(expr, depth);
  } else if (expr.kind == K::MethodCall) {
    bool index = expr.text == "index";
    if (!protocol() || (expr.text != "draw" && !index) ||
        expr.children.size() != 1 ||
        expr.arguments.size() != (index ? 1u : 0u)) {
      fail("source.service",
           "managed query requires service.draw() or service.index<N>() in "
           "protocol mode",
           expr.span);
      return {};
    }
    auto root = service(syntax.expressions[expr.children.front()]);
    if (!root)
      return {};
    const auto &port = body.services[root->index];
    if (!active({port.owner}, expr.span))
      return {};
    if (!index) {
      result =
          emit(ServiceQuery{*root, {}}, port.field, {port.owner}, expr.span);
    } else {
      // UniformIndex uses the installed bit sampler, which is distinct from
      // reducing a field element; the field must grant IndexRandomness.
      if (!checker.types.entails(
              &decl,
              CapabilityBound{"IndexRandomness", {port.field}, expr.span},
              "source.service"))
        return {};
      auto bound = checker.type(decl, expr.arguments.front());
      if (!bound)
        return {};
      if (bound->kind != T::Natural) {
        fail("source.service", "index domain must be a static natural",
             expr.span);
        return {};
      }
      if (bound->dimension.isClosed() &&
          !protocol::uniformIndexBound(bound->dimension.closedValue())) {
        fail("source.service",
             "index domain must be a power of two no greater than 2^63",
             expr.span);
        return {};
      }
      result = emit(ServiceQuery{*root, bound->dimension}, Type(T::Index),
                    {port.owner}, expr.span);
    }
  } else if (expr.kind == K::Name) {
    auto p = place(id, depth);
    if (!p)
      return {};
    result = p->first;
  } else if (expr.kind == K::Projection) {
    auto p = place(id, depth);
    if (!p)
      return {};
    auto type =
        projected(body.values[p->first.index].type, p->second, expr.span);
    if (!type || !use(p->first, expr.span, p->second))
      return {};
    result = emit(Projection{p->first, p->second}, *type, components(p->first),
                  expr.span);
  } else if (expr.kind == K::Boolean || expr.kind == K::Decimal) {
    Type type;
    if (expr.kind == K::Decimal) {
      if (!expected ||
          (expected->kind != T::Field && expected->kind != T::Index)) {
        fail("source.inference",
             "numeric literal needs a unique field or index context",
             expr.span);
        return {};
      }
      type = *expected;
      if (type.kind == T::Index) {
        uint64_t number;
        if (StringRef(expr.text).getAsInteger(10, number)) {
          fail("source.literal", "index literal overflows uint64", expr.span);
          return {};
        }
        if (!local()) {
          fail("source.mode", "index literals currently require local mode",
               expr.span);
          return {};
        }
        result =
            emit(LocalPrimitive{"index.constant", {}, {std::to_string(number)}},
                 type, {}, expr.span);
      } else {
        if (type.symbolic) {
          if (auto error = protocol::checkGenericParameters("field.constant",
                                                            {expr.text})) {
            fail("source.literal", toString(std::move(error)), expr.span);
            return {};
          }
        } else if (auto error = protocol::checkParameters(
                       "field.constant", {expr.text}, type.domain)) {
          fail("source.literal", toString(std::move(error)), expr.span);
          return {};
        }
      }
    }
    if (!result) {
      if (local())
        result = emit(LocalPrimitive{expr.kind == K::Boolean ? "bool.constant"
                                                             : "field.constant",
                                     {},
                                     {expr.text}},
                      type, {}, expr.span);
      else
        result = emit(MathValue{expr.kind == K::Boolean
                                    ? MathematicalIdentity::BooleanConstant
                                    : MathematicalIdentity::FieldConstant,
                                {},
                                expr.text},
                      type, math() ? std::vector<unsigned>{} : allRoles(),
                      expr.span);
    }
  } else if (expr.kind == K::Call)
    result = call(expr, depth);
  else if (expr.kind == K::Tuple || expr.kind == K::Array ||
           expr.kind == K::Record)
    result = construct(expr, expected, depth);
  else if (expr.kind == K::Block)
    result = block(expr, expected, allowUntypedStop);
  else if (expr.kind == K::For && protocol()) {
    if (repeat(expr))
      result = pack({}, expr.span);
  } else if (expr.kind == K::If || expr.kind == K::Match || expr.kind == K::For)
    result = control(expr, expected, depth, allowUntypedStop);
  else
    result = call(expr, depth);
  if (result && expected && body.values[result->index].type != *expected) {
    fail("source.type", "expression type does not match context", expr.span);
    return {};
  }
  return result;
}
std::optional<ValueId> BodyChecker::construct(const Expression &expr,
                                              std::optional<Type> expected,
                                              unsigned depth) {
  using E = Expression::Kind;
  using T = Type::Kind;
  Type type;
  std::vector<TypeField> fields;
  if (expr.kind == E::Tuple) {
    type = Type(expr.children.empty() ? T::Unit : T::Tuple);
    if (expected) {
      if (expected->kind != type.kind) {
        fail("source.type", "tuple does not match expected type", expr.span);
        return {};
      }
      type = *expected;
    }
    if (!expected)
      type.arguments.resize(expr.children.size());
    if (type.arguments.size() != expr.children.size()) {
      fail("source.type", "tuple arity differs", expr.span);
      return {};
    }
    for (unsigned i = 0; i < type.arguments.size(); ++i)
      fields.push_back({std::to_string(i), type.arguments[i], true, expr.span});
  } else if (expr.kind == E::Array) {
    type = Type(T::Array);
    type.dimension = Natural::constant(expr.children.size());
    std::optional<Type> element;
    if (expected && expected->kind == T::Array) {
      type = *expected;
      element = type.arguments.front();
    } else
      for (auto child : expr.children) {
        element = inferredType(child);
        if (element || checker.types.diagnostic)
          break;
      }
    if (!element) {
      if (!checker.types.diagnostic)
        fail("source.inference", "array literal needs an element type",
             expr.span);
      return {};
    }
    if (type.dimension != Natural::constant(expr.children.size())) {
      fail("source.type", "array literal length differs", expr.span);
      return {};
    }
    type.arguments = {*element};
    for (unsigned i = 0; i < expr.children.size(); ++i)
      fields.push_back({std::to_string(i), *element, true, expr.span});
  } else {
    type =
        inference->expressions.at(uint32_t(&expr - syntax.expressions.data()));
    if (type.kind != T::Record) {
      fail("source.type", "named field constructor requires a record",
           expr.span);
      return {};
    }
    auto fs = checker.types.fields(type, expr.span);
    if (!fs)
      return {};
    fields = std::move(*fs);
    if ((restricted(type) ||
         llvm::any_of(fields, [](auto &f) { return !f.isPublic; })) &&
        !checker.types.constructorAllowed(decl, type)) {
      fail("source.private",
           "record constructor is private to its defining module", expr.span);
      return {};
    }
  }
  if (fields.size() != expr.children.size()) {
    fail("source.field", "constructor field count differs", expr.span);
    return {};
  }
  std::vector<ValueId> values(fields.size());
  std::set<unsigned> assigned;
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    unsigned index = i;
    if (expr.kind == E::Record) {
      auto found = llvm::find_if(
          fields, [&](auto &f) { return f.name == expr.labels[i]; });
      if (found == fields.end()) {
        fail("source.field", "unknown constructor field", expr.span);
        return {};
      }
      index = found - fields.begin();
    }
    if (!assigned.insert(index).second) {
      fail("source.duplicate", "duplicate constructor field", expr.span);
      return {};
    }
    // Evaluate each field exactly once, in source order.
    const bool inferred = expr.kind == E::Tuple && !expected;
    auto v = expression(expr.children[i],
                        inferred ? std::nullopt
                                 : std::optional<Type>(fields[index].type),
                        depth + 1);
    if (!v || !use(*v, expr.span))
      return {};
    if (inferred)
      type.arguments[index] = body.values[v->index].type;
    values[index] = *v;
  }
  auto caps = checker.types.permissions(type, expr.span, &decl);
  if (!caps)
    return {};
  if (!local() && (!caps->copy || !caps->drop)) {
    fail("source.mode", "restricted construction requires local mode",
         expr.span);
    return {};
  }
  auto components = combine(values, expr.span);
  if (!components)
    return {};
  return emit(Construct{std::move(values), {}}, type, *components, expr.span);
}
} // namespace zkc::language::detail
