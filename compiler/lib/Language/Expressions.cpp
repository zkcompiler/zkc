#include "BodyCheck.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/Services.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
std::optional<Type> BodyChecker::hint(uint32_t id, unsigned depth) {
  auto &expr = syntax.expressions[id];
  if (depth > checker.work.limits.expressionDepth ||
      !checker.types.charge(1, expr.span)) {
    if (!checker.types.diagnostic)
      fail("source.limit", "expression depth limit exceeded", expr.span);
    return {};
  }
  using K = Expression::Kind;
  if (expr.kind == K::Kernel || expr.kind == K::Intrinsic) {
    std::vector<Type> arguments;
    std::vector<std::string> parameters;
    std::vector<AssetReference> references;
    auto signature =
        expr.kind == K::Kernel
            ? kernelSignature(expr, arguments, parameters, references)
            : intrinsicSignature(expr, arguments);
    if (!signature)
      return {};
    return signature->resultType();
  }
  if (expr.kind == K::MethodCall) {
    if (expr.text == "index")
      return Type(Type::Kind::Index);
    auto root = service(syntax.expressions[expr.children.front()]);
    return root ? std::optional<Type>(body.services[root->index].field)
                : std::nullopt;
  }
  if (expr.kind == K::Boolean || expr.kind == K::Equal)
    return Type{};
  if (expr.kind == K::Decimal)
    return {};
  if (expr.kind == K::Name) {
    auto p = place(id, depth);
    return p ? std::optional<Type>(body.values[p->first.index].type)
             : std::nullopt;
  }
  if (expr.kind == K::Projection) {
    auto p = place(id, depth);
    return p ? projected(body.values[p->first.index].type, p->second, expr.span)
             : std::nullopt;
  }
  if (expr.kind == K::Tuple) {
    Type result(expr.children.empty() ? Type::Kind::Unit : Type::Kind::Tuple);
    for (auto child : expr.children) {
      auto t = hint(child, depth + 1);
      if (!t)
        return {};
      result.arguments.push_back(*t);
    }
    return result;
  }
  if (expr.kind == K::Array) {
    if (expr.children.empty())
      return {};
    auto t = hint(expr.children.front(), depth + 1);
    if (!t)
      return {};
    Type result(Type::Kind::Array);
    result.arguments = {*t};
    result.dimension = Natural::constant(expr.children.size());
    return result;
  }
  if (expr.kind == K::Call || expr.kind == K::Record) {
    // Constructor and generic call result inference is performed by expression
    // checking; hints never choose an implementation or consume an argument.
    if (expr.kind == K::Record) {
      SyntaxType term;
      term.name = expr.text;
      term.arguments = expr.arguments;
      term.span = expr.span;
      return checker.type(decl, term);
    }
    if (expr.text == "index")
      return Type(Type::Kind::Index);
    if (expr.text == "unpack")
      return {};
    auto parts = StringRef(expr.text).rsplit("::");
    if (!parts.second.empty()) {
      auto saved = checker.types.diagnostic;
      auto target = checker.resolve(decl, parts.first, expr.span);
      if (!target)
        checker.types.diagnostic = saved;
      else if (checker.output.declarations[target->index].kind ==
               Declaration::Kind::Variant) {
        SyntaxType term;
        term.name = parts.first.str();
        term.arguments = expr.arguments;
        term.span = expr.span;
        return checker.type(decl, term);
      }
    }
    auto target = callable(expr);
    if (!target)
      return {};
    auto &callee = checker.output.declarations[target->first.index];
    if (callee.kind != Declaration::Kind::Math &&
        callee.kind != Declaration::Kind::Local)
      return {};
    std::vector<std::optional<Type>> inputs;
    for (auto child : expr.children)
      inputs.push_back(hint(child, depth + 1));
    if (checker.types.diagnostic)
      return {};
    auto args = actuals(callee, expr, inputs, {}, target->second);
    if (!args) {
      if (checker.types.diagnostic &&
          checker.types.diagnostic->code == "source.inference")
        checker.types.diagnostic.reset();
      return {};
    }
    auto sub = checker.types.substitution(callee, *args);
    if (target->second && callee.parent)
      sub.emplace(
          "self:" +
              checker.output.declarations[callee.parent->index].qualifiedName,
          *target->second);
    return checker.types.substitute(callee.outputs.front().type, sub,
                                    expr.span);
  }
  if (expr.kind == K::If || expr.kind == K::Match || expr.kind == K::For ||
      expr.kind == K::Apply || expr.kind == K::Repeat ||
      expr.kind == K::FinishIf)
    return {};
  for (auto child : expr.children) {
    auto result = hint(child, depth + 1);
    if (result || checker.types.diagnostic)
      return result;
  }
  return {};
}
std::optional<ValueId> BodyChecker::expression(uint32_t id,
                                               std::optional<Type> expected,
                                               unsigned depth) {
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
  if (expr.kind == K::Apply || expr.kind == K::Repeat ||
      expr.kind == K::FinishIf) {
    fail("source.mode", "protocol action requires a complete let statement",
         expr.span);
    return {};
  }
  if (expr.kind == K::Kernel) {
    result = kernel(expr, depth);
  } else if (expr.kind == K::Intrinsic) {
    result = intrinsic(expr, depth);
  } else if (expr.kind == K::MethodCall) {
    bool index = expr.text == "index";
    if (!protocol() || owner || (expr.text != "draw" && !index) ||
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
    auto found = bindings.find(expr.text);
    if (found == bindings.end()) {
      fail("source.name", "unknown local value: " + expr.text, expr.span);
      return {};
    }
    result = found->second;
  } else if (expr.kind == K::Projection) {
    auto p = place(id, depth);
    if (!p)
      return {};
    auto type =
        projected(body.values[p->first.index].type, p->second, expr.span);
    if (!type || !use(p->first, expr.span, p->second))
      return {};
    result = emit(Projection{p->first, p->second}, *type,
                  body.values[p->first.index].components, expr.span);
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
    result = call(expr, expected, depth);
  else if (expr.kind == K::Tuple || expr.kind == K::Array ||
           expr.kind == K::Record)
    result = construct(expr, expected, depth);
  else if (expr.kind == K::If || expr.kind == K::Match || expr.kind == K::For)
    result = control(expr, expected, depth);
  else {
    bool equal = expr.kind == K::Equal;
    auto operand = equal ? std::optional<Type>{} : expected;
    if (!operand)
      for (auto child : expr.children) {
        operand = hint(child, depth + 1);
        if (checker.types.diagnostic)
          return {};
        if (operand)
          break;
      }
    if (!operand) {
      fail("source.inference", "expression needs a unique operand type",
           expr.span);
      return {};
    }
    bool group = operand->kind == T::Group, index = operand->kind == T::Index;
    if (!equal && operand->kind != T::Field && !group && !index) {
      fail("source.type", "arithmetic requires a field, group or local index",
           expr.span);
      return {};
    }
    if (equal && operand->kind != T::Field && !group && !index &&
        operand->kind != T::Boolean) {
      fail("source.type", "equality is defined only for scalar values",
           expr.span);
      return {};
    }
    if (group && expr.kind == K::Subtract) {
      fail("source.type",
           "group subtraction requires an explicitly supported operation",
           expr.span);
      return {};
    }
    if (index && !local()) {
      fail("source.mode", "index arithmetic requires local mode", expr.span);
      return {};
    }
    std::vector<ValueId> args;
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      auto type = operand;
      if (group && expr.kind == K::Multiply && i == 1) {
        type = checker.types.associated(*operand, "Scalar", expr.span);
        if (!type)
          return {};
      }
      auto arg = expression(expr.children[i], type, depth + 1);
      if (!arg || !use(*arg, expr.span))
        return {};
      args.push_back(*arg);
    }
    auto components = combine(args, expr.span);
    if (!components)
      return {};
    auto type = equal ? Type{} : *operand;
    if (local()) {
      std::string family = group                         ? "curve"
                           : index                       ? "index"
                           : operand->kind == T::Boolean ? "bool"
                                                         : "field";
      std::string op = equal                      ? "equal"
                       : expr.kind == K::Add      ? "add"
                       : expr.kind == K::Subtract ? "sub"
                       : group                    ? "scale"
                                                  : "mul";
      result = emit(LocalPrimitive{family + "." + op, std::move(args), {}},
                    type, {}, expr.span);
      body.mayStop |= index && !equal;
    } else {
      for (auto arg : args)
        if (!data(body.values[arg.index].type, expr.span))
          return {};
      if (math() && !components->empty())
        body.formationRequirements.push_back(*components);
      auto identity =
          group ? (equal                 ? MathematicalIdentity::GroupEqual
                   : expr.kind == K::Add ? MathematicalIdentity::GroupAdd
                                         : MathematicalIdentity::GroupScale)
          : expr.kind == K::Add         ? MathematicalIdentity::FieldAdd
          : expr.kind == K::Subtract    ? MathematicalIdentity::FieldSubtract
          : expr.kind == K::Multiply    ? MathematicalIdentity::FieldMultiply
          : operand->kind == T::Boolean ? MathematicalIdentity::BooleanEqual
                                        : MathematicalIdentity::FieldEqual;
      result = emit(MathValue{identity, std::move(args), {}}, type, *components,
                    expr.span);
    }
  }
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
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      std::optional<Type> field;
      if (expected && i < expected->arguments.size())
        field = expected->arguments[i];
      else
        field = hint(expr.children[i], depth + 1);
      if (!field) {
        if (!checker.types.diagnostic)
          fail("source.inference", "tuple element needs a type", expr.span);
        return {};
      }
      fields.push_back({std::to_string(i), *field, true, expr.span});
      if (!expected)
        type.arguments.push_back(*field);
    }
    if (type.arguments.size() != expr.children.size()) {
      fail("source.type", "tuple arity differs", expr.span);
      return {};
    }
  } else if (expr.kind == E::Array) {
    type = Type(T::Array);
    type.dimension = Natural::constant(expr.children.size());
    std::optional<Type> element;
    if (expected && expected->kind == T::Array) {
      type = *expected;
      element = type.arguments.front();
    } else
      for (auto child : expr.children) {
        element = hint(child, depth + 1);
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
    SyntaxType term;
    term.name = expr.text;
    term.arguments = expr.arguments;
    term.span = expr.span;
    auto resolved = checker.type(decl, term);
    if (!resolved)
      return {};
    type = *resolved;
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
    auto v = expression(expr.children[i], fields[index].type, depth + 1);
    if (!v || !use(*v, expr.span))
      return {};
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
