#include "BodyCheck.h"
#include "TypeInference.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
/// Collect type equations without evaluating source. BodyChecker remains the
/// authority for execution modes, resources, effects and participant placement.
class ExpressionInference {
  using Variable = TypeInference::Variable;
  using K = Expression::Kind;
  using T = Type::Kind;
  struct Result {
    Variable type;
    bool stopped = false;
  };
  struct Call {
    uint32_t expression;
    DeclarationId target;
    TypeInference::Parameters parameters;
    bool checked = false;
  };
  BodyChecker &owner;
  Checker &checker;
  Declaration &decl;
  const SyntaxDeclaration &syntax;
  TypeInference types;
  std::map<BindingId, Variable> bindings;
  std::map<BindingId, Type> services;
  std::map<uint32_t, Result> expressions;
  std::vector<Call> calls;
  ExpressionTypes output;

  bool fail(StringRef code, const Twine &message, Span span) {
    return checker.types.fail(code, message, span);
  }
  Variable known(const Type &type, Span span) {
    return types.known(type, span);
  }
  void constrain(Variable variable, const Type &type, Span span) {
    types.equal(variable, known(type, span), span);
  }
  Variable annotation(const SyntaxType &term) {
    auto type = checker.type(decl, term);
    return type ? known(*type, term.span) : types.fresh(term.span);
  }
  Variable binding(BindingId id, Span span) {
    if (auto it = bindings.find(id); it != bindings.end())
      return it->second;
    if (auto it = owner.bindings.find(id); it != owner.bindings.end()) {
      auto value = known(it->second.type, span);
      bindings.emplace(id, value);
      return value;
    }
    fail("source.name", "expected an available data binding", span);
    return types.fresh(span);
  }
  Variable aggregate(T kind, std::vector<Variable> children, Span span) {
    if (kind == T::Array) {
      auto element = types.fresh(span);
      for (auto child : children)
        types.equal(element, child, span);
      Type length(T::Natural);
      length.dimension = Natural::constant(children.size());
      children = {element, known(length, span)};
    }
    return types.shape(Type(kind), std::move(children), span);
  }
  Variable packed(std::vector<Variable> values, Span span) {
    if (values.size() == 1)
      return values.front();
    auto kind = values.empty() ? T::Unit : T::Tuple;
    return aggregate(kind, std::move(values), span);
  }
  std::optional<Type> service(uint32_t id) {
    const auto &expr = syntax.expressions[id];
    if (expr.binding)
      if (auto it = services.find(*expr.binding); it != services.end())
        return it->second;
    if (expr.binding)
      if (auto it = owner.services.find(*expr.binding);
          it != owner.services.end())
        return owner.body.services[it->second.index].field;
    fail("source.service", "expected a managed service binding", expr.span);
    return {};
  }
  bool finishCalls(unsigned begin, Span span) {
    if (!types.solve(span))
      return false;
    for (unsigned i = begin; i < calls.size(); ++i) {
      auto &call = calls[i];
      if (call.checked)
        continue;
      const auto &callee = checker.output.declarations[call.target.index];
      auto callSpan = syntax.expressions[call.expression].span;
      Substitution substitution;
      for (const auto &[name, variable] : call.parameters) {
        auto value = types.get(variable, callSpan);
        if (!value)
          return checker.types.diagnostic
                     ? false
                     : fail(
                           "source.inference",
                           "static argument needs an explicit type or argument",
                           callSpan);
        substitution.emplace(name, *value);
      }
      std::vector<Type> arguments;
      for (const auto &parameter : callee.parameters)
        arguments.push_back(substitution.at(parameter.atom));
      if (!checker.types.checkArguments(callee, arguments, callSpan, &decl,
                                        substitution))
        return false;
      for (const auto &bound : callee.bounds)
        if (!checker.types.assumptions(decl, bound, substitution, callSpan))
          return false;
      output.arguments.emplace(call.expression, std::move(arguments));
      call.checked = true;
    }
    return true;
  }
  std::vector<Variable> application(uint32_t id, const Declaration &callee,
                                    std::optional<Type> component,
                                    unsigned depth) {
    const auto &expr = syntax.expressions[id];
    if (!callee.abstract) {
      if (!checker.body(callee.id, owner.callDepth + 1))
        return {};
      checker.bodyHeights[decl.id.index] =
          std::max(checker.bodyHeights[decl.id.index],
                   checker.bodyHeights[callee.id.index] + 1);
    }
    TypeInference::Parameters parameters;
    for (const auto &parameter : callee.parameters)
      parameters.emplace(parameter.atom, types.fresh(expr.span));
    unsigned inherited = 0;
    if (component && callee.parent) {
      const auto &interface = checker.output.declarations[callee.parent->index];
      inherited = interface.parameters.size();
      for (unsigned i = 0; i < inherited; ++i)
        constrain(parameters.at(interface.parameters[i].atom),
                  component->arguments[i], expr.span);
      parameters.emplace("self:" + interface.qualifiedName,
                         known(*component, expr.span));
    }
    if (!expr.arguments.empty()) {
      if (expr.arguments.size() + inherited != callee.parameters.size()) {
        fail("source.generic", "static argument count differs", expr.span);
        return {};
      }
      for (unsigned i = 0; i < expr.arguments.size(); ++i)
        if (expr.arguments[i].kind != SyntaxType::Kind::Hole)
          types.equal(parameters.at(callee.parameters[inherited + i].atom),
                      annotation(expr.arguments[i]), expr.span);
    }
    bool protocol = callee.kind == Declaration::Kind::Protocol;
    if (expr.children.size() !=
        (protocol ? callee.inputOrder.size() : callee.inputs.size())) {
      fail("source.call", "call input count differs", expr.span);
      return {};
    }
    calls.push_back({id, callee.id, parameters});
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      auto slot =
          protocol
              ? callee.inputOrder[i]
              : Declaration::InputSlot{Declaration::InputSlot::Kind::Data, i};
      if (slot.kind == Declaration::InputSlot::Kind::Service) {
        auto field = service(expr.children[i]);
        if (field)
          types.equal(types.instantiate(callee.services[slot.index].field,
                                        parameters, expr.span),
                      known(*field, expr.span), expr.span);
      } else {
        auto parameter = types.instantiate(callee.inputs[slot.index].type,
                                           parameters, expr.span);
        auto argument = expression(expr.children[i], depth + 1);
        types.equal(parameter, argument.type, expr.span);
      }
    }
    std::vector<Variable> results;
    for (const auto &port : callee.outputs)
      results.push_back(types.instantiate(port.type, parameters, expr.span));
    return results;
  }
  void bind(const Pattern &pattern, Variable value, unsigned depth) {
    if (checker.types.diagnostic)
      return;
    if (depth > checker.work.limits.expressionDepth) {
      fail("source.limit", "inference pattern depth exceeded", pattern.span);
      return;
    }
    if (pattern.binding) {
      bindings.emplace(*pattern.binding, value);
      return;
    }
    if (pattern.children.empty())
      return;
    auto type = types.get(value, pattern.span);
    if (!type) {
      if (!checker.types.diagnostic)
        fail("source.inference", "binding pattern needs a known type",
             pattern.span);
      return;
    }
    auto fields = checker.types.fields(*type, pattern.span);
    if (!fields)
      return;
    if (fields->size() != pattern.children.size()) {
      fail("source.binding", "pattern must cover every field exactly once",
           pattern.span);
      return;
    }
    for (unsigned i = 0; i < pattern.children.size(); ++i) {
      auto field = fields->begin() + i;
      if (pattern.kind == Pattern::Kind::Record)
        field = llvm::find_if(*fields, [&](const auto &field) {
          return field.name == pattern.labels[i];
        });
      if (field == fields->end()) {
        fail("source.field", "unknown pattern field", pattern.span);
        return;
      }
      bind(pattern.children[i], known(field->type, pattern.span), depth + 1);
    }
  }
  Result region(uint32_t id, unsigned depth) {
    const auto &body = syntax.bodies[id];
    for (const auto &statement : body.statements) {
      const auto &expr = syntax.expressions[statement.expression];
      if (expr.binding && syntax.bindings[expr.binding->index].service &&
          statement.kind == Statement::Kind::Let) {
        auto field = service(statement.expression);
        if (field)
          services.emplace(*statement.pattern.binding, *field);
        continue;
      }
      auto firstCall = calls.size();
      auto value = expression(statement.expression, depth + 1);
      if (statement.type)
        types.equal(value.type, annotation(*statement.type), statement.span);
      if (statement.kind == Statement::Kind::Assign)
        types.equal(value.type,
                    binding(*statement.pattern.binding, statement.span),
                    statement.span);
      if (statement.kind == Statement::Kind::Require)
        constrain(value.type, Type{}, statement.span);
      if (statement.kind == Statement::Kind::Expression &&
          !statement.terminated)
        constrain(value.type, Type(T::Unit), statement.span);
      // Authored statements are inference boundaries. A later statement or an
      // enclosing result cannot retroactively supply an earlier let's type.
      if (!finishCalls(firstCall, statement.span))
        return value;
      if (value.stopped) {
        if ((statement.kind == Statement::Kind::Let ||
             statement.kind == Statement::Kind::Assign) &&
            !types.get(value.type, statement.span) && !checker.types.diagnostic)
          fail("source.inference", "stopped binding needs an explicit type",
               statement.span);
        return {types.fresh(statement.span), true};
      }
      if (statement.kind == Statement::Kind::Let) {
        if (!types.get(value.type, statement.span)) {
          if (!checker.types.diagnostic)
            fail("source.inference", "binding needs a type before its next use",
                 statement.span);
          return value;
        }
        bind(statement.pattern, value.type, depth + 1);
      }
    }
    if (body.stopped)
      return {types.fresh(body.span), true};
    if (body.results.empty())
      return {known(Type(T::Unit), body.span)};
    return expression(body.results.front().second, depth + 1);
  }
  void call(uint32_t id, unsigned depth, Result result) {
    const auto &expr = syntax.expressions[id];
    auto child = [&](unsigned i) {
      return expression(expr.children[i], depth + 1).type;
    };
    if (expr.text == "index" && expr.kind == K::Call) {
      constrain(result.type, Type(T::Index), expr.span);
      return;
    }
    if (expr.text == "unpack" && expr.kind == K::Call) {
      if (expr.children.size() != 1) {
        fail("source.call", "unpack requires one value", expr.span);
        return;
      }
      auto base = child(0);
      types.defer([this, base, result, span = expr.span] {
        auto type = types.get(base, span);
        if (!type)
          return false;
        auto fields = checker.types.fields(*type, span);
        if (fields) {
          Type unpacked(fields->empty() ? T::Unit : T::Tuple);
          for (const auto &field : *fields)
            unpacked.arguments.push_back(field.type);
          constrain(result.type,
                    type->kind == T::Associated ? fields->front().type
                                                : unpacked,
                    span);
        }
        return true;
      });
      return;
    }
    auto split = StringRef(expr.text).rsplit("::");
    auto nominal = expr.kind == K::Record
                       ? checker.resolve(decl, expr.text, expr.span, false)
                   : split.second.empty()
                       ? std::nullopt
                       : checker.resolve(decl, split.first, expr.span, false);
    if (expr.kind == K::Record ||
        (nominal && checker.output.declarations[nominal->index].kind ==
                        Declaration::Kind::Variant)) {
      SyntaxType term;
      term.name = expr.kind == K::Record ? expr.text : split.first.str();
      term.arguments = expr.arguments;
      term.span = expr.span;
      auto type = checker.type(decl, term);
      if (!type)
        return;
      constrain(result.type, *type, expr.span);
      std::optional<std::vector<TypeField>> fields;
      if (expr.kind == K::Record)
        fields = checker.types.fields(*type, expr.span);
      else if (auto alternatives =
                   checker.types.alternatives(*type, expr.span)) {
        auto alt = llvm::find_if(*alternatives, [&](const auto &alternative) {
          return alternative.name == split.second;
        });
        if (alt != alternatives->end())
          fields = alt->fields;
      }
      if (!fields || fields->size() != expr.children.size()) {
        if (!checker.types.diagnostic)
          fail("source.call", "constructor arguments differ", expr.span);
        return;
      }
      for (unsigned i = 0; i < expr.children.size(); ++i) {
        auto field = fields->begin() + i;
        if (expr.kind == K::Record)
          field = llvm::find_if(*fields, [&](const auto &field) {
            return field.name == expr.labels[i];
          });
        if (field == fields->end()) {
          fail("source.field", "unknown constructor field", expr.span);
          return;
        }
        constrain(child(i), field->type, expr.span);
      }
      return;
    }
    auto target = owner.callable(expr);
    if (!target)
      return;
    const auto &callee = checker.output.declarations[target->first.index];
    if (callee.kind == Declaration::Kind::Associated) {
      SyntaxType term;
      term.name = expr.text;
      term.arguments = expr.arguments;
      term.span = expr.span;
      auto type = checker.type(decl, term);
      if (!type)
        return;
      constrain(result.type, *type, expr.span);
      auto fields = checker.types.fields(*type, expr.span);
      if (fields && fields->size() == 1 && expr.children.size() == 1)
        constrain(child(0), fields->front().type, expr.span);
      return;
    }
    if (callee.kind != Declaration::Kind::Local &&
        callee.kind != Declaration::Kind::Math &&
        callee.kind != Declaration::Kind::Protocol) {
      fail("source.call", "call target must be a callable", expr.span);
      return;
    }
    types.equal(
        result.type,
        packed(application(id, callee, target->second, depth), expr.span),
        expr.span);
  }
  Result expression(uint32_t id, unsigned depth) {
    if (auto it = expressions.find(id); it != expressions.end())
      return it->second;
    const auto &expr = syntax.expressions[id];
    Result result{types.fresh(expr.span)};
    if (checker.types.diagnostic ||
        depth > checker.work.limits.expressionDepth ||
        !checker.types.charge(1, expr.span)) {
      if (!checker.types.diagnostic)
        fail("source.limit", "expression inference depth exceeded", expr.span);
      return result;
    }
    auto child = [&](unsigned i) {
      return expression(expr.children[i], depth + 1).type;
    };
    switch (expr.kind) {
    case K::Decimal:
      types.requireKinds(result.type, {T::Field, T::Index}, expr.span);
      break;
    case K::Boolean:
      constrain(result.type, Type{}, expr.span);
      break;
    case K::Name:
      if (expr.binding)
        types.equal(result.type, binding(*expr.binding, expr.span), expr.span);
      else
        fail("source.name", "expected a data binding: " + expr.text, expr.span);
      break;
    case K::Projection: {
      auto base = child(0);
      types.defer([this, base, result, id] {
        const auto &expr = syntax.expressions[id];
        auto type = types.get(base, expr.span);
        if (!type)
          return false;
        auto index =
            checker.types.fieldIndex(decl, *type, expr.text, expr.span);
        auto field = index ? checker.types.projectedType(decl, *type, {*index},
                                                         expr.span)
                           : std::nullopt;
        if (field)
          constrain(result.type, *field, expr.span);
        return true;
      });
      break;
    }
    case K::Tuple:
    case K::Array: {
      std::vector<Variable> children;
      for (auto id : expr.children)
        children.push_back(expression(id, depth + 1).type);
      auto kind = expr.kind == K::Array ? T::Array
                  : children.empty()    ? T::Unit
                                        : T::Tuple;
      types.equal(result.type, aggregate(kind, std::move(children), expr.span),
                  expr.span);
      break;
    }
    case K::Add:
    case K::Subtract:
    case K::Equal:
    case K::Multiply: {
      auto left = child(0), right = child(1);
      if (expr.kind == K::Equal)
        constrain(result.type, Type{}, expr.span);
      else
        types.equal(result.type, left, expr.span);
      if (expr.kind != K::Multiply)
        types.equal(left, right, expr.span);
      else {
        types.defer([this, left, right, span = expr.span] {
          auto type = types.get(left, span);
          if (!type) {
            // Numeric expressions cannot be groups, so a scalar multiplier
            // supplies their type even through nested calls and arithmetic.
            auto scalar = types.get(right, span);
            if (!types.allows(left, T::Group) ||
                (scalar && scalar->kind == T::Index)) {
              types.equal(left, right, span);
              return true;
            }
            return false;
          }
          if (type->kind == T::Group) {
            auto scalar = checker.types.associated(*type, "Scalar", span);
            if (scalar)
              constrain(right, *scalar, span);
          } else
            types.equal(left, right, span);
          return true;
        });
      }
      break;
    }
    case K::Block:
      result = region(expr.regions.front(), depth + 1);
      break;
    case K::If:
    case K::Match: {
      auto condition = child(0);
      if (expr.kind == K::If)
        constrain(condition, Type{}, expr.span);
      std::optional<std::vector<Alternative>> alternatives;
      if (expr.kind == K::Match) {
        types.solve(expr.span);
        auto type = types.get(condition, expr.span);
        if (!type) {
          if (!checker.types.diagnostic)
            fail("source.inference", "match needs a known scrutinee type",
                 expr.span);
          break;
        }
        alternatives = checker.types.alternatives(*type, expr.span);
        if (!alternatives)
          break;
      }
      result.stopped = true;
      for (unsigned i = 0; i < expr.regions.size(); ++i) {
        if (alternatives) {
          auto alt = llvm::find_if(*alternatives, [&](const auto &alternative) {
            return alternative.name == expr.labels[i];
          });
          if (alt == alternatives->end() ||
              alt->fields.size() != expr.payloads[i].size()) {
            fail("source.match", "unknown alternative or wrong payload count",
                 expr.span);
            break;
          }
          for (unsigned j = 0; j < alt->fields.size(); ++j)
            bind(expr.payloads[i][j], known(alt->fields[j].type, expr.span),
                 depth + 1);
        }
        auto arm = region(expr.regions[i], depth + 1);
        if (!arm.stopped) {
          result.stopped = false;
          types.equal(result.type, arm.type, expr.span);
        }
      }
      break;
    }
    case K::For:
      // Loop bodies have their own statement scopes and no value result.
      constrain(result.type, Type(T::Unit), expr.span);
      break;
    case K::MethodCall: {
      auto field = service(expr.children.front());
      if (field)
        constrain(result.type, *field, expr.span);
      break;
    }
    case K::Kernel:
    case K::Intrinsic: {
      std::vector<Type> arguments;
      auto signature = expr.kind == K::Kernel
                           ? owner.kernelSignature(expr, arguments)
                           : owner.intrinsicSignature(expr, arguments);
      if (!signature)
        break;
      constrain(result.type, signature->resultType(), expr.span);
      if (expr.children.size() != signature->inputs.size()) {
        fail(expr.kind == K::Kernel ? "source.kernel" : "source.intrinsic",
             "installed input count differs", expr.span);
        break;
      }
      for (unsigned i = 0; i < expr.children.size(); ++i)
        constrain(child(i), signature->inputs[i], expr.span);
      break;
    }
    case K::Record:
    case K::Call:
      call(id, depth, result);
      break;
    case K::FinishIf: {
      constrain(child(0), Type{}, expr.span);
      std::vector<Variable> continuations;
      for (unsigned i = 0; i < expr.labels.size(); ++i) {
        auto port = llvm::find_if(decl.outputs, [&](const auto &port) {
          return port.name == expr.labels[i];
        });
        if (port == decl.outputs.end()) {
          fail("source.completion", "unknown completion output", expr.span);
          break;
        }
        constrain(child(i + 1), port->type, expr.span);
      }
      auto roles = checker.roles(decl, {expr.text}, expr.span);
      if (roles)
        for (const auto &port : decl.outputs)
          if (llvm::is_contained(port.roles, roles->front())) {
            auto caps = checker.types.permissions(port.type, expr.span, &decl);
            if (caps && !caps->copy)
              continuations.push_back(known(port.type, expr.span));
          }
      types.equal(result.type, packed(std::move(continuations), expr.span),
                  expr.span);
      break;
    }
    }
    expressions.emplace(id, result);
    return result;
  }

public:
  explicit ExpressionInference(BodyChecker &owner)
      : owner(owner), checker(owner.checker), decl(owner.decl),
        syntax(owner.syntax), types(checker.types) {}
  std::optional<ExpressionTypes> run(uint32_t id,
                                     std::optional<Type> expected) {
    auto result = expression(id, 1);
    if (expected)
      constrain(result.type, *expected, syntax.expressions[id].span);
    if (!finishCalls(0, syntax.expressions[id].span))
      return {};
    for (const auto &[id, value] : expressions) {
      output.covered.insert(id);
      if (auto type = types.get(value.type, syntax.expressions[id].span))
        output.expressions.emplace(id, std::move(*type));
    }
    if (checker.types.diagnostic)
      return {};
    return std::move(output);
  }
};
std::optional<ExpressionTypes>
BodyChecker::inferExpression(uint32_t id, std::optional<Type> expected) {
  return ExpressionInference(*this).run(id, std::move(expected));
}
BodyChecker::TypeScope::TypeScope(BodyChecker &checker, uint32_t id,
                                  std::optional<Type> expected)
    : checker(checker), outer(checker.inference), valid(true) {
  if (outer && outer->covered.count(id))
    return;
  state = checker.inferExpression(id, std::move(expected));
  valid = state.has_value();
  if (valid)
    checker.inference = &*state;
}
BodyChecker::TypeScope::~TypeScope() { checker.inference = outer; }
std::optional<Type> BodyChecker::inferredType(uint32_t id) const {
  if (inference)
    if (auto it = inference->expressions.find(id);
        it != inference->expressions.end())
      return it->second;
  return {};
}
} // namespace zkc::language::detail
