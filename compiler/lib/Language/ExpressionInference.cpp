#include "Arguments.h"
#include "BodyCheck.h"
#include "CallableConstraints.h"
#include "DataRequirements.h"
#include "OperatorInference.h"
#include "TypeInference.h"
#include "llvm/ADT/STLExtras.h"
#include <cassert>
#include <numeric>
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
  std::unique_ptr<OperatorInference> operators;
  std::map<BindingId, Variable> bindings, domains;
  std::map<uint32_t, Variable> domainExpressions;
  std::map<BindingId, Type> services;
  std::map<uint32_t, Result> expressions;
  std::vector<uint32_t> expressionOrder;
  std::vector<Call> calls;
  ExpressionTypes output;
  std::optional<Body::Mode> scopedMode;
  unsigned scopedDepth = 0;
  struct ScopedEquations {
    ScopedSignature::Mode mode;
    std::vector<Variable> inputs;
    Variable result;
    Effects allowance;
  };
  std::map<uint32_t, ScopedEquations> scopedEquations;
  std::optional<ScopedSignature> scopedSignature(const Expression &expr) {
    if (!expr.binding)
      return {};
    auto found = owner.scoped.find(*expr.binding);
    if (found != owner.scoped.end())
      return owner.body.scopedBindings[found->second].signature;
    return {};
  }
  void scopedArgument(uint32_t id, const ScopedSignature &signature,
                      const TypeInference::Parameters &parameters,
                      unsigned depth) {
    const auto &expr = syntax.expressions[id];
    ScopedEquations equations{
        signature.mode,
        {},
        types.instantiate(signature.result, parameters, expr.span),
        signature.allowance};
    for (const auto &input : signature.inputs)
      equations.inputs.push_back(
          types.instantiate(input, parameters, expr.span));
    if (expr.kind == K::Name) {
      auto actual = scopedSignature(expr);
      if (!actual || actual->mode != signature.mode ||
          (actual->allowance.mayStop && !signature.allowance.mayStop) ||
          (actual->allowance.opaque && !signature.allowance.opaque) ||
          actual->inputs.size() != signature.inputs.size()) {
        fail("source.scoped", "scoped forwarding contract differs", expr.span);
        return;
      }
      for (unsigned i = 0; i < actual->inputs.size(); ++i)
        constrain(equations.inputs[i], actual->inputs[i], expr.span);
      constrain(equations.result, actual->result, expr.span);
    } else if (expr.kind == K::Lambda) {
      if (expr.payloads.front().size() != equations.inputs.size()) {
        fail("source.scoped", "lambda binder count differs from scoped inputs",
             expr.span);
        return;
      }
      for (unsigned i = 0; i < equations.inputs.size(); ++i)
        bind(expr.payloads.front()[i], equations.inputs[i], depth + 1);
      auto previous = scopedMode;
      scopedMode = signature.mode == ScopedSignature::Mode::Math
                       ? Body::Mode::Math
                       : Body::Mode::Local;
      ++scopedDepth;
      auto result = region(expr.regions.front(), depth + 1);
      --scopedDepth;
      if (!result.stopped)
        types.equal(result.type, equations.result, expr.span);
      scopedMode = previous;
    } else {
      fail("source.scoped", "expected a lambda or scoped parameter", expr.span);
      return;
    }
    scopedEquations.emplace(id, std::move(equations));
  }
  Variable domainArgument(uint32_t id, unsigned depth) {
    const auto &expr = syntax.expressions[id];
    if (depth > checker.work.limits.expressionDepth ||
        !checker.types.charge(1, expr.span)) {
      fail("source.limit", "domain inference depth exceeded", expr.span);
      return types.fresh(expr.span);
    }
    if (auto found = domainExpressions.find(id);
        found != domainExpressions.end())
      return found->second;
    Variable result = types.fresh(expr.span);
    if (expr.kind == K::DomainProduct) {
      if (expr.children.size() != 2) {
        fail("source.finite-domain", "domain product requires two operands",
             expr.span);
        return result;
      }
      auto left = domainArgument(expr.children[0], depth + 1);
      auto right = domainArgument(expr.children[1], depth + 1);
      types.equal(result, types.shape(Type(T::Tuple), {left, right}, expr.span),
                  expr.span);
      domainExpressions.emplace(id, result);
      return result;
    }
    bool collection = false;
    if (expr.kind == K::Name && expr.binding) {
      if (auto found = domains.find(*expr.binding); found != domains.end())
        types.equal(result, found->second, expr.span);
      else if (auto found = owner.domains.find(*expr.binding);
               found != owner.domains.end())
        constrain(result, owner.body.domainBindings[found->second].item,
                  expr.span);
      else
        collection = true;
    } else if (expr.kind == K::Call && !expr.binding && !expr.roles) {
      auto target = owner.callable(expr);
      if (!target)
        return result;
      const auto &callee =
          checker.output.declarations[target->declaration.index];
      if (callee.kind != Declaration::Kind::DomainFunction) {
        collection = true;
      } else {
        output.callees.emplace(id, *target);
        contexts.emplace(
            id, CallContext{scopedMode.value_or(owner.body.mode), scopedDepth});
        auto outputs = application(id, callee, target->module, depth);
        if (outputs.size() == 1)
          types.equal(result, outputs.front(), expr.span);
      }
    } else
      collection = true;
    if (collection) {
      output.collectionDomains.insert(id);
      auto input = expression(id, depth + 1).type;
      types.defer([this, input, result, span = expr.span] {
        auto structure = types.structure(input, span);
        if (!structure)
          return false;
        const auto &head = structure->head;
        const auto &arguments = structure->arguments;
        auto kind = collectionElementKind(head, arguments.size());
        if ((head.kind == T::Array && arguments.size() == 2) ||
            kind == CollectionElementKind::Parameter) {
          types.equal(result, arguments.front(), span);
          return true;
        }
        if (kind == CollectionElementKind::Index) {
          constrain(result, Type(T::Index), span);
          return true;
        }
        return fail("source.finite-domain",
                    "expected a finite domain or a collection; matrices "
                    "require an explicit view",
                    span);
      });
    }
    domainExpressions.emplace(id, result);
    return result;
  }
  struct CallContext {
    Body::Mode mode;
    unsigned scopedDepth;
  };
  std::map<uint32_t, CallContext> contexts;
  bool accountCall(uint32_t id, const Declaration &callee,
                   bool mapped = false) {
    if (callee.kind == Declaration::Kind::EntryFunction ||
        (callee.generated && callee.generated->operation)) {
      if (owner.body.stage != Body::Stage::Host || contexts.at(id).scopedDepth)
        return fail("source.stage", "Host calls require an entry function",
                    syntax.expressions[id].span);
      if (callee.generated)
        return true;
    }
    if (callee.abstract)
      return true;
    const auto &context = contexts.at(id);
    const auto &primitive = checker.sources[callee.id.index]->primitive;
    unsigned edge =
        !mapped && primitive &&
                primitiveCallIsInline(context.mode, callee.kind, *primitive)
            ? 0
            : 1;
    unsigned extra = context.scopedDepth;
    if (!checker.body(callee.id, owner.callDepth + extra + edge))
      return false;
    unsigned height = checker.bodyHeights[callee.id.index] + edge;
    checker.bodyHeights[decl.id.index] =
        std::max(checker.bodyHeights[decl.id.index], height + extra);
    return true;
  }

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
      auto value = known(it->second.type,
                         it->second.value
                             ? owner.body.values[it->second.value->index].span
                             : span);
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
  bool finishCalls(unsigned begin, unsigned firstExpression, Span span) {
    std::optional<Diagnostic> incompleteCall;
    auto selected = operators->solve(span, [&] {
      bool complete = true;
      for (unsigned i = begin; i < calls.size(); ++i) {
        const auto &call = calls[i];
        const auto &callee = checker.output.declarations[call.target.index];
        CallableConstraints constraints{
            output.callees.at(call.expression), call.parameters, {}, {}};
        auto arguments =
            callableArguments(types, checker.types, callee, constraints, span);
        complete &= arguments.has_value();
        if (!arguments && !checker.types.diagnostic && !incompleteCall) {
          for (const auto &parameter : callee.parameters)
            if (!types.get(call.parameters.at(parameter.atom), span)) {
              checker.types.fail(
                  "source.inference",
                  "cannot infer static argument '" + parameter.name + "' of " +
                      callee.qualifiedName +
                      "; supply an explicit static argument or a result type "
                      "annotation",
                  syntax.expressions[call.expression].span, {parameter.span});
              incompleteCall = std::move(checker.types.diagnostic);
              checker.types.diagnostic.reset();
              break;
            }
        }
      }
      for (unsigned i = firstExpression; i < expressionOrder.size(); ++i) {
        auto id = expressionOrder[i];
        const auto &value = expressions.at(id);
        if (!value.stopped)
          complete &=
              types.get(value.type, syntax.expressions[id].span).has_value();
      }
      return complete;
    });
    if (!selected) {
      if (incompleteCall && checker.types.diagnostic &&
          checker.types.diagnostic->code == "source.inference")
        checker.types.diagnostic = std::move(incompleteCall);
      return false;
    }
    for (auto &[id, selection] : *selected) {
      auto &signature = selection.constraints;
      auto &callee =
          checker.output.declarations[signature.target.declaration.index];
      output.callees.emplace(id, signature.target);
      output.operators.at(id).binding = selection.binding;
      std::vector<unsigned> inputs(signature.inputs.size());
      std::iota(inputs.begin(), inputs.end(), 0);
      output.inputs.emplace(id, std::move(inputs));
      // Complete only the selected target. The ordinary body checker owns
      // cycles, permissions, requirements and execution modes after selection.
      if (!accountCall(id, callee))
        return false;
      calls.push_back({id, callee.id, std::move(signature.parameters)});
    }
    for (unsigned i = begin; i < calls.size(); ++i) {
      auto &call = calls[i];
      if (call.checked)
        continue;
      const auto &callee = checker.output.declarations[call.target.index];
      auto callSpan = syntax.expressions[call.expression].span;
      Substitution substitution;
      for (const auto &[name, variable] : call.parameters) {
        auto value = types.get(variable, callSpan);
        if (!value) {
          if (checker.types.diagnostic)
            return false;
          auto parameter = llvm::find_if(
              callee.parameters,
              [atom = name](const Parameter &p) { return p.atom == atom; });
          auto parameterName =
              parameter != callee.parameters.end() ? parameter->name : name;
          auto parameterSpan = parameter != callee.parameters.end()
                                   ? parameter->span
                                   : callee.span;
          return checker.types.fail("source.inference",
                                    "cannot infer static argument '" +
                                        parameterName + "' of " +
                                        callee.qualifiedName +
                                        "; supply an explicit static argument "
                                        "by name or use _ for other slots, "
                                        "or a result type annotation",
                                    callSpan, {parameterSpan});
        }
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
  /// `rows` lifts the marked data inputs and every result of a pointwise map
  /// to native vectors of the helper's scalar types.
  std::vector<Variable> application(uint32_t id, const Declaration &callee,
                                    std::optional<Type> module, unsigned depth,
                                    const std::vector<bool> &rows = {},
                                    ArrayRef<std::optional<Type>> bound = {}) {
    const auto &expr = syntax.expressions[id];
    if (!accountCall(id, callee, expr.kind == K::Map))
      return {};
    auto constraints = instantiateCallable(types, checker.types, callee,
                                           {callee.id, module}, expr.span);
    if (checker.types.diagnostic)
      return {};
    const auto &parameters = constraints.parameters;
    for (unsigned i = 0; i < bound.size(); ++i)
      if (bound[i])
        types.equal(parameters.at(callee.parameters[i].atom),
                    known(*bound[i], expr.span), expr.span);
    unsigned inherited = 0;
    if (module && callee.parent)
      inherited =
          checker.output.declarations[callee.parent->index].parameters.size();
    auto staticBinding =
        bindArguments(checker.types,
                      argumentNames<Parameter>(
                          ArrayRef(callee.parameters).drop_front(inherited)),
                      expr.arguments.size(), expr.staticLabels, false,
                      expr.span, "source.generic");
    if (!staticBinding)
      return {};
    for (unsigned i = 0; i < expr.arguments.size(); ++i)
      if (expr.arguments[i].kind != SyntaxType::Kind::Hole)
        types.equal(
            parameters.at(
                callee.parameters[inherited + (*staticBinding)[i]].atom),
            annotation(expr.arguments[i]), expr.span);
    // Reuse enclosing binders only for omitted slots. Written arguments and
    // explicit holes retain their normal inference behavior.
    auto enclosing = checker.enclosingParameters(decl, callee, expr.span);
    if (!enclosing)
      return {};
    std::vector<bool> written(callee.parameters.size(), false);
    for (auto position : *staticBinding)
      written[inherited + position] = true;
    for (unsigned i = inherited; i < callee.parameters.size(); ++i)
      if ((*enclosing)[i] && !written[i]) {
        const auto &parameter = callee.parameters[i];
        types.equal(parameters.at(parameter.atom),
                    known(parameterType(parameter), expr.span), expr.span);
      }
    auto binding =
        bindArguments(checker.types, inputNames(callee), expr.children.size(),
                      expr.callLabels, true, expr.span, "source.call");
    if (!binding)
      return {};
    output.inputs.emplace(id, *binding);
    calls.push_back({id, callee.id, parameters});
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      auto slot = !callee.inputOrder.empty()
                      ? callee.inputOrder[(*binding)[i]]
                      : Declaration::InputSlot{
                            Declaration::InputSlot::Kind::Data, (*binding)[i]};
      if (slot.kind == Declaration::InputSlot::Kind::Service) {
        auto field = service(expr.children[i]);
        if (field)
          types.equal(types.instantiate(callee.services[slot.index].field,
                                        parameters, expr.span,
                                        callee.services[slot.index].span),
                      known(*field, expr.span), expr.span);
      } else if (slot.kind == Declaration::InputSlot::Kind::Domain) {
        types.equal(types.instantiate(callee.domainInputs[slot.index].item,
                                      parameters, expr.span),
                    domainArgument(expr.children[i], depth + 1), expr.span);
      } else if (slot.kind == Declaration::InputSlot::Kind::Data) {
        auto parameter = constraints.inputs[slot.index];
        auto argument = expression(expr.children[i], depth + 1);
        if (!rows.empty()) {
          // Report a missing or extra `each` before unifying the two modes.
          if (!types.allows(argument.type, rows[i] ? T::Builtin : T::Field)) {
            fail("source.map",
                 rows[i] ? "an each argument requires a native vector"
                         : "an argument without each requires a scalar field",
                 expr.span);
            return {};
          }
          if (rows[i])
            parameter = vectorOf(parameter, expr.span);
        }
        types.equal(parameter, argument.type, expr.span);
      }
    }
    for (unsigned i = 0; i < expr.children.size(); ++i)
      if (!callee.inputOrder.empty()) {
        auto slot = callee.inputOrder[(*binding)[i]];
        if (slot.kind == Declaration::InputSlot::Kind::Scoped)
          scopedArgument(expr.children[i],
                         callee.scopedInputs[slot.index].signature, parameters,
                         depth + 1);
      }
    std::vector<Variable> results;
    if (callee.domainResult)
      results.push_back(
          types.instantiate(*callee.domainResult, parameters, expr.span));
    for (auto result : constraints.outputs)
      results.push_back(rows.empty() ? result : vectorOf(result, expr.span));
    return results;
  }
  Variable vectorOf(Variable element, Span span) {
    return types.shape(Type(T::Builtin, "vector"), {element}, span);
  }
  void map(uint32_t id, unsigned depth, Result result) {
    const auto &expr = syntax.expressions[id];
    auto target = owner.callable(expr);
    if (!target)
      return;
    output.callees.emplace(id, *target);
    const auto &callee = checker.output.declarations[target->declaration.index];
    if (callee.kind != Declaration::Kind::Math || callee.abstract ||
        target->module) {
      fail("source.map", "map selects a static, defined math fn", expr.span);
      return;
    }
    if (!llvm::is_contained(expr.each, true)) {
      fail("source.map", "map requires at least one each argument", expr.span);
      return;
    }
    types.equal(
        result.type,
        packed(application(id, callee, {}, depth, expr.each), expr.span),
        expr.span);
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
      if (statement.kind == Statement::Kind::Let && statement.pattern.binding &&
          syntax.bindings[statement.pattern.binding->index].domain) {
        auto firstCall = calls.size();
        auto firstExpression = expressionOrder.size();
        auto item = domainArgument(statement.expression, depth + 1);
        if (!finishCalls(firstCall, firstExpression, statement.span))
          return {item};
        if (!types.get(item, statement.span))
          fail("source.inference",
               "domain item needs a type before its next use", statement.span);
        domains.emplace(*statement.pattern.binding, item);
        continue;
      }
      auto firstCall = calls.size();
      auto firstExpression = expressionOrder.size();
      auto enclosingOperators = std::move(operators);
      operators = std::make_unique<OperatorInference>(
          types, checker.types, checker.output.declarations);
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
      if (!finishCalls(firstCall, firstExpression, statement.span))
        return value;
      operators = std::move(enclosingOperators);
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
    if (expr.binding && expr.kind == K::Call) {
      auto signature = scopedSignature(expr);
      if (!signature || !expr.arguments.empty() || !expr.callLabels.empty() ||
          expr.roles || expr.children.size() != signature->inputs.size()) {
        fail("source.scoped", "expected a positional scoped invocation",
             expr.span);
        return;
      }
      for (unsigned i = 0; i < signature->inputs.size(); ++i)
        constrain(child(i), signature->inputs[i], expr.span);
      constrain(result.type, signature->result, expr.span);
      return;
    }
    if (expr.text == "index" && expr.kind == K::Call) {
      constrain(result.type, Type(T::Index), expr.span);
      return;
    }
    if (expr.text == "unpack" && expr.kind == K::Call) {
      if (expr.children.size() != 1 || !expr.callLabels.empty() ||
          !expr.arguments.empty()) {
        fail("source.call", "unpack requires one positional value", expr.span);
        return;
      }
      auto base = child(0);
      types.defer([this, base, result, span = expr.span] {
        auto type = types.get(base, span);
        if (!type)
          return false;
        auto fields = checker.types.structuralFields(*type, span);
        if (fields) {
          Type unpacked(fields->empty() ? T::Unit : T::Tuple);
          for (const auto &field : *fields)
            unpacked.arguments.push_back(field.type);
          constrain(result.type,
                    type->kind == T::Associated ? fields->front().type
                                                : unpacked,
                    span);
        }
        return fields.has_value() || checker.types.diagnostic.has_value();
      });
      return;
    }
    std::optional<ExpressionTypes::Callable> target;
    if (expr.kind != K::Record) {
      target = owner.callable(expr);
      if (!target)
        return;
      output.callees.emplace(id, *target);
      auto kind = checker.output.declarations[target->declaration.index].kind;
      if (!expr.callLabels.empty() && (kind == Declaration::Kind::Variant ||
                                       kind == Declaration::Kind::Associated)) {
        fail("source.call", "constructor payloads require positional values",
             expr.span);
        return;
      }
    }
    auto split = StringRef(expr.text).rsplit("::");
    if (expr.kind == K::Record ||
        checker.output.declarations[target->declaration.index].kind ==
            Declaration::Kind::Variant) {
      SyntaxType term;
      term.name = expr.kind == K::Record ? expr.text : split.first.str();
      term.arguments = expr.arguments;
      term.labels = expr.staticLabels;
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
    const auto &callee = checker.output.declarations[target->declaration.index];
    if (callee.kind == Declaration::Kind::Associated) {
      SyntaxType term;
      term.name = expr.text;
      term.arguments = expr.arguments;
      term.labels = expr.staticLabels;
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
        callee.kind != Declaration::Kind::EntryFunction &&
        callee.kind != Declaration::Kind::Math &&
        callee.kind != Declaration::Kind::Protocol) {
      fail("source.call", "call target must be a callable", expr.span);
      return;
    }
    types.equal(
        result.type,
        packed(application(id, callee, target->module, depth), expr.span),
        expr.span);
  }
  Result expression(uint32_t id, unsigned depth) {
    if (auto it = expressions.find(id); it != expressions.end())
      return it->second;
    const auto &expr = syntax.expressions[id];
    contexts.emplace(
        id, CallContext{scopedMode.value_or(owner.body.mode), scopedDepth});
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
    case K::Not:
      llvm_unreachable("Boolean negation must be elaborated before inference");
    case K::And:
    case K::Or:
      constrain(result.type, Type{}, expr.span);
      constrain(child(0), Type{}, expr.span);
      constrain(child(1), Type{}, expr.span);
      break;
    case K::DomainProduct:
      fail("source.finite-domain",
           "domain products require a scoped domain argument", expr.span);
      break;
    case K::Lambda:
      fail("source.scoped",
           "scoped computations cannot escape an argument position", expr.span);
      break;
    case K::Name:
      if (expr.binding && syntax.bindings[expr.binding->index].scoped)
        fail("source.scoped", "scoped parameters have no runtime value",
             expr.span);
      else if (expr.binding)
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
        auto field = checker.types.projectionType(*type, expr.text, expr.span);
        if (field)
          constrain(result.type, *field, expr.span);
        return field.has_value() || checker.types.diagnostic.has_value();
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
    case K::Subscript:
    case K::NotationCall: {
      if (expr.kind == K::Subscript) {
        auto receiver = child(0);
        auto structure = types.structure(receiver, expr.span);
        if (!structure) {
          if (!operators->propagate(expr.span))
            break;
          structure = types.structure(receiver, expr.span);
        }
        if (!structure) {
          auto visible = checker.operatorCandidates(decl, syntax, id);
          if (!visible)
            break;
          if (visible->empty() && staticSubscriptIndex(syntax, expr)) {
            // Preserve static projection constraints through ordinary overload
            // search. This adds equations only, never choices during rollback.
            constrain(child(1), Type(T::Index), expr.span);
            types.defer([this, receiver, result, id] {
              const auto &expr = syntax.expressions[id];
              auto type = types.get(receiver, expr.span);
              if (!type)
                return false;
              if (type->kind != T::Array) {
                fail("source.index",
                     "indexing requires a visible indexing [] binding for this "
                     "receiver",
                     expr.span);
                return true;
              }
              auto field = checker.types.projectionType(
                  *type, *staticSubscriptIndex(syntax, expr), expr.span);
              if (field)
                constrain(result.type, *field, expr.span);
              return field.has_value() || checker.types.diagnostic.has_value();
            });
          } else if (visible->empty())
            fail("source.index",
                 "indexing requires a visible indexing [] binding for this "
                 "receiver",
                 expr.span);
          else if (!checker.types.diagnostic)
            fail("source.inference",
                 "indexing needs a known receiver type constructor; add a type "
                 "annotation",
                 expr.span);
          break;
        }
        if (structure->head.kind == T::Array) {
          if (!staticSubscriptIndex(syntax, expr)) {
            fail("source.index", "fixed arrays require a static numeric index",
                 expr.span);
            break;
          }
          constrain(child(1), Type(T::Index), expr.span);
          types.equal(result.type, structure->arguments.front(), expr.span);
          break;
        }
      }
      if (expr.kind == K::Subscript &&
          expr.children.size() > checker.work.limits.notationHoles) {
        fail("source.limit", "notation hole limit exceeded", expr.span);
        break;
      }
      auto visible = checker.operatorCandidates(decl, syntax, id);
      if (!visible)
        break;
      if (expr.kind == K::Subscript && visible->empty()) {
        fail(
            "source.index",
            "indexing requires a visible indexing [] binding for this receiver",
            expr.span);
        break;
      }
      if (expr.notation->position == NotationDescriptor::Position::Reduction) {
        if (visible->size() != 1) {
          fail("source.notation-ambiguous",
               "finite binder requires one visible reduction binding; select "
               "an import or rebind it locally",
               expr.span);
          break;
        }
        const auto &binding = visible->front();
        if (expr.filteredReduction && !binding.filtered) {
          fail("source.reduction-target",
               "this reduction binding has no filtered companion", expr.span);
          break;
        }
        auto target =
            expr.filteredReduction ? binding.filtered->target : binding.target;
        const auto &arguments = expr.filteredReduction
                                    ? binding.filtered->arguments
                                    : binding.arguments;
        output.operators.emplace(
            id, ExpressionTypes::Operator{
                    {operatorBindingKey(binding, checker.output.declarations)},
                    binding.span});
        output.callees.emplace(id, target);
        const auto &callee =
            checker.output.declarations[target.declaration.index];
        types.equal(
            result.type,
            packed(application(id, callee, target.module, depth, {}, arguments),
                   expr.span),
            expr.span);
        break;
      }
      std::vector<Variable> inputs;
      for (unsigned i = 0; i < expr.children.size(); ++i)
        inputs.push_back(child(i));
      std::vector<OperatorInference::Candidate> candidates;
      ExpressionTypes::Operator witness;
      for (auto &binding : *visible) {
        witness.family.push_back(
            operatorBindingKey(binding, checker.output.declarations));
        candidates.push_back(
            {binding.target, std::move(binding.arguments), binding.span});
      }
      output.operators.emplace(id, std::move(witness));
      operators->add(id, expr.span, std::move(inputs), result.type,
                     std::move(candidates));
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
        if (!operators->propagate(expr.span))
          break;
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
    case K::OracleSend: {
      auto kind = checker.type(decl, expr.arguments.front());
      if (!kind)
        break;
      if (kind->kind != T::OracleKind) {
        fail("source.oracle-kind", "oracle delivery requires an oracle kind",
             expr.span);
        break;
      }
      auto data = checker.types.associated(*kind, "Data", expr.span);
      if (!data)
        break;
      constrain(child(0), *data, expr.span);
      if (expr.children.size() == 2)
        constrain(child(1), Type(T::Index), expr.span);
      Type handle(T::Oracle);
      handle.arguments = {*kind};
      constrain(result.type, handle, expr.span);
      break;
    }
    case K::OracleQuery:
    case K::OracleContents:
    case K::OracleRows:
    case K::OracleForgetRows: {
      auto input = child(0);
      auto position =
          expr.kind == K::OracleQuery ? std::optional(child(1)) : std::nullopt;
      auto output = result.type;
      auto action = expr.kind;
      auto span = expr.span;
      types.defer([this, input, position, output, action, span] {
        auto handle = types.get(input, span);
        if (!handle)
          return false;
        if (handle->kind != T::Oracle || handle->arguments.size() != 1) {
          fail("source.oracle-action",
               "oracle operation requires a logical handle", span);
          return true;
        }
        auto kind = handle->arguments.front();
        if (position) {
          auto query = checker.types.associated(kind, "Query", span);
          if (query)
            constrain(*position, *query, span);
        }
        if (action == K::OracleRows)
          constrain(output, Type(T::Index), span);
        else if (action == K::OracleForgetRows) {
          if (kind.arguments.size() != 2) {
            fail("source.oracle-shape",
                 "forget_rows requires an exact sized kind", span);
            return true;
          }
          kind.arguments.pop_back();
          Type result(T::Oracle);
          result.arguments = {kind};
          constrain(output, result, span);
        } else {
          auto value = checker.types.associated(
              kind, position ? "Answer" : "Data", span);
          if (value)
            constrain(output, *value, span);
        }
        return true;
      });
      break;
    }
    case K::MethodCall: {
      auto field = service(expr.children.front());
      if (field)
        constrain(result.type, expr.text == "index" ? Type(T::Index) : *field,
                  expr.span);
      break;
    }
    case K::Kernel:
    case K::Intrinsic: {
      std::vector<Type> arguments;
      std::vector<std::string> parameters;
      std::vector<AssetReference> references;
      auto signature =
          expr.kind == K::Kernel
              ? owner.kernelSignature(expr, arguments, parameters, references)
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
    case K::Map:
      map(id, depth, result);
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
          if (llvm::is_contained(port.roles, roles->front()))
            continuations.push_back(known(port.type, expr.span));
      types.equal(result.type, packed(std::move(continuations), expr.span),
                  expr.span);
      break;
    }
    }
    expressions.emplace(id, result);
    expressionOrder.push_back(id);
    return result;
  }

public:
  explicit ExpressionInference(BodyChecker &owner)
      : owner(owner), checker(owner.checker), decl(owner.decl),
        syntax(owner.syntax), types(checker.types),
        operators(std::make_unique<OperatorInference>(
            types, checker.types, checker.output.declarations)) {}
  std::optional<ExpressionTypes> run(uint32_t id, std::optional<Type> expected,
                                     bool domain) {
    auto result = domain ? Result{domainArgument(id, 1)} : expression(id, 1);
    if (expected)
      constrain(result.type, *expected, syntax.expressions[id].span);
    if (!finishCalls(0, 0, syntax.expressions[id].span))
      return {};
    for (const auto &[id, value] : expressions) {
      output.covered.insert(id);
      if (auto type = types.get(value.type, syntax.expressions[id].span))
        output.expressions.emplace(id, std::move(*type));
    }
    for (const auto &[id, item] : domainExpressions) {
      output.covered.insert(id);
      auto type = types.get(item, syntax.expressions[id].span);
      if (!type) {
        if (!checker.types.diagnostic)
          fail("source.inference", "cannot infer finite domain item",
               syntax.expressions[id].span);
        return {};
      }
      output.domainItems.emplace(id, *type);
    }
    for (const auto &[id, equations] : scopedEquations) {
      ScopedSignature signature{equations.mode, {}, {}, equations.allowance};
      for (auto input : equations.inputs) {
        auto type = types.get(input, syntax.expressions[id].span);
        if (!type)
          return {};
        signature.inputs.push_back(*type);
      }
      auto result = types.get(equations.result, syntax.expressions[id].span);
      if (!result)
        return {};
      signature.result = *result;
      output.scopedSignatures.emplace(id, std::move(signature));
    }
    if (checker.types.diagnostic)
      return {};
    return std::move(output);
  }
};
std::optional<ExpressionTypes>
BodyChecker::inferExpression(uint32_t id, std::optional<Type> expected,
                             bool domain) {
  assert(syntax.elaborated && "inference requires elaborated source");
  return ExpressionInference(*this).run(id, std::move(expected), domain);
}
BodyChecker::TypeScope::TypeScope(BodyChecker &checker, uint32_t id,
                                  std::optional<Type> expected, bool domain)
    : checker(checker), outer(checker.inference), valid(true) {
  if (outer && outer->covered.count(id))
    return;
  state = checker.inferExpression(id, std::move(expected), domain);
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
