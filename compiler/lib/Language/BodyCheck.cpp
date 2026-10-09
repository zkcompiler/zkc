#include "BodyCheck.h"
#include "zkc/Contracts/Kernels.h"
#include <algorithm>
#include <numeric>
using namespace llvm;
namespace zkc::language::detail {
bool BodyChecker::fail(StringRef code, const Twine &message, Span span) {
  return checker.types.fail(code, message, span);
}

BodyChecker::BodyChecker(Checker &checker, Declaration &decl,
                         const SyntaxDeclaration &syntax, Body &body,
                         unsigned depth)
    : checker(checker), decl(decl), syntax(syntax), body(body),
      callDepth(depth) {}
bool BodyChecker::active(ArrayRef<unsigned> roles, Span span) {
  auto available = allRoles();
  return std::includes(available.begin(), available.end(), roles.begin(),
                       roles.end()) ||
         fail("source.roles",
              "action uses a participant outside the active roster", span);
}
std::vector<unsigned> BodyChecker::allRoles() const {
  if (activeRoles)
    return *activeRoles;
  std::vector<unsigned> result(decl.roles.size());
  std::iota(result.begin(), result.end(), 0);
  return result;
}
bool BodyChecker::data(const Type &type, Span span) {
  return checker.types.mathematicalData(type, span, &decl);
}
bool BodyChecker::addService(BindingId id, const ServicePort &port) {
  if (!protocol() || !checker.types.chargeType(port.field, port.span))
    return false;
  services.emplace(id, ServiceId{uint32_t(body.services.size())});
  body.services.push_back(port);
  return true;
}
std::optional<ServiceId> BodyChecker::service(const Expression &expr) {
  if (expr.kind != Expression::Kind::Name || !expr.binding) {
    fail("source.service", "service reference must name a managed binding",
         expr.span);
    return {};
  }
  auto found = services.find(*expr.binding);
  if (found == services.end()) {
    fail("source.service", "unknown managed service: " + expr.text, expr.span);
    return {};
  }
  return found->second;
}
std::optional<ValueId> BodyChecker::input(const Type &type,
                                          std::vector<unsigned> components,
                                          Span span) {
  if ((!math() && !checker.types.executableType(type, span)) ||
      !checker.types.chargeType(type, span))
    return {};
  ValueId value{uint32_t(body.values.size())};
  body.values.push_back({type, std::move(components), span});
  uses.emplace_back();
  ++body.inputs;
  return value;
}
bool BodyChecker::addInput(BindingId id, const Type &type,
                           std::vector<unsigned> components, Span span) {
  auto value = input(type, components, span);
  if (!value)
    return false;
  bindings.emplace(id, BindingState{type, std::move(components), *value, {}});
  return true;
}
std::optional<ValueId> BodyChecker::emit(decltype(Operation::action) action,
                                         const Type &type,
                                         Components components, Span span) {
  auto ids = emitResults(
      std::move(action),
      {{type,
        components.owners.empty() ? components.roles : std::vector<unsigned>{},
        span}},
      span);
  if (ids && placement) {
    if (!placement->form(components, span))
      return {};
    placement->values[ids->front().index] = std::move(components);
  }
  return ids ? std::optional<ValueId>(ids->front()) : std::nullopt;
}
std::optional<std::vector<ValueId>>
BodyChecker::emitResults(decltype(Operation::action) action,
                         std::vector<Value> results, Span span) {
  if (!checker.types.accept(checker.work.count(checker.work.operations,
                                               checker.work.limits.operations,
                                               "operation count", span)))
    return {};
  for (const auto &value : results) {
    if (!math() && !checker.types.executableType(value.type, span))
      return {};
    if (!checker.types.chargeType(value.type, span) ||
        !checker.types.charge(value.components.size() + 1, span))
      return {};
    if (protocol() && !placement && value.components.size() > 1) {
      auto caps = checker.types.permissions(value.type, span, &decl);
      if (!caps || !caps->share) {
        if (!checker.types.diagnostic)
          fail("source.permission",
               "multiple participant components require Share", span);
        return {};
      }
    }
  }
  std::vector<ValueId> ids;
  for (auto &value : results) {
    ids.push_back(ValueId{uint32_t(body.values.size())});
    if (placement)
      placement->values.emplace(ids.back().index, Components(value.components));
    body.values.push_back(std::move(value));
    uses.emplace_back();
  }
  body.operations.push_back({std::move(action), ids, span, statement});
  return ids;
}
std::optional<Components> BodyChecker::combine(ArrayRef<ValueId> args,
                                               Span span) {
  if (placement) {
    std::vector<Components> inputs;
    for (auto id : args)
      inputs.push_back(components(id));
    auto result = placement->intersect(inputs, span);
    if (result && !placement->form(*result, span))
      return {};
    return result;
  }
  std::vector<unsigned> result =
      math() || local() ? std::vector<unsigned>{} : allRoles();
  for (auto id : args) {
    auto &next = body.values[id.index].components;
    if (!checker.types.charge(result.size() + next.size() + 1, span))
      return {};
    std::vector<unsigned> out;
    if (math())
      std::set_union(result.begin(), result.end(), next.begin(), next.end(),
                     std::back_inserter(out));
    else if (protocol())
      std::set_intersection(result.begin(), result.end(), next.begin(),
                            next.end(), std::back_inserter(out));
    result = std::move(out);
  }
  if (protocol() && result.empty()) {
    fail("source.roles", "operation has no common participant", span);
    return {};
  }
  if (math() && !result.empty())
    body.formationRequirements.push_back(result);
  return Components(std::move(result));
}
bool BodyChecker::restricted(const Type &type) {
  if (type.kind == Type::Kind::Associated || type.kind == Type::Kind::Parameter)
    return true;
  auto *d = checker.types.typeDeclaration(type);
  return d && d->permissions.has_value();
}
std::optional<Type> BodyChecker::projected(Type type, ArrayRef<unsigned> path,
                                           Span span) {
  return checker.types.projectedType(decl, std::move(type), path, span);
}
bool BodyChecker::statements(const SyntaxBody &source) {
  for (const auto &s : source.statements) {
    if (body.stopped)
      return fail("source.unreachable", "statement follows a guaranteed stop",
                  s.span);
    StatementPlacement inference(*this);
    const auto &expr = syntax.expressions[s.expression];
    if (s.kind == Statement::Kind::Let && expr.kind == Expression::Kind::Name &&
        expr.binding && syntax.bindings[expr.binding->index].service) {
      auto root = service(expr);
      if (!root)
        return false;
      services.emplace(*s.pattern.binding, *root);
      ++statement;
      continue;
    }
    if (expr.kind == Expression::Kind::FinishIf) {
      auto results = complete(s);
      if (!results || !inference.commit() || !bindResults(s, *results))
        return false;
      ++statement;
      continue;
    }
    if (expr.kind == Expression::Kind::Call) {
      auto target = checker.resolve(decl, expr.text, expr.span, false);
      if (checker.types.diagnostic)
        return false;
      if (target && checker.output.declarations[target->index].kind ==
                        Declaration::Kind::Protocol) {
        if (s.exchange || (s.kind != Statement::Kind::Let &&
                           s.kind != Statement::Kind::Assign &&
                           s.kind != Statement::Kind::Expression))
          return fail("source.mode",
                      "protocol application requires a complete statement",
                      s.span);
        auto results = application(expr);
        if (!results || !inference.commit() || !bindResults(s, *results))
          return false;
        ++statement;
        continue;
      }
    }
    std::optional<Type> expected;
    std::optional<std::vector<unsigned>> selected;
    if (s.type) {
      expected = checker.type(decl, *s.type);
      if (!expected)
        return false;
    }
    if (s.roles) {
      selected = checker.roles(decl, *s.roles, s.span);
      if (!selected || !active(*selected, s.span))
        return false;
    }
    if (s.kind == Statement::Kind::Assign) {
      auto found = bindings.find(*s.pattern.binding);
      if (found == bindings.end())
        return fail("source.assignment",
                    "assignment target is not in this region", s.span);
      expected = found->second.type;
      selected = found->second.roles;
    }
    std::optional<unsigned> requireOwner;
    if (s.kind == Statement::Kind::Require && s.owner) {
      auto roles = checker.roles(decl, {*s.owner}, s.span);
      if (!roles || !active(*roles, s.span))
        return false;
      requireOwner = roles->front();
    }
    if (s.kind == Statement::Kind::Require)
      expected = Type{};
    if (s.kind == Statement::Kind::Expression && !s.terminated)
      expected = Type(Type::Kind::Unit);
    auto value = expression(s.expression, expected, 1,
                            s.kind != Statement::Kind::Let &&
                                s.kind != Statement::Kind::Assign);
    if (!value) {
      if (!body.stopped || checker.types.diagnostic)
        return false;
      if (s.kind != Statement::Kind::Let && s.kind != Statement::Kind::Assign &&
          s.kind != Statement::Kind::Expression)
        return fail("source.unreachable",
                    "statement action follows an operand that always stops",
                    s.span);
      continue;
    }
    if (s.kind == Statement::Kind::Require) {
      if (math())
        return fail("source.mode", "require needs ordered execution", s.span);
      std::optional<unsigned> variable;
      if (protocol()) {
        auto chosen = placement->owner(s.span);
        if (!chosen)
          return false;
        variable = chosen->owners.front();
        if ((requireOwner &&
             !placement->demand(*chosen, {*requireOwner}, s.span)) ||
            !placement->together(*chosen, components(*value), s.span))
          return false;
      }
      if (!inference.commit())
        return false;
      if (variable)
        requireOwner = inference.state->selected(*variable);
      if (!use(*value, s.span) ||
          !emitResults(Require{*value, requireOwner}, {}, s.span))
        return false;
      body.mayStop = true;
      ++statement;
      continue;
    }
    if (s.exchange) {
      auto sender = checker.roles(decl, {s.exchange->first}, s.span),
           receiver = checker.roles(decl, {s.exchange->second}, s.span);
      if (!sender || !receiver || !active(*sender, s.span) ||
          !active(*receiver, s.span))
        return false;
      auto before = body.values[value->index];
      if (!checker.types.executableType(before.type, s.span))
        return false;
      auto caps = checker.types.permissions(before.type, s.span, &decl);
      if (!caps)
        return false;
      if (!caps->copy || !caps->drop || !caps->share || !caps->wire)
        return fail("source.permission",
                    "send requires Copy, Drop, Share and Wire", s.span);
      if (*sender == *receiver)
        return fail("source.send", "sender and receiver must be distinct",
                    s.span);
      if (!demand(*value, *sender, s.span) || !inference.commit())
        return false;
      if (!use(*value, s.span))
        return false;
      value = emit(Exchange{sender->front(), receiver->front(), *value},
                   before.type, *receiver, s.span);
      if (!value)
        return false;
    }
    if (s.kind == Statement::Kind::Let || s.kind == Statement::Kind::Assign ||
        s.kind == Statement::Kind::Expression) {
      if (!s.exchange && protocol() &&
          (!demand(*value, selected.value_or(std::vector<unsigned>{}),
                   s.span) ||
           !inference.commit()))
        return false;
      if (!bindResults(s, {*value}))
        return false;
    } else {
      auto &type = body.values[value->index].type;
      auto caps = checker.types.permissions(type, s.span, &decl);
      if (!caps)
        return false;
      if (!local())
        return fail("source.mode",
                    "explicit resource disposal belongs in local functions",
                    s.span);
      if (s.kind == Statement::Kind::Drop && !caps->drop)
        return fail("source.drop", "explicit drop requires Drop", s.span);
      if (s.kind == Statement::Kind::Consume &&
          !checker.types.constructorAllowed(decl, type))
        return fail("source.private", "consume requires constructor authority",
                    s.span);
      if (s.kind == Statement::Kind::Consume) {
        auto fs = checker.types.fields(type, s.span);
        if (!fs)
          return false;
        for (auto &f : *fs) {
          auto child = checker.types.permissions(f.type, s.span, &decl);
          if (!child)
            return false;
          if (!child->drop)
            return fail("source.drop",
                        "unpack and transfer mandatory fields before consuming "
                        "the wrapper",
                        s.span);
        }
      }
      if (!use(*value, s.span) ||
          !emit(Consume{*value}, Type(Type::Kind::Unit), {}, s.span))
        return false;
    }
    ++statement;
  }
  if (body.stopped &&
      (source.returned || source.stopped || !source.results.empty()))
    return fail("source.unreachable", "terminator follows a guaranteed stop",
                source.span);
  if (source.stopped) {
    if (!local())
      return fail("source.mode", "stop requires ordered local mode",
                  source.span);
    if (!llvm::is_contained(
            {"reject", "abort", "exhausted", "incomplete", "refused"},
            source.stopReason))
      return fail("source.mode", "unknown local stop reason", source.span);
    body.stopped = true;
    body.stopReason = source.stopReason;
    body.mayStop = true;
  }
  return true;
}
std::optional<ValueId> BodyChecker::tail(const SyntaxBody &source,
                                         std::optional<Type> expected,
                                         bool allowUntypedStop) {
  if (!statements(source) || body.stopped)
    return {};
  // A protocol loop body has its own tail statement. Expression-block tails
  // instead participate in the enclosing statement's demands.
  std::optional<StatementPlacement> inference;
  if (protocol() && !placement)
    inference.emplace(*this);
  std::optional<ValueId> result;
  if (source.results.empty()) {
    if (expected && expected->kind != Type::Kind::Unit) {
      fail("source.type", "block without a tail has unit type", source.span);
      return {};
    }
    result = pack({}, source.span);
  } else if (source.results.size() != 1) {
    fail("source.return", "block requires one logical result", source.span);
    return {};
  } else
    result = expression(source.results.front().second, expected, 1,
                        allowUntypedStop);
  if (result && inference &&
      (!demand(*result, {}, source.span) || !inference->commit()))
    return {};
  return result;
}
std::optional<ValueId> BodyChecker::block(const Expression &expr,
                                          std::optional<Type> expected,
                                          bool allowUntypedStop) {
  auto value =
      tail(syntax.bodies[expr.regions.front()], expected, allowUntypedStop);
  if (!value && body.stopped && !expected && !allowUntypedStop &&
      !checker.types.diagnostic)
    fail("source.inference", "stopped value block needs an expected type",
         expr.span);
  return value;
}
bool BodyChecker::run(const SyntaxBody &source, ArrayRef<Port> outputs,
                      bool isProtocol) {
  if (!statements(source))
    return false;
  if (body.stopped)
    return finish(source.span);
  if (!source.returned)
    return fail("source.return",
                "continuing declaration requires an explicit return",
                source.span);
  std::map<std::string, unsigned> names;
  for (unsigned i = 0; i < outputs.size(); ++i)
    names.emplace(outputs[i].name, i);
  std::set<unsigned> seen;
  StatementPlacement inference(*this);
  body.results.resize(outputs.size());
  for (const auto &[name, id] : source.results) {
    auto found = names.find(name);
    if (isProtocol && name.empty() && outputs.size() == 1)
      found = names.begin();
    if (found == names.end())
      return fail("source.return",
                  "unknown return port; several ports require names",
                  source.span);
    if (!seen.insert(found->second).second)
      return fail("source.return", "duplicate return port", source.span);
    const auto &port = outputs[found->second];
    auto value = expression(id, port.type);
    if (!value) {
      if (body.stopped)
        body.results.clear();
      return body.stopped && !checker.types.diagnostic && finish(source.span);
    }
    if (isProtocol && !demand(*value, port.roles, syntax.expressions[id].span))
      return false;
    if (!use(*value, syntax.expressions[id].span))
      return false;
    body.results[found->second] = *value;
  }
  if (seen.size() != outputs.size())
    return fail("source.return", "missing return port", source.span);
  if (!inference.commit())
    return false;
  if (isProtocol)
    for (unsigned i = 0; i < outputs.size(); ++i)
      if (body.values[body.results[i].index].components != outputs[i].roles) {
        auto caps =
            checker.types.permissions(outputs[i].type, outputs[i].span, &decl);
        if (!caps || (!caps->drop &&
                      !fail("source.permission",
                            "return cannot discard components without Drop",
                            outputs[i].span)))
          return false;
      }
  return finish(source.span);
}
bool Checker::body(DeclarationId id, unsigned depth) {
  auto &decl = output.declarations[id.index];
  if (depth > work.limits.callDepth)
    return types.fail("source.limit", "helper call depth limit exceeded",
                      decl.span);
  if (bodyState[id.index] == 1)
    return types.fail("source.cycle", "recursive callable", decl.span);
  if (bodyState[id.index] == 2)
    return depth - 1 + bodyHeights[id.index] <= work.limits.callDepth ||
           types.fail("source.limit", "helper call depth limit exceeded",
                      decl.span);
  bodyState[id.index] = 1;
  bodyHeights[id.index] = 1;
  Body result;
  result.mode = (decl.kind == Declaration::Kind::Math ||
                 decl.kind == Declaration::Kind::Relation)
                    ? Body::Mode::Math
                : decl.kind == Declaration::Kind::Local ? Body::Mode::Local
                                                        : Body::Mode::Protocol;
  if (!resolveBindings(*this, decl, *sources[id.index]))
    return false;
  BodyChecker check(*this, decl, *sources[id.index], result, depth);
  for (unsigned i = 0; i < decl.inputs.size(); ++i) {
    auto &p = decl.inputs[i];
    auto caps = types.permissions(p.type, p.span, &decl);
    if (!caps)
      return false;
    if (result.mode == Body::Mode::Math &&
        !types.mathematicalData(p.type, p.span, &decl))
      return false;
    if (result.mode == Body::Mode::Protocol) {
      if (p.roles.size() > 1 && (!caps->copy || !caps->drop || !caps->share))
        return types.fail("source.permission",
                          "shared input requires Copy, Drop and Share", p.span);
    }
    if (!check.addInput(sources[id.index]->inputBindings[i], p.type,
                        result.mode == Body::Mode::Math
                            ? std::vector<unsigned>{i}
                            : p.roles,
                        p.span))
      return false;
  }
  for (unsigned i = 0; i < decl.services.size(); ++i)
    if (!check.addService(sources[id.index]->serviceBindings[i],
                          decl.services[i]))
      return false;
  for (auto &p : decl.outputs) {
    auto caps = types.permissions(p.type, p.span, &decl);
    if (!caps)
      return false;
    if (result.mode == Body::Mode::Math &&
        !types.mathematicalData(p.type, p.span, &decl))
      return false;
    if (result.mode == Body::Mode::Protocol && p.roles.size() > 1 &&
        (!caps->copy || !caps->drop || !caps->share))
      return types.fail("source.permission",
                        "shared output requires Copy, Drop and Share", p.span);
  }
  if (!check.run(sources[id.index]->bodies.front(), decl.outputs,
                 result.mode == Body::Mode::Protocol))
    return false;
  if (decl.effectAllowance &&
      ((result.mayStop && !decl.effectAllowance->mayStop) ||
       (result.opaque && !decl.effectAllowance->opaque)))
    return types.fail("source.effect",
                      "body exceeds its written effect allowance", decl.span);
  decl.body = std::make_shared<Body>(std::move(result));
  bodyState[id.index] = 2;
  return true;
}
} // namespace zkc::language::detail
