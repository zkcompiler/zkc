#include "BodyCheck.h"
#include "zkc/Contracts/Kernels.h"
#include <algorithm>
#include <numeric>
using namespace llvm;
namespace zkc::language::detail {
namespace {
bool prefix(ArrayRef<unsigned> a, ArrayRef<unsigned> b) {
  return a.size() <= b.size() && std::equal(a.begin(), a.end(), b.begin());
}
} // namespace
BodyChecker::BodyChecker(Checker &checker, Declaration &decl,
                         const SyntaxDeclaration &syntax, Body &body,
                         unsigned depth)
    : checker(checker), decl(decl), syntax(syntax), body(body),
      callDepth(depth) {}
bool BodyChecker::fail(StringRef code, const Twine &message, Span span) {
  return checker.fail(code, message, span);
}
bool BodyChecker::active(ArrayRef<unsigned> roles, Span span) {
  auto available = activeRoles.value_or(allRoles());
  return std::includes(available.begin(), available.end(), roles.begin(),
                       roles.end()) ||
         fail("source.roles",
              "action uses a participant outside the active roster", span);
}
std::vector<unsigned> BodyChecker::allRoles() const {
  std::vector<unsigned> result(decl.roles.size());
  std::iota(result.begin(), result.end(), 0);
  return result;
}
bool BodyChecker::data(const Type &type, Span span) {
  return checker.mathematicalData(type, span, &decl);
}
bool BodyChecker::addService(const ServicePort &port) {
  if (!protocol() || !checker.bindingName(decl, port.name, port.span) ||
      !checker.chargeType(port.field, port.span))
    return false;
  if (bindings.count(port.name) ||
      !services.emplace(port.name, ServiceId{uint32_t(body.services.size())})
           .second)
    return fail("source.shadow", "duplicate service or data binding",
                port.span);
  body.services.push_back(port);
  return true;
}
std::optional<ServiceId> BodyChecker::service(const Expression &expr) {
  if (expr.kind != Expression::Kind::Name) {
    fail("source.service", "service reference must name a managed binding",
         expr.span);
    return {};
  }
  auto found = services.find(expr.text);
  if (found == services.end()) {
    fail("source.service", "unknown managed service: " + expr.text, expr.span);
    return {};
  }
  return found->second;
}
bool BodyChecker::addInput(StringRef name, const Type &type,
                           std::vector<unsigned> components, Span span) {
  if (!math() && !checker.executableType(type, span))
    return false;
  if (!checker.bindingName(decl, name, span) || !checker.chargeType(type, span))
    return false;
  if (services.count(name.str()))
    return fail("source.shadow", "data binding shadows a service", span);
  if (!bindings.emplace(name.str(), ValueId{uint32_t(body.values.size())})
           .second)
    return fail("source.duplicate", "duplicate local input or capture", span);
  body.values.push_back({type, std::move(components), span});
  uses.emplace_back();
  ++body.inputs;
  return true;
}
std::optional<ValueId> BodyChecker::emit(decltype(Operation::action) action,
                                         const Type &type,
                                         std::vector<unsigned> components,
                                         Span span) {
  auto ids = emitResults(std::move(action),
                         {{type, std::move(components), span}}, span);
  return ids ? std::optional<ValueId>(ids->front()) : std::nullopt;
}
std::optional<std::vector<ValueId>>
BodyChecker::emitResults(decltype(Operation::action) action,
                         std::vector<Value> results, Span span) {
  if (!checker.accept(checker.work.count(checker.work.operations,
                                         checker.work.limits.operations,
                                         "operation count", span)))
    return {};
  for (const auto &value : results) {
    if (!math() && !checker.executableType(value.type, span))
      return {};
    if (!checker.chargeType(value.type, span) ||
        !checker.charge(value.components.size() + 1, span))
      return {};
    if (protocol() && value.components.size() > 1) {
      auto caps = checker.permissions(value.type, span, &decl);
      if (!caps || !caps->share) {
        if (!checker.diagnostic)
          fail("source.permission",
               "multiple participant components require Share", span);
        return {};
      }
    }
  }
  std::vector<ValueId> ids;
  for (auto &value : results) {
    ids.push_back(ValueId{uint32_t(body.values.size())});
    body.values.push_back(std::move(value));
    uses.emplace_back();
  }
  body.operations.push_back({std::move(action), ids, span, statement});
  return ids;
}
std::optional<std::vector<unsigned>>
BodyChecker::combine(ArrayRef<ValueId> args, Span span) {
  std::vector<unsigned> result =
      math() || local() ? std::vector<unsigned>{} : allRoles();
  for (auto id : args) {
    auto &next = body.values[id.index].components;
    if (!checker.charge(result.size() + next.size() + 1, span))
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
  return result;
}
bool BodyChecker::restricted(const Type &type) {
  if (type.kind == Type::Kind::Associated || type.kind == Type::Kind::Parameter)
    return true;
  auto *d = checker.typeDeclaration(type);
  return d && d->permissions.has_value();
}
std::optional<Type> BodyChecker::projected(Type type, ArrayRef<unsigned> path,
                                           Span span) {
  return checker.projectedType(decl, std::move(type), path, span);
}
bool BodyChecker::use(ValueId value, Span span, ArrayRef<unsigned> path) {
  if (!checker.charge(path.size() + 1, span))
    return false;
  auto type = projected(body.values[value.index].type, path, span);
  if (!type)
    return false;
  auto caps = checker.permissions(*type, span, &decl);
  if (!caps)
    return false;
  auto &state = uses[value.index];
  for (auto &moved : state.moved) {
    if (!checker.charge(moved.size() + 1, span))
      return false;
    if (prefix(moved, path) || prefix(path, moved))
      return fail("source.move", "value or overlapping field was already moved",
                  span);
  }
  state.used.emplace_back(path.begin(), path.end());
  if (!caps->copy)
    state.moved.emplace_back(path.begin(), path.end());
  return true;
}
bool BodyChecker::finish(Span span) {
  if (body.stopped)
    return true;
  for (unsigned i = 0; i < body.values.size(); ++i) {
    auto &state = uses[i];
    std::function<bool(const Type &, std::vector<unsigned>, unsigned)> check =
        [&](const Type &t, std::vector<unsigned> path, unsigned depth) {
          if (depth > checker.work.limits.typeDepth || !checker.charge(1, span))
            return checker.diagnostic ? false
                                      : fail("source.limit",
                                             "resource obligation depth", span);
          auto caps = checker.permissions(t, span, &decl);
          if (!caps)
            return false;
          if (caps->drop)
            return true;
          for (auto &used : state.used) {
            if (!checker.charge(used.size() + 1, span))
              return false;
            if (prefix(used, path))
              return true;
          }
          if (!restricted(t) &&
              (t.kind == Type::Kind::Record || t.kind == Type::Kind::Tuple ||
               (t.kind == Type::Kind::Array && t.dimension.isClosed()))) {
            auto fs = checker.fields(t, span);
            if (!fs)
              return false;
            if (!fs->empty()) {
              for (unsigned j = 0; j < fs->size(); ++j) {
                auto child = path;
                child.push_back(j);
                if (!check((*fs)[j].type, std::move(child), depth + 1))
                  return false;
              }
              return true;
            }
          }
          return fail("source.drop",
                      "value without Drop remains unused on a continuing path",
                      body.values[i].span);
        };
    if (!check(body.values[i].type, {}, 1))
      return false;
  }
  return true;
}
std::optional<std::pair<ValueId, std::vector<unsigned>>>
BodyChecker::place(uint32_t id, unsigned depth) {
  if (depth > checker.work.limits.expressionDepth) {
    fail("source.limit", "place depth limit", syntax.expressions[id].span);
    return {};
  }
  auto &expr = syntax.expressions[id];
  if (expr.kind == Expression::Kind::Name) {
    auto found = bindings.find(expr.text);
    if (found == bindings.end()) {
      fail("source.name", "unknown local value: " + expr.text, expr.span);
      return {};
    }
    return std::make_pair(found->second, std::vector<unsigned>{});
  }
  if (expr.kind != Expression::Kind::Projection) {
    fail("source.place", "field access requires a named place", expr.span);
    return {};
  }
  auto base = place(expr.children.front(), depth + 1);
  if (!base)
    return {};
  auto type =
      projected(body.values[base->first.index].type, base->second, expr.span);
  if (!type)
    return {};
  auto index = checker.fieldIndex(decl, *type, expr.text, expr.span);
  if (!index)
    return {};
  base->second.push_back(*index);
  if (!projected(body.values[base->first.index].type, base->second, expr.span))
    return {};
  return base;
}
bool BodyChecker::run(const SyntaxBody &source, ArrayRef<Port> outputs,
                      bool isProtocol) {
  for (auto &s : source.statements) {
    owner.reset();
    std::optional<unsigned> guardOwner;
    if (s.kind == Statement::Kind::Alias) {
      if (!protocol() || s.owner || !checker.bindingName(decl, s.name, s.span))
        return checker.diagnostic
                   ? false
                   : fail("source.mode",
                          "service aliases require protocol mode", s.span);
      auto root = service(syntax.expressions[s.expression]);
      if (!root)
        return false;
      if (bindings.count(s.name) || !services.emplace(s.name, *root).second)
        return fail("source.shadow",
                    "service alias shadows an existing binding", s.span);
      ++statement;
      continue;
    }
    if (syntax.expressions[s.expression].kind == Expression::Kind::FinishIf) {
      if (!complete(s))
        return false;
      ++statement;
      continue;
    }
    if (syntax.expressions[s.expression].kind == Expression::Kind::Repeat) {
      if (!repeat(s))
        return false;
      ++statement;
      continue;
    }
    if (syntax.expressions[s.expression].kind == Expression::Kind::Apply) {
      if (!application(s))
        return false;
      ++statement;
      continue;
    }
    if (s.resultNames)
      return fail(
          "source.binding",
          "multiple bindings require a protocol application or control action",
          s.span);
    if (s.owner) {
      auto selected = checker.roles(decl, {*s.owner}, s.span);
      if (!selected)
        return false;
      if (!active(*selected, s.span))
        return false;
      if (s.kind == Statement::Kind::Guard)
        guardOwner = selected->front();
      else
        owner = selected->front();
    }
    if (s.kind == Statement::Kind::Let &&
        !checker.bindingName(decl, s.name, s.span))
      return false;
    if (s.kind == Statement::Kind::Let &&
        (bindings.count(s.name) || services.count(s.name)))
      return fail("source.shadow", "binding shadows an existing local", s.span);
    std::optional<Type> expected;
    if (s.type) {
      expected = checker.type(decl, *s.type);
      if (!expected)
        return false;
    }
    if (s.kind == Statement::Kind::Require || s.kind == Statement::Kind::Guard)
      expected = Type{};
    auto value = expression(s.expression, expected);
    if (!value)
      return false;
    if (s.kind == Statement::Kind::Guard) {
      if (!protocol() || !guardOwner ||
          !llvm::is_contained(body.values[value->index].components,
                              *guardOwner))
        return fail("source.roles",
                    "guard condition must be available at its owner", s.span);
      if (!use(*value, s.span) ||
          !emitResults(ProtocolGuard{*value, *guardOwner}, {}, s.span))
        return false;
      body.mayStop = true;
      ++statement;
      continue;
    }
    if (s.owner) {
      const auto *call =
          body.operations.empty()
              ? nullptr
              : std::get_if<HelperCall>(&body.operations.back().action);
      if (!call || !call->owner || body.operations.back().results.size() != 1 ||
          body.operations.back().results.front().index != value->index)
        return fail("source.mode",
                    "owned statement requires a local function call", s.span);
    }
    if (s.exchange) {
      auto sender = checker.roles(decl, {s.exchange->first}, s.span),
           receiver = checker.roles(decl, {s.exchange->second}, s.span);
      if (!sender || !receiver || !active(*sender, s.span) ||
          !active(*receiver, s.span))
        return false;
      auto before = body.values[value->index];
      if (!checker.executableType(before.type, s.span))
        return false;
      auto caps = checker.permissions(before.type, s.span, &decl);
      if (!caps)
        return false;
      if (!caps->copy || !caps->drop || !caps->share || !caps->wire)
        return fail("source.permission",
                    "send requires Copy, Drop, Share and Wire", s.span);
      if (*sender == *receiver)
        return fail("source.send", "sender and receiver must be distinct",
                    s.span);
      if (!llvm::is_contained(before.components, sender->front()))
        return fail("source.roles", "payload unavailable at sender", s.span);
      if (!use(*value, s.span))
        return false;
      value = emit(Exchange{sender->front(), receiver->front(), *value},
                   before.type, *receiver, s.span);
      if (!value)
        return false;
    }
    if (s.roles) {
      auto selected = checker.roles(decl, *s.roles, s.span);
      if (!selected)
        return false;
      auto before = body.values[value->index];
      if (!std::includes(before.components.begin(), before.components.end(),
                         selected->begin(), selected->end()))
        return fail("source.roles",
                    "binding cannot gain participant availability", s.span);
      if (*selected != before.components) {
        if (!checker.executableType(before.type, s.span))
          return false;
        auto caps = checker.permissions(before.type, s.span, &decl);
        if (!caps)
          return false;
        if (!caps->drop)
          return fail("source.permission",
                      "restriction cannot discard a component without Drop",
                      s.span);
        if (!use(*value, s.span))
          return false;
        value = emit(Restriction{*value, *selected}, before.type, *selected,
                     s.span);
        if (!value)
          return false;
      }
    }
    if (s.kind == Statement::Kind::Let) {
      // A binding transfers the expression's value to a fresh logical place.
      // Copy/Drop obligations attach to that place even when its layout is
      // empty.
      auto before = body.values[value->index];
      if (!use(*value, s.span))
        return false;
      auto alias =
          emit(Projection{*value, {}}, before.type, before.components, s.span);
      if (!alias)
        return false;
      bindings.emplace(s.name, *alias);
    } else if (s.kind == Statement::Kind::Require) {
      if (!local())
        return fail("source.mode",
                    "require belongs in an ordered local function", s.span);
      if (!use(*value, s.span))
        return false;
      if (!emit(LocalPrimitive{"control.require", {*value}, {}},
                Type(Type::Kind::Unit), {}, s.span))
        return false;
      body.mayStop = true;
    } else {
      auto &type = body.values[value->index].type;
      auto caps = checker.permissions(type, s.span, &decl);
      if (!caps)
        return false;
      if (!local())
        return fail("source.mode",
                    "explicit resource disposal belongs in local functions",
                    s.span);
      if (s.kind == Statement::Kind::Drop && !caps->drop)
        return fail("source.drop", "explicit drop requires Drop", s.span);
      if (s.kind == Statement::Kind::Consume &&
          !checker.constructorAllowed(decl, type))
        return fail("source.private", "consume requires constructor authority",
                    s.span);
      if (s.kind == Statement::Kind::Consume) {
        auto fs = checker.fields(type, s.span);
        if (!fs)
          return false;
        for (auto &f : *fs) {
          auto child = checker.permissions(f.type, s.span, &decl);
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
  owner.reset();
  if (source.stopped) {
    if (!local())
      return fail("source.mode", "stop requires ordered local mode",
                  source.span);
    body.stopped = true;
    body.stopReason = source.stopReason;
    body.mayStop = true;
  } else {
    std::vector<Port> inferred;
    if (!isProtocol && outputs.empty()) {
      if (source.results.size() != 1)
        return fail("source.return", "local region requires one logical result",
                    source.span);
      auto type = hint(source.results.front().second);
      if (!type) {
        if (!checker.diagnostic)
          fail("source.inference", "region result needs an explicit context",
               source.span);
        return false;
      }
      inferred.push_back({"result", *type, {}, source.span});
      outputs = inferred;
    }
    std::map<std::string, unsigned> names;
    for (unsigned i = 0; i < outputs.size(); ++i)
      names.emplace(outputs[i].name, i);
    std::set<unsigned> seen;
    body.results.resize(outputs.size());
    for (auto &[name, id] : source.results) {
      auto found = names.find(name);
      if (found == names.end())
        return fail("source.return", "unknown return port", source.span);
      if (!seen.insert(found->second).second)
        return fail("source.return", "duplicate return port", source.span);
      auto &port = outputs[found->second];
      auto value = expression(id, port.type);
      if (!value)
        return false;
      if (isProtocol) {
        auto &available = body.values[value->index].components;
        if (!std::includes(available.begin(), available.end(),
                           port.roles.begin(), port.roles.end()))
          return fail("source.roles", "result unavailable at output roles",
                      syntax.expressions[id].span);
        if (available != port.roles) {
          auto caps = checker.permissions(port.type, port.span, &decl);
          if (!caps)
            return false;
          if (!caps->drop)
            return fail("source.permission",
                        "return cannot discard components without Drop",
                        port.span);
        }
      }
      if (!use(*value, syntax.expressions[id].span))
        return false;
      body.results[found->second] = *value;
    }
    if (seen.size() != outputs.size())
      return fail("source.return", "missing return port", source.span);
  }
  return finish(source.span);
}
bool Checker::body(DeclarationId id, unsigned depth) {
  auto &decl = output.declarations[id.index];
  if (depth > work.limits.callDepth)
    return fail("source.limit", "helper call depth limit exceeded", decl.span);
  if (bodyState[id.index] == 1)
    return fail("source.cycle", "recursive callable", decl.span);
  if (bodyState[id.index] == 2)
    return depth - 1 + bodyHeights[id.index] <= work.limits.callDepth ||
           fail("source.limit", "helper call depth limit exceeded", decl.span);
  bodyState[id.index] = 1;
  bodyHeights[id.index] = 1;
  Body result;
  result.mode = (decl.kind == Declaration::Kind::Math ||
                 decl.kind == Declaration::Kind::Relation)
                    ? Body::Mode::Math
                : decl.kind == Declaration::Kind::Local ? Body::Mode::Local
                                                        : Body::Mode::Protocol;
  BodyChecker check(*this, decl, *sources[id.index], result, depth);
  for (unsigned i = 0; i < decl.inputs.size(); ++i) {
    auto &p = decl.inputs[i];
    auto caps = permissions(p.type, p.span, &decl);
    if (!caps)
      return false;
    if (result.mode == Body::Mode::Math &&
        !mathematicalData(p.type, p.span, &decl))
      return false;
    if (result.mode == Body::Mode::Protocol) {
      if (p.roles.size() > 1 && (!caps->copy || !caps->drop || !caps->share))
        return fail("source.permission",
                    "shared input requires Copy, Drop and Share", p.span);
    }
    if (!check.addInput(p.name, p.type,
                        result.mode == Body::Mode::Math
                            ? std::vector<unsigned>{i}
                            : p.roles,
                        p.span))
      return false;
  }
  for (const auto &service : decl.services)
    if (!check.addService(service))
      return false;
  for (auto &p : decl.outputs) {
    auto caps = permissions(p.type, p.span, &decl);
    if (!caps)
      return false;
    if (result.mode == Body::Mode::Math &&
        !mathematicalData(p.type, p.span, &decl))
      return false;
    if (result.mode == Body::Mode::Protocol && p.roles.size() > 1 &&
        (!caps->copy || !caps->drop || !caps->share))
      return fail("source.permission",
                  "shared output requires Copy, Drop and Share", p.span);
  }
  if (!check.run(sources[id.index]->bodies.front(), decl.outputs,
                 result.mode == Body::Mode::Protocol))
    return false;
  if (decl.effectAllowance &&
      ((result.mayStop && !decl.effectAllowance->mayStop) ||
       (result.opaque && !decl.effectAllowance->opaque)))
    return fail("source.effect", "body exceeds its written effect allowance",
                decl.span);
  decl.body = std::make_shared<Body>(std::move(result));
  bodyState[id.index] = 2;
  return true;
}
} // namespace zkc::language::detail
