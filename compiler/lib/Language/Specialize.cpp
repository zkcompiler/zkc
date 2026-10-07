#include "Checker.h"
#include "zkc/Contracts/Kernels.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
bool Checker::specialize() {
  const unsigned templates = output.declarations.size();
  std::map<std::string, DeclarationId> instances;
  std::set<std::string> active;
  uint64_t count = 0;
  std::function<std::optional<DeclarationId>(DeclarationId, ArrayRef<Type>,
                                             Body::Mode)>
      instantiate;
  std::function<bool(Body &, const Substitution &, Body::Mode)> closeBody;
  auto closeType = [&](Type &type, const Substitution &bindings, Span span) {
    auto result = substitute(type, bindings, span);
    if (!result)
      return false;
    if (symbolic(*result))
      return fail("source.generic", "unresolved type after static substitution",
                  span);
    type = std::move(*result);
    return true;
  };
  closeBody = [&](Body &body, const Substitution &bindings, Body::Mode mode) {
    body.mode = mode;
    for (auto &value : body.values) {
      if (!closeType(value.type, bindings, value.span))
        return false;
      if (!permissions(value.type, value.span))
        return false;
      if (mode == Body::Mode::Local)
        value.components.clear();
    }
    if (mode == Body::Mode::Protocol)
      for (unsigned i = 0; i < body.inputs; ++i)
        if (!ingress(body.values[i].type, body.values[i].span))
          return false;
    for (auto &op : body.operations) {
      if (!charge(1, op.span))
        return false;
      if (auto *primitive = std::get_if<LocalPrimitive>(&op.action)) {
        for (auto &argument : primitive->staticArguments)
          if (!closeType(argument, bindings, op.span))
            return false;
        if (!primitive->staticArguments.empty())
          primitive->parameters = {std::to_string(
              primitive->staticArguments.front().dimension.closedValue())};
      }
      if (auto *exchange = std::get_if<Exchange>(&op.action)) {
        if (!ingress(body.values[exchange->payload.index].type, op.span))
          return false;
      }
      if (auto *application = std::get_if<ProtocolApplication>(&op.action)) {
        for (auto &argument : application->arguments)
          if (!closeType(argument, bindings, op.span))
            return false;
        DeclarationId target = application->callee;
        if (auto origin = output.declarations[target.index].origin) {
          application->arguments =
              output.declarations[target.index].staticArguments;
          target = *origin;
        }
        auto instance =
            instantiate(target, application->arguments, Body::Mode::Protocol);
        if (!instance)
          return false;
        application->callee = *instance;
      } else if (auto *call = std::get_if<HelperCall>(&op.action)) {
        for (auto &arg : call->arguments)
          if (!closeType(arg, bindings, op.span))
            return false;
        DeclarationId target = call->callee;
        if (auto origin = output.declarations[target.index].origin) {
          call->arguments = output.declarations[target.index].staticArguments;
          target = *origin;
        }
        if (call->component) {
          if (!closeType(*call->component, bindings, op.span))
            return false;
          auto *component = typeDeclaration(*call->component);
          if (!component || component->kind != Declaration::Kind::Component)
            return fail("source.conformance",
                        "static dispatch did not select a component", op.span);
          const auto name = output.declarations[target.index].name;
          auto found = llvm::find_if(component->members, [&](auto id) {
            return output.declarations[id.index].name == name;
          });
          if (found == component->members.end())
            return fail("source.conformance", "static dispatch member missing",
                        op.span);
          target = *found;
          call->arguments = call->component->arguments;
        }
        auto targetMode = output.declarations[target.index].kind ==
                                      Declaration::Kind::Local ||
                                  mode == Body::Mode::Local
                              ? Body::Mode::Local
                              : Body::Mode::Math;
        auto instance = instantiate(target, call->arguments, targetMode);
        if (!instance)
          return false;
        call->callee = *instance;
      } else if (auto *control = std::get_if<LocalControl>(&op.action)) {
        for (auto &region : control->regions) {
          auto copy = std::make_shared<Body>(*region);
          if (!closeBody(*copy, bindings, Body::Mode::Local))
            return false;
          region = std::move(copy);
        }
      } else if (auto *math = std::get_if<MathValue>(&op.action)) {
        if (mode == Body::Mode::Local) {
          std::string contract;
          switch (math->identity) {
          case MathematicalIdentity::BooleanConstant:
            contract = "bool.constant";
            break;
          case MathematicalIdentity::BooleanEqual:
            contract = "bool.equal";
            break;
          case MathematicalIdentity::FieldConstant:
            contract = "field.constant";
            break;
          case MathematicalIdentity::FieldAdd:
            contract = "field.add";
            break;
          case MathematicalIdentity::FieldSubtract:
            contract = "field.sub";
            break;
          case MathematicalIdentity::FieldMultiply:
            contract = "field.mul";
            break;
          case MathematicalIdentity::FieldEqual:
            contract = "field.equal";
            break;
          case MathematicalIdentity::GroupAdd:
            contract = "curve.add";
            break;
          case MathematicalIdentity::GroupScale:
            contract = "curve.scale";
            break;
          case MathematicalIdentity::GroupEqual:
            contract = "curve.equal";
            break;
          default:
            return fail("source.mode",
                        "mathematical operation has no ordered representation",
                        op.span);
          }
          LocalPrimitive ordered{contract, math->operands, {}};
          if (!math->literal.empty())
            ordered.parameters.push_back(math->literal);
          op.action = std::move(ordered);
        }
      }
    }
    if (mode == Body::Mode::Local)
      body.formationRequirements.clear();
    return true;
  };
  instantiate = [&](DeclarationId origin, ArrayRef<Type> args,
                    Body::Mode mode) -> std::optional<DeclarationId> {
    const auto &source = output.declarations[origin.index];
    if (!source.body || source.abstract) {
      fail("source.call", "cannot specialize an abstract callable",
           source.span);
      return {};
    }
    if (!checkArguments(source, args, source.span))
      return {};
    std::string key = std::to_string(origin.index) + ":" +
                      std::to_string(unsigned(mode)) + ":";
    for (auto &arg : args) {
      if (symbolic(arg)) {
        fail("source.generic",
             "entry specialization requires closed static arguments",
             source.span);
        return {};
      }
      if (!chargeType(arg, source.span))
        return {};
      detail::frame(key, typeIdentity(arg));
    }
    auto known = instances.find(key);
    if (known != instances.end())
      return known->second;
    if (!active.insert(key).second) {
      fail("source.cycle", "recursive static instantiation", source.span);
      return {};
    }
    if (++count > work.limits.instances ||
        !charge(key.size() + 1, source.span)) {
      if (!diagnostic)
        fail("source.limit", "static instance limit exceeded", source.span);
      return {};
    }
    // Charge the snapshot before allocating it. Recursive instances can grow
    // the declaration vector, so no reference into that vector crosses
    // closeBody.
    std::function<bool(const Body &)> chargeBody = [&](const Body &body) {
      if (!charge(body.operations.size() + body.values.size() + 1, source.span))
        return false;
      for (const auto &value : body.values)
        if (!chargeType(value.type, value.span))
          return false;
      return true;
    };
    for (auto *ports : {&source.inputs, &source.outputs})
      for (const auto &port : *ports)
        if (!chargeType(port.type, port.span))
          return {};
    if (!chargeBody(*source.body))
      return {};
    Declaration result = source;
    const bool reuse = args.empty() && result.body->mode == mode;
    DeclarationId id =
        reuse ? origin : DeclarationId{uint32_t(output.declarations.size())};
    if (!reuse) {
      if (output.declarations.size() >= work.limits.declarations) {
        fail("source.limit", "specialized declaration count exceeded",
             result.span);
        return {};
      }
      result.id = id;
      result.origin = origin;
      result.staticArguments.assign(args.begin(), args.end());
      result.symbol = "zkl_instance_" + std::to_string(id.index);
      if (result.symbol.size() > work.limits.symbolBytes) {
        fail("source.limit", "specialized symbol exceeds byte limit",
             result.span);
        return {};
      }
      output.declarations.push_back(result);
    }
    auto bindings = substitution(result, args);
    if (result.parent && output.declarations[result.parent->index].kind ==
                             Declaration::Kind::Component) {
      auto &parent = output.declarations[result.parent->index];
      Type self(Type::Kind::Component, parent.qualifiedName);
      self.arguments.assign(args.begin(),
                            args.begin() + parent.parameters.size());
      if (parent.implementation)
        bindings.emplace("self:" + parent.implementation->domain, self);
    }
    for (auto *ports : {&result.inputs, &result.outputs})
      for (auto &port : *ports)
        if (!closeType(port.type, bindings, port.span))
          return {};
    if (!closeBody(*result.body, bindings, mode))
      return {};
    if (mode == Body::Mode::Local)
      result.kind = Declaration::Kind::Local;
    result.parameters.clear();
    result.bounds.clear();
    result.permissionBounds.clear();
    output.declarations[id.index] = std::move(result);
    instances.emplace(key, id);
    active.erase(key);
    return id;
  };
  // Keep concrete unused definitions checkable and visible in the original.
  for (unsigned i = 0; i < templates; ++i) {
    auto &decl = output.declarations[i];
    if (decl.body && decl.parameters.empty() &&
        !instantiate(DeclarationId{i}, {}, decl.body->mode))
      return false;
  }
  for (unsigned i = 0; i < templates; ++i) {
    if (output.declarations[i].kind != Declaration::Kind::Entry)
      continue;
    auto &entry = output.declarations[i];
    auto &source = *sources[i];
    auto target = resolve(entry, source.target, source.span);
    if (!target)
      return false;
    auto &protocol = output.declarations[target->index];
    if (protocol.kind != Declaration::Kind::Protocol)
      return fail("source.entry", "entry target must be a protocol",
                  source.span);
    auto args = arguments(entry, protocol, source.targetArguments, source.span);
    if (!args)
      return false;
    auto instance = instantiate(*target, *args, Body::Mode::Protocol);
    if (!instance)
      return false;
    output.declarations[i].target = *instance;
  }
  return true;
}
} // namespace zkc::language::detail
