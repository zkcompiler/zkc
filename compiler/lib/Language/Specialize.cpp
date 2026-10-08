#include "Checker.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/Services.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
bool Checker::specialize(DeclarationId selected) {
  const unsigned templates = output.declarations.size();
  std::map<std::string, DeclarationId> instances;
  std::set<std::string> active;
  std::map<std::string, std::string> symbolKeys;
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
  auto closeService = [&](ServicePort &port, const Substitution &bindings) {
    if (!closeType(port.field, bindings, port.span))
      return false;
    port.contract = protocol::randomServiceContract(port.field.domain).str();
    return !port.contract.empty() ||
           fail("source.service",
                "no installed random service for selected field", port.span);
  };
  closeBody = [&](Body &body, const Substitution &bindings, Body::Mode mode) {
    body.mode = mode;
    for (auto &service : body.services)
      if (!closeService(service, bindings))
        return false;
    for (auto &value : body.values) {
      if (!closeType(value.type, bindings, value.span))
        return false;
      if (!permissions(value.type, value.span))
        return false;
      if (mode != Body::Mode::Math && !executableType(value.type, value.span))
        return false;
      if (mode == Body::Mode::Local)
        value.components.clear();
    }
    for (auto &op : body.operations) {
      if (!charge(1, op.span))
        return false;
      if (auto *primitive = std::get_if<LocalPrimitive>(&op.action)) {
        for (auto &argument : primitive->staticArguments)
          if (!closeType(argument, bindings, op.span))
            return false;
        if (primitive->bindingArguments) {
          for (auto &argument : *primitive->bindingArguments)
            if (!closeType(argument, bindings, op.span))
              return false;
          auto signature =
              kernelSignature(primitive->contract, *primitive->bindingArguments,
                              primitive->parameters, op.span);
          if (!signature)
            return false;
          if (primitive->operands.size() != signature->inputs.size() ||
              op.results.size() != 1 ||
              !(body.values[op.results.front().index].type ==
                signature->resultType()))
            return fail("source.kernel", "specialized kernel ports differ",
                        op.span);
          for (unsigned i = 0; i < primitive->operands.size(); ++i)
            if (!(body.values[primitive->operands[i].index].type ==
                  signature->inputs[i]))
              return fail("source.kernel", "specialized kernel input differs",
                          op.span);
        }
        if (!primitive->staticArguments.empty())
          primitive->parameters = {std::to_string(
              primitive->staticArguments.front().dimension.closedValue())};
      }
      if (auto *math = std::get_if<MathValue>(&op.action);
          math && !math->staticArguments.empty()) {
        for (auto &argument : math->staticArguments)
          if (!closeType(argument, bindings, op.span))
            return false;
        auto intrinsics = mathematicalIntrinsics();
        auto intrinsic = llvm::find_if(intrinsics, [&](const auto &candidate) {
          return candidate.identity == math->identity;
        });
        if (intrinsic == intrinsics.end())
          return fail("source.intrinsic", "unknown mathematical hook", op.span);
        auto signature =
            intrinsicSignature(nullptr, intrinsic->name, math->staticArguments,
                               math->parameters, op.span);
        if (!signature)
          return false;
        if (math->operands.size() != signature->inputs.size() ||
            op.results.size() != 1 ||
            body.values[op.results.front().index].type !=
                signature->resultType())
          return fail("source.intrinsic",
                      "specialized mathematical ports differ", op.span);
        for (unsigned i = 0; i < math->operands.size(); ++i)
          if (body.values[math->operands[i].index].type != signature->inputs[i])
            return fail("source.intrinsic",
                        "specialized mathematical input differs", op.span);
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
        auto targetMode =
            output.declarations[target.index].kind == Declaration::Kind::Local
                ? Body::Mode::Local
                : Body::Mode::Math;
        auto instance = instantiate(target, call->arguments, targetMode);
        if (!instance)
          return false;
        call->callee = *instance;
      } else if (auto *repeat = std::get_if<ProtocolRepeat>(&op.action)) {
        Type maximum(Type::Kind::Natural);
        maximum.dimension = repeat->maximum;
        maximum.symbolic = !repeat->maximum.isClosed();
        if (!closeType(maximum, bindings, op.span))
          return false;
        if (maximum.dimension.closedValue() > 1048576)
          return fail("source.bound",
                      "selected repeat maximum exceeds installed limit",
                      op.span);
        repeat->maximum = maximum.dimension;
        auto copy = std::make_shared<Body>(*repeat->region);
        if (!closeBody(*copy, bindings, Body::Mode::Protocol))
          return false;
        repeat->region = std::move(copy);
      } else if (auto *control = std::get_if<LocalControl>(&op.action)) {
        for (auto &region : control->regions) {
          auto copy = std::make_shared<Body>(*region);
          if (!closeBody(*copy, bindings, Body::Mode::Local))
            return false;
          region = std::move(copy);
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
    if ((!source.body && source.kind != Declaration::Kind::Relation) ||
        source.abstract) {
      fail("source.call", "cannot specialize an abstract callable",
           source.span);
      return {};
    }
    if (!checkArguments(source, args, source.span))
      return {};
    std::string key;
    detail::frame(key, source.qualifiedName);
    detail::frame(key, std::to_string(unsigned(mode)));
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
    if (++count > work.limits.instances || count > work.limits.declarations ||
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
      for (const auto &op : body.operations)
        if (const auto *math = std::get_if<MathValue>(&op.action)) {
          if (!charge(math->operands.size() + math->literal.size() + 1,
                      op.span))
            return false;
          for (const auto &arg : math->staticArguments)
            if (!chargeType(arg, op.span))
              return false;
          for (const auto &parameter : math->parameters)
            if (!charge(parameter.size() + 1, op.span))
              return false;
        }
      return true;
    };
    for (auto *ports : {&source.inputs, &source.outputs})
      for (const auto &port : *ports)
        if (!chargeType(port.type, port.span))
          return {};
    for (const auto &service : source.services)
      if (!chargeType(service.field, service.span))
        return {};
    if (source.body && !chargeBody(*source.body))
      return {};
    if (source.relation && !charge(source.relation->purposes.size() +
                                       source.relation->externalKind.size() +
                                       source.relation->key.size() +
                                       source.relation->revision.size() + 1,
                                   source.span))
      return {};
    for (const auto &clause : source.specifications) {
      if (!charge(clause.name.size() + 1, clause.span))
        return {};
      for (const auto *subject :
           {&clause.subject, clause.residual ? &*clause.residual : nullptr}) {
        if (!subject)
          continue;
        for (const auto &argument : subject->arguments)
          if (!chargeType(argument, subject->span))
            return {};
        for (const auto &operand : subject->operands)
          if (!charge(operand.path.size() + 1, operand.span))
            return {};
      }
      if (clause.decision &&
          !charge(clause.decision->path.size() + 1, clause.decision->span))
        return {};
    }
    Declaration result = source;
    DeclarationId id{uint32_t(output.declarations.size())};
    result.id = id;
    result.origin = origin;
    result.members.clear();
    result.staticArguments.assign(args.begin(), args.end());
    // Native participant carriers bound identifiers to 128 bytes. Reuse the
    // instance key for long declaration paths instead of narrowing source
    // names.
    if (!args.empty() || (result.body && result.body->mode != mode) ||
        result.symbol.size() > 128)
      result.symbol = "zkl_" + detail::digest(key);
    if (result.symbol.size() > work.limits.symbolBytes) {
      fail("source.limit", "specialized symbol exceeds byte limit",
           result.span);
      return {};
    }
    auto [symbol, inserted] = symbolKeys.emplace(result.symbol, key);
    if (!inserted && symbol->second != key) {
      fail("source.symbol", "distinct instance keys have the same symbol",
           result.span);
      return {};
    }
    output.declarations.push_back(result);
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
    for (auto &service : result.services)
      if (!closeService(service, bindings))
        return {};
    auto closeSubject = [&](RelationApplication &subject) {
      for (auto &argument : subject.arguments)
        if (!closeType(argument, bindings, subject.span))
          return false;
      auto selected =
          instantiate(subject.relation, subject.arguments, Body::Mode::Math);
      if (!selected)
        return false;
      subject.relation = *selected;
      const auto &relation = output.declarations[selected->index];
      for (unsigned i = 0; i < subject.operands.size(); ++i) {
        auto type = selectedType(result, subject.operands[i]);
        if (!type)
          return false;
        if (*type != relation.inputs[i].type)
          return fail("source.specification",
                      "closed relation operand type differs", subject.span);
      }
      return true;
    };
    for (auto &clause : result.specifications) {
      if (!closeSubject(clause.subject) ||
          (clause.residual && !closeSubject(*clause.residual)))
        return {};
      if (clause.decision && !selectedType(result, *clause.decision))
        return {};
    }
    if (result.body) {
      auto body = std::make_shared<Body>(*result.body);
      if (!closeBody(*body, bindings, mode))
        return {};
      if (result.kind == Declaration::Kind::Math ||
          result.kind == Declaration::Kind::Relation)
        for (const auto &value : body->values)
          if (!mathematicalData(value.type, value.span))
            return {};
      result.body = std::move(body);
    }
    result.parameters.clear();
    result.bounds.clear();
    result.permissionBounds.clear();
    output.declarations[id.index] = std::move(result);
    instances.emplace(key, id);
    active.erase(key);
    return id;
  };
  auto target = output.declarations[selected.index].target;
  auto args = output.declarations[selected.index].staticArguments;
  if (!target)
    return fail("source.entry", "Entry has no checked target",
                output.declarations[selected.index].span);
  auto instance = instantiate(*target, args, Body::Mode::Protocol);
  if (!instance)
    return false;
  if (!checkProofEntry(output.declarations[selected.index],
                       output.declarations[instance->index]))
    return false;
  for (const auto &port : output.declarations[instance->index].inputs)
    if (!ingress(port.type, port.span))
      return false;
  output.declarations[selected.index].target = *instance;
  for (unsigned i = 0; i < templates; ++i)
    output.declarations[i].body.reset();
  return true;
}
} // namespace zkc::language::detail
