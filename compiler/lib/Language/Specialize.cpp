#include "Semantics.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Language/Builtins.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
namespace {
// Charge nested payloads before specialization copies immutable template
// bodies.
bool chargeBodySnapshot(Semantics &types, const Body &body, Span span) {
  if (!types.charge(body.operations.size() + body.values.size() +
                        body.results.size() + body.stopReason.size() + 1,
                    span))
    return false;
  for (const auto &value : body.values)
    if (!types.charge(value.components.size(), value.span) ||
        !types.chargeType(value.type, value.span))
      return false;
  for (const auto &requirement : body.formationRequirements)
    if (!types.charge(requirement.size() + 1, span))
      return false;
  for (const auto &service : body.services)
    if (!types.charge(service.name.size() + service.contract.size() + 1,
                      service.span) ||
        !types.chargeType(service.field, service.span))
      return false;
  for (const auto &op : body.operations) {
    if (!types.charge(op.results.size(), op.span))
      return false;
    if (op.binding) {
      const auto &binding = *op.binding;
      if (!types.charge(binding.operands.size() + binding.symbol.size() + 1,
                        op.span))
        return false;
      for (const auto &member : binding.family)
        if (!types.charge(member.size() + 1, op.span))
          return false;
      for (const auto &arg : binding.arguments)
        if (!types.chargeType(arg, op.span))
          return false;
      if (binding.target.component &&
          !types.chargeType(*binding.target.component, op.span))
        return false;
    }
    if (const auto *math = std::get_if<MathValue>(&op.action)) {
      if (!types.charge(math->operands.size() + math->literal.size() + 1,
                        op.span))
        return false;
      for (const auto &arg : math->staticArguments)
        if (!types.chargeType(arg, op.span))
          return false;
      for (const auto &parameter : math->parameters)
        if (!types.charge(parameter.size() + 1, op.span))
          return false;
    } else if (const auto *primitive =
                   std::get_if<LocalPrimitive>(&op.action)) {
      if (!types.charge(primitive->contract.size() +
                            primitive->operands.size() + 1,
                        op.span))
        return false;
      for (const auto &parameter : primitive->parameters)
        if (!types.charge(parameter.size() + 1, op.span))
          return false;
      for (const auto &arg : primitive->staticArguments)
        if (!types.chargeType(arg, op.span))
          return false;
      for (const auto &reference : primitive->assetReferences)
        if (!types.chargeType(reference.term, op.span))
          return false;
      if (primitive->bindingArguments)
        for (const auto &arg : *primitive->bindingArguments)
          if (!types.chargeType(arg, op.span))
            return false;
    } else if (const auto *bulk = std::get_if<BulkApplication>(&op.action)) {
      if (!types.charge(bulk->operands.size() + bulk->mapped.size() + 1,
                        op.span))
        return false;
      for (const auto &arg : bulk->arguments)
        if (!types.chargeType(arg, op.span))
          return false;
    } else if (const auto *repeat = std::get_if<ProtocolRepeat>(&op.action)) {
      if (!types.charge(repeat->roles.size() + repeat->carried.size() +
                            repeat->captures.size() + repeat->services.size(),
                        op.span) ||
          !chargeBodySnapshot(types, *repeat->region, op.span))
        return false;
    } else if (const auto *control = std::get_if<LocalControl>(&op.action)) {
      if (!types.charge(control->operands.size() + control->regions.size(),
                        op.span))
        return false;
      for (const auto &alternative : control->alternatives)
        if (!types.charge(alternative.size() + 1, op.span))
          return false;
      for (const auto &region : control->regions)
        if (!chargeBodySnapshot(types, *region, op.span))
          return false;
    }
  }
  return true;
}
} // namespace
llvm::Error specialize(std::vector<Declaration> &declarations,
                       ArrayRef<Asset> assets, Work &work,
                       DeclarationId selected) {
  Semantics types(declarations, assets, work);
  auto close = [&]() -> bool {
    const unsigned templates = declarations.size();
    std::map<std::string, DeclarationId> instances;
    std::map<unsigned, unsigned> heights;
    std::set<std::string> active;
    std::map<std::string, std::string> symbolKeys;
    uint64_t count = 0;
    std::function<std::optional<DeclarationId>(DeclarationId, ArrayRef<Type>,
                                               unsigned)>
        instantiate;
    std::function<bool(Body &, const Substitution &, Body::Mode, unsigned,
                       unsigned &)>
        closeBody;
    auto closeType = [&](Type &type, const Substitution &bindings, Span span) {
      auto result = types.substitute(type, bindings, span);
      if (!result)
        return false;
      if (types.symbolic(*result))
        return types.fail("source.generic",
                          "unresolved type after static substitution", span);
      type = std::move(*result);
      return true;
    };
    auto closeService = [&](ServicePort &port, const Substitution &bindings) {
      if (!closeType(port.field, bindings, port.span))
        return false;
      port.contract = protocol::randomServiceContract(port.field.domain).str();
      return !port.contract.empty() ||
             types.fail("source.service",
                        "no installed random service for selected field",
                        port.span);
    };
    closeBody = [&](Body &body, const Substitution &bindings, Body::Mode mode,
                    unsigned depth, unsigned &height) {
      body.mode = mode;
      for (auto &service : body.services)
        if (!closeService(service, bindings))
          return false;
      for (auto &value : body.values) {
        if (!closeType(value.type, bindings, value.span))
          return false;
        if (!types.permissions(value.type, value.span))
          return false;
        if (mode != Body::Mode::Math &&
            !types.executableType(value.type, value.span))
          return false;
        if (mode == Body::Mode::Local)
          value.components.clear();
      }
      for (auto &op : body.operations) {
        if (!types.charge(1, op.span))
          return false;
        if (op.binding) {
          for (auto &argument : op.binding->arguments)
            if (!closeType(argument, bindings, op.span))
              return false;
          if (op.binding->target.component &&
              !closeType(*op.binding->target.component, bindings, op.span))
            return false;
          // Target and family retain their definition identities. The action
          // below selects instances; notation is never resolved at a caller.
        }
        if (auto *primitive = std::get_if<LocalPrimitive>(&op.action)) {
          for (auto &argument : primitive->staticArguments)
            if (!closeType(argument, bindings, op.span))
              return false;
          // A closed asset term writes its identity; the installed parameter
          // check below then sees an actual digest.
          for (auto &reference : primitive->assetReferences) {
            if (!closeType(reference.term, bindings, op.span))
              return false;
            if (reference.term.kind != Type::Kind::Asset ||
                reference.position >= primitive->parameters.size())
              return types.fail("source.asset-reference",
                                "closed kernel parameter is not an asset term",
                                op.span);
            primitive->parameters[reference.position] = reference.term.domain;
          }
          if (primitive->bindingArguments) {
            for (auto &argument : *primitive->bindingArguments)
              if (!closeType(argument, bindings, op.span))
                return false;
            auto signature = types.kernelSignature(
                primitive->contract, *primitive->bindingArguments,
                primitive->parameters, op.span, nullptr);
            if (!signature)
              return false;
            if (primitive->operands.size() != signature->inputs.size() ||
                op.results.size() != 1 ||
                !(body.values[op.results.front().index].type ==
                  signature->resultType()))
              return types.fail("source.kernel",
                                "specialized kernel ports differ", op.span);
            for (unsigned i = 0; i < primitive->operands.size(); ++i)
              if (!(body.values[primitive->operands[i].index].type ==
                    signature->inputs[i]))
                return types.fail("source.kernel",
                                  "specialized kernel input differs", op.span);
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
          auto intrinsic =
              llvm::find_if(intrinsics, [&](const auto &candidate) {
                return candidate.identity == math->identity;
              });
          if (intrinsic == intrinsics.end())
            return types.fail("source.intrinsic", "unknown mathematical hook",
                              op.span);
          auto signature = types.intrinsicSignature(nullptr, intrinsic->name,
                                                    math->staticArguments,
                                                    math->parameters, op.span);
          if (!signature)
            return false;
          if (math->operands.size() != signature->inputs.size() ||
              op.results.size() != 1 ||
              body.values[op.results.front().index].type !=
                  signature->resultType())
            return types.fail("source.intrinsic",
                              "specialized mathematical ports differ", op.span);
          for (unsigned i = 0; i < math->operands.size(); ++i)
            if (body.values[math->operands[i].index].type !=
                signature->inputs[i])
              return types.fail("source.intrinsic",
                                "specialized mathematical input differs",
                                op.span);
        }
        if (auto *exchange = std::get_if<Exchange>(&op.action)) {
          if (!types.ingress(body.values[exchange->payload.index].type,
                             op.span))
            return false;
        }
        if (auto *application = std::get_if<ProtocolApplication>(&op.action)) {
          for (auto &argument : application->arguments)
            if (!closeType(argument, bindings, op.span))
              return false;
          DeclarationId target = application->callee;
          if (auto origin = declarations[target.index].origin) {
            application->arguments = declarations[target.index].staticArguments;
            target = *origin;
          }
          auto instance =
              instantiate(target, application->arguments, depth + 1);
          if (!instance)
            return false;
          height = std::max(height, heights.at(instance->index) + 1);
          application->callee = *instance;
        } else if (auto *call = std::get_if<HelperCall>(&op.action)) {
          for (auto &arg : call->arguments)
            if (!closeType(arg, bindings, op.span))
              return false;
          DeclarationId target = call->callee;
          if (auto origin = declarations[target.index].origin) {
            call->arguments = declarations[target.index].staticArguments;
            target = *origin;
          }
          if (call->component) {
            if (!closeType(*call->component, bindings, op.span))
              return false;
            auto *component = types.typeDeclaration(*call->component);
            if (!component || component->kind != Declaration::Kind::Component)
              return types.fail("source.conformance",
                                "static dispatch did not select a component",
                                op.span);
            if (!types.charge(component->members.size(), op.span))
              return false;
            const auto name = declarations[target.index].name;
            auto found = llvm::find_if(component->members, [&](auto id) {
              return declarations[id.index].name == name;
            });
            if (found == component->members.end())
              return types.fail("source.conformance",
                                "static dispatch member missing", op.span);
            target = *found;
            call->arguments = call->component->arguments;
          }
          auto instance = instantiate(target, call->arguments, depth + 1);
          if (!instance)
            return false;
          height = std::max(height, heights.at(instance->index) + 1);
          call->callee = *instance;
        } else if (auto *bulk = std::get_if<BulkApplication>(&op.action)) {
          for (auto &arg : bulk->arguments)
            if (!closeType(arg, bindings, op.span))
              return false;
          DeclarationId target = bulk->callee;
          if (auto origin = declarations[target.index].origin) {
            bulk->arguments = declarations[target.index].staticArguments;
            target = *origin;
          }
          auto instance = instantiate(target, bulk->arguments, depth + 1);
          if (!instance)
            return false;
          height = std::max(height, heights.at(instance->index) + 1);
          bulk->callee = *instance;
          // Selection must keep one scalar field and the written row modes.
          const auto &helper = declarations[instance->index];
          auto field = helper.outputs.size() == 1 ? helper.outputs.front().type
                                                  : Type(Type::Kind::Unit);
          auto rows = builtinType("vector", {field});
          bool exact = rows && field.kind == Type::Kind::Field &&
                       helper.kind == Declaration::Kind::Math &&
                       helper.inputs.size() == bulk->operands.size() &&
                       bulk->mapped.size() == bulk->operands.size() &&
                       op.results.size() == 1 &&
                       body.values[op.results.front().index].type == *rows;
          for (unsigned i = 0; exact && i < bulk->operands.size(); ++i)
            exact = helper.inputs[i].type == field &&
                    body.values[bulk->operands[i].index].type ==
                        (bulk->mapped[i] ? *rows : field);
          if (!rows)
            consumeError(rows.takeError());
          if (!exact)
            return types.fail("source.map", "specialized map ports differ",
                              op.span);
        } else if (auto *query = std::get_if<ServiceQuery>(&op.action);
                   query && query->bound) {
          Type bound(Type::Kind::Natural);
          bound.dimension = *query->bound;
          bound.symbolic = !query->bound->isClosed();
          if (!closeType(bound, bindings, op.span))
            return false;
          if (!protocol::uniformIndexBound(bound.dimension.closedValue()))
            return types.fail(
                "source.service",
                "selected index domain must be a power of two no greater "
                "than 2^63",
                op.span);
          query->bound = bound.dimension;
        } else if (auto *repeat = std::get_if<ProtocolRepeat>(&op.action)) {
          Type maximum(Type::Kind::Natural);
          maximum.dimension = repeat->maximum;
          maximum.symbolic = !repeat->maximum.isClosed();
          if (!closeType(maximum, bindings, op.span))
            return false;
          if (maximum.dimension.closedValue() > 1048576)
            return types.fail("source.bound",
                              "selected repeat maximum exceeds installed limit",
                              op.span);
          repeat->maximum = maximum.dimension;
          auto copy = std::make_shared<Body>(*repeat->region);
          if (!closeBody(*copy, bindings, Body::Mode::Protocol, depth, height))
            return false;
          repeat->region = std::move(copy);
        } else if (auto *control = std::get_if<LocalControl>(&op.action)) {
          for (auto &region : control->regions) {
            auto copy = std::make_shared<Body>(*region);
            if (!closeBody(*copy, bindings, Body::Mode::Local, depth, height))
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
                      unsigned depth) -> std::optional<DeclarationId> {
      const auto &source = declarations[origin.index];
      if (depth > work.limits.callDepth) {
        types.fail("source.limit", "closed call depth limit exceeded",
                   source.span);
        return {};
      }
      auto mode = source.kind == Declaration::Kind::Protocol
                      ? Body::Mode::Protocol
                  : source.kind == Declaration::Kind::Local ? Body::Mode::Local
                                                            : Body::Mode::Math;
      if ((!source.body && source.kind != Declaration::Kind::Relation) ||
          source.abstract) {
        types.fail("source.call", "cannot specialize an abstract callable",
                   source.span);
        return {};
      }
      if (!types.checkArguments(source, args, source.span))
        return {};
      std::string key;
      detail::frame(key, source.qualifiedName);
      for (auto &arg : args) {
        if (types.symbolic(arg)) {
          types.fail("source.generic",
                     "entry specialization requires closed static arguments",
                     source.span);
          return {};
        }
        if (!types.chargeType(arg, source.span))
          return {};
        detail::frame(key, typeIdentity(arg));
      }
      auto known = instances.find(key);
      if (known != instances.end()) {
        if (depth - 1 + heights.at(known->second.index) >
            work.limits.callDepth) {
          types.fail("source.limit", "closed call depth limit exceeded",
                     source.span);
          return {};
        }
        return known->second;
      }
      if (!active.insert(key).second) {
        types.fail("source.cycle", "recursive static instantiation",
                   source.span);
        return {};
      }
      if (++count > work.limits.instances || count > work.limits.declarations ||
          !types.charge(key.size() + 1, source.span)) {
        if (!types.diagnostic)
          types.fail("source.limit", "static instance limit exceeded",
                     source.span);
        return {};
      }
      // Charge the snapshot before allocating it. Recursive instances can grow
      // the declaration vector, so no reference into that vector crosses
      // closeBody.
      for (const auto &role : source.roles)
        if (!types.charge(role.size() + 1, source.span))
          return {};
      for (auto *ports : {&source.inputs, &source.outputs})
        for (const auto &port : *ports)
          if (!types.charge(port.name.size() + port.roles.size() + 1,
                            port.span) ||
              !types.chargeType(port.type, port.span))
            return {};
      for (const auto &service : source.services)
        if (!types.chargeType(service.field, service.span))
          return {};
      if (source.body && !chargeBodySnapshot(types, *source.body, source.span))
        return {};
      if (source.relation &&
          !types.charge(source.relation->purposes.size() +
                            source.relation->externalKind.size() +
                            source.relation->key.size() +
                            source.relation->revision.size() + 1,
                        source.span))
        return {};
      for (const auto &clause : source.specifications) {
        if (!types.charge(clause.name.size() + 1, clause.span))
          return {};
        for (const auto *subject :
             {&clause.subject, clause.residual ? &*clause.residual : nullptr}) {
          if (!subject)
            continue;
          for (const auto &argument : subject->arguments)
            if (!types.chargeType(argument, subject->span))
              return {};
          for (const auto &operand : subject->operands)
            if (!types.charge(operand.path.size() + 1, operand.span))
              return {};
        }
        if (clause.decision && !types.charge(clause.decision->path.size() + 1,
                                             clause.decision->span))
          return {};
      }
      Declaration result = source;
      DeclarationId id{uint32_t(declarations.size())};
      result.id = id;
      result.origin = origin;
      result.members.clear();
      result.staticArguments.assign(args.begin(), args.end());
      // Native participant carriers bound identifiers to 128 bytes. Reuse the
      // instance key for long declaration paths instead of narrowing source
      // names.
      if (!args.empty() || result.symbol.size() > 128)
        result.symbol = "zkl_" + detail::digest(key);
      if (result.symbol.size() > work.limits.symbolBytes) {
        types.fail("source.limit", "specialized symbol exceeds byte limit",
                   result.span);
        return {};
      }
      auto [symbol, inserted] = symbolKeys.emplace(result.symbol, key);
      if (!inserted && symbol->second != key) {
        types.fail("source.symbol",
                   "distinct instance keys have the same symbol", result.span);
        return {};
      }
      declarations.push_back(result);
      auto bindings = types.substitution(result, args);
      if (result.parent && declarations[result.parent->index].kind ==
                               Declaration::Kind::Component) {
        auto &parent = declarations[result.parent->index];
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
      if (result.primitive)
        for (auto &argument : result.primitive->arguments)
          if (!closeType(argument, bindings, result.span))
            return {};
      for (auto &service : result.services)
        if (!closeService(service, bindings))
          return {};
      auto closeSubject = [&](RelationApplication &subject) {
        for (auto &argument : subject.arguments)
          if (!closeType(argument, bindings, subject.span))
            return false;
        auto selected = instantiate(subject.relation, subject.arguments, 1);
        if (!selected)
          return false;
        subject.relation = *selected;
        const auto &relation = declarations[selected->index];
        for (unsigned i = 0; i < subject.operands.size(); ++i) {
          auto type = types.selectedType(result, subject.operands[i]);
          if (!type)
            return false;
          if (*type != relation.inputs[i].type)
            return types.fail("source.specification",
                              "closed relation operand type differs",
                              subject.span);
        }
        return true;
      };
      for (auto &clause : result.specifications) {
        if (!closeSubject(clause.subject) ||
            (clause.residual && !closeSubject(*clause.residual)))
          return {};
        if (clause.decision && !types.selectedType(result, *clause.decision))
          return {};
      }
      unsigned height = 1;
      if (result.body) {
        assert(result.body->mode == mode && "declaration body mode changed");
        auto body = std::make_shared<Body>(*result.body);
        if (!closeBody(*body, bindings, mode, depth, height))
          return {};
        if (result.kind == Declaration::Kind::Math ||
            result.kind == Declaration::Kind::Relation)
          for (const auto &value : body->values)
            if (!types.mathematicalData(value.type, value.span))
              return {};
        result.body = std::move(body);
      }
      result.parameters.clear();
      result.bounds.clear();
      result.permissionBounds.clear();
      result.capabilityBounds.clear();
      declarations[id.index] = std::move(result);
      heights.emplace(id.index, height);
      instances.emplace(key, id);
      active.erase(key);
      return id;
    };
    auto target = declarations[selected.index].target;
    auto args = declarations[selected.index].staticArguments;
    if (!target)
      return types.fail("source.entry", "Entry has no checked target",
                        declarations[selected.index].span);
    auto instance = instantiate(*target, args, 1);
    if (!instance)
      return false;
    if (!types.checkProofEntry(declarations[selected.index],
                               declarations[instance->index]))
      return false;
    const auto &inputs = declarations[instance->index].inputs;
    for (unsigned i = 0; i < inputs.size(); ++i) {
      const auto &port = inputs[i];
      // Whole key ports use Entry setup initialization. Exact setup coverage is
      // checked from the closed layout before closeEntry publishes its handle.
      bool key = port.type.kind == Type::Kind::Builtin &&
                 (port.type.domain == "prover_key" ||
                  port.type.domain == "verifier_key");
      bool initialized = llvm::any_of(
          declarations[selected.index].setups, [&](const SetupSlot &slot) {
            return llvm::any_of(slot.inputs, [&](const EntryInput &input) {
              return input.port == i && input.path.empty();
            });
          });
      if (key && initialized) {
        if (!types.executableType(port.type, port.span))
          return false;
      } else if (!types.ingress(port.type, port.span))
        return false;
    }
    declarations[selected.index].target = *instance;
    for (unsigned i = 0; i < templates; ++i)
      declarations[i].body.reset();
    return true;
  };
  return close() ? Error::success() : types.takeError();
}
} // namespace zkc::language::detail
