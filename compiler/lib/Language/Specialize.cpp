#include "BodyMapping.h"
#include "BodySummary.h"
#include "ClosureInputs.h"
#include "DataRequirements.h"
#include "DomainClosure.h"
#include "Effects.h"
#include "FiniteContracts.h"
#include "OracleDefinitions.h"
#include "Semantics.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/SourceTerms.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
namespace {
// Charge nested payloads before specialization copies immutable template
// bodies.
bool chargeBodySnapshot(Semantics &types, const Body &body, Span span) {
  if (!types.charge(body.operations.size() + body.values.size() +
                        body.results.size() + body.expressionValues.size() +
                        body.stopReason.size() +
                        body.effects.dependencies.size() + 1,
                    span))
    return false;
  for (const auto &value : body.values)
    if (!types.charge(value.components.size(), value.span) ||
        !types.chargeType(value.type, value.span))
      return false;
  for (const auto &requirement : body.formationRequirements)
    if (!types.charge(requirement.size() + 1, span))
      return false;
  for (const auto &binding : body.scopedBindings) {
    if (!types.charge(binding.captures.size() + binding.scopedCaptures.size() +
                          binding.domainCaptures.size() + 1,
                      binding.span) ||
        !types.chargeType(binding.signature.result, binding.span))
      return false;
    for (const auto &input : binding.signature.inputs)
      if (!types.chargeType(input, binding.span))
        return false;
    // The immutable nested Body is charged when its helper is instantiated.
    // Captured-place metadata is copied here with the containing binding.
    if (binding.computation)
      for (const auto &capture : binding.computation->captures)
        if (!types.charge(capture.path.size() + 1, capture.firstUse) ||
            !types.chargeType(capture.type, capture.firstUse))
          return false;
  }
  for (const auto &domain : body.domainBindings) {
    if (!types.charge(domain.operands.size() + domain.children.size() +
                          domain.arguments.size() +
                          domain.argumentOrder.size() + 1,
                      domain.span) ||
        !types.chargeType(domain.item, domain.span))
      return false;
    for (const auto &argument : domain.arguments)
      if (!types.chargeType(argument, domain.span))
        return false;
    if (domain.factory && domain.factory->module &&
        !types.chargeType(*domain.factory->module, domain.span))
      return false;
  }
  for (const auto &service : body.services)
    if (!types.charge(service.name.size() + service.contract.size() + 1,
                      service.span) ||
        !types.chargeType(service.field, service.span))
      return false;
  for (const auto &op : body.operations) {
    if (!types.charge(op.results.size() + (op.site ? op.site->size() : 0),
                      op.span))
      return false;
    if (op.binding) {
      const auto &binding = *op.binding;
      if (!types.charge(binding.operands.size() + binding.symbol.size() +
                            binding.argumentOrder.size() +
                            binding.scopedArguments.size() +
                            binding.domainArguments.size() + 1,
                        op.span))
        return false;
      if (binding.notation &&
          !types.charge(binding.notation->symbol.size() +
                            binding.notation->closing.size() + 1,
                        op.span))
        return false;
      for (const auto &member : binding.family)
        if (!types.charge(member.size() + 1, op.span))
          return false;
      for (const auto &arg : binding.arguments)
        if (!types.chargeType(arg, op.span))
          return false;
      if (binding.target.module &&
          !types.chargeType(*binding.target.module, op.span))
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
    } else if (const auto *call = std::get_if<HelperCall>(&op.action)) {
      if (!types.charge(call->operands.size() + call->arguments.size() +
                            call->scopedArguments.size() +
                            call->domainArguments.size() + 1,
                        op.span))
        return false;
      for (const auto &argument : call->arguments)
        if (!types.chargeType(argument, op.span))
          return false;
      if (call->module && !types.chargeType(*call->module, op.span))
        return false;
    } else if (const auto *call =
                   std::get_if<OracleInstantiation>(&op.action)) {
      if (!types.charge(call->operands.size() + call->arguments.size() +
                            call->receivers.size() + 1,
                        op.span))
        return false;
      for (const auto &argument : call->arguments)
        if (!types.chargeType(argument, op.span))
          return false;
      if (call->module && !types.chargeType(*call->module, op.span))
        return false;
    } else if (const auto *call = std::get_if<HostInvocation>(&op.action)) {
      if (!types.charge(call->operands.size() + call->arguments.size() + 1,
                        op.span))
        return false;
      for (const auto &argument : call->arguments)
        if (!types.chargeType(argument, op.span))
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
      if (!types.charge(control->operands.size() + control->regions.size() +
                            control->domainArguments.size(),
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
                       DeclarationId selected,
                       std::optional<HostInvocation::Kind> operation) {
  Semantics types(declarations, assets, work);
  auto close = [&]() -> bool {
    const unsigned templates = declarations.size();
    std::map<std::string, DeclarationId> instances;
    std::map<unsigned, unsigned> heights;
    std::set<std::string> active;
    std::map<std::string, std::string> symbolKeys;
    uint64_t count = 0;
    struct Environment {
      DeclarationId helper;
      std::vector<ValueId> captures;
    };
    std::map<std::pair<unsigned, unsigned>, DeclarationId> scopedTemplates;
    std::vector<DeclarationId> generatedTemplates;
    std::function<std::optional<DeclarationId>(
        DeclarationId, ArrayRef<Type>, unsigned, ArrayRef<DeclarationId>,
        ArrayRef<std::shared_ptr<const DomainShape>>, const ClosureLayout &)>
        instantiate;
    std::function<bool(Body &, const Substitution &, Body::Mode, unsigned,
                       unsigned &, const std::vector<Environment> &,
                       ArrayRef<DomainEnvironment>)>
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
    auto closeCallable = [&](DeclarationId &target, std::optional<Type> &module,
                             std::vector<Type> &arguments,
                             const Substitution &bindings, Span span) {
      for (auto &argument : arguments)
        if (!closeType(argument, bindings, span))
          return false;
      if (auto origin = declarations[target.index].origin) {
        arguments = declarations[target.index].staticArguments;
        target = *origin;
      }
      if (!module)
        return true;
      if (!closeType(*module, bindings, span))
        return false;
      const auto *owner = types.typeDeclaration(*module);
      if (!owner || owner->kind != Declaration::Kind::Module)
        return types.fail("source.conformance",
                          "static dispatch did not select a module", span);
      if (!types.charge(owner->members.size(), span))
        return false;
      const auto name = declarations[target.index].name;
      auto found = llvm::find_if(owner->members, [&](auto id) {
        return declarations[id.index].name == name;
      });
      if (found == owner->members.end())
        return types.fail("source.conformance",
                          "static dispatch member missing", span);
      target = *found;
      arguments = module->arguments;
      return true;
    };
    auto callableSubstitution = [&](const Declaration &source,
                                    ArrayRef<Type> args) {
      auto bindings = types.substitution(source, args);
      auto lexicalParent = source.parent;
      while (lexicalParent && declarations[lexicalParent->index].kind !=
                                  Declaration::Kind::Module)
        lexicalParent = declarations[lexicalParent->index].parent;
      if (lexicalParent) {
        const auto &parent = declarations[lexicalParent->index];
        Type self(Type::Kind::Module, parent.qualifiedName);
        self.arguments.assign(args.begin(),
                              args.begin() + parent.parameters.size());
        if (parent.implementation)
          bindings.emplace("self:" + parent.implementation->domain, self);
      }
      return bindings;
    };
    closeBody = [&](Body &body, const Substitution &bindings, Body::Mode mode,
                    unsigned depth, unsigned &height,
                    const std::vector<Environment> &environment,
                    ArrayRef<DomainEnvironment> domains) {
      body.mode = mode;
      ValueOrigins bodyOrigins(types, body);
      for (auto &service : body.services)
        if (!closeService(service, bindings))
          return false;
      for (auto &value : body.values) {
        if (!closeType(value.type, bindings, value.span))
          return false;
        if (!types.permissions(value.type, value.span))
          return false;
        if (mode != Body::Mode::Math && mode != Body::Mode::Oracle &&
            !(mode == Body::Mode::Protocol
                  ? types.protocolValue(value.type, value.span)
                  : types.executableType(value.type, value.span)))
          return false;
        if (mode == Body::Mode::Local)
          value.components.clear();
      }
      std::vector<std::optional<DomainEnvironment>> resolvedDomains(
          body.domainBindings.size());
      auto resolveDomain =
          [&](unsigned index) -> std::optional<DomainEnvironment> {
        if (index >= resolvedDomains.size()) {
          types.fail("source.finite-domain", "domain edge outside body", {});
          return {};
        }
        if (!resolvedDomains[index])
          resolvedDomains[index] = closeDomain(types, declarations, body, index,
                                               bindings, domains, &bodyOrigins);
        return resolvedDomains[index];
      };
      std::vector<std::optional<Environment>> resolved(
          body.scopedBindings.size());
      std::function<std::optional<Environment>(unsigned, unsigned)>
          resolveScoped =
              [&](unsigned index,
                  unsigned nestedDepth) -> std::optional<Environment> {
        if (index >= body.scopedBindings.size() ||
            nestedDepth > work.limits.callDepth) {
          types.fail("source.limit", "scoped environment expansion limit",
                     body.values.empty() ? Span{} : body.values.front().span);
          return {};
        }
        if (resolved[index])
          return resolved[index];
        const auto &binding = body.scopedBindings[index];
        if (!types.charge(binding.captures.size() +
                              binding.scopedCaptures.size() + 1,
                          binding.span))
          return {};
        if (binding.parameter) {
          if (*binding.parameter >= environment.size()) {
            types.fail("source.scoped", "unbound scoped formal", binding.span);
            return {};
          }
          return resolved[index] = environment[*binding.parameter];
        }
        const auto &computation = *binding.computation;
        std::vector<DeclarationId> selected;
        std::vector<ValueId> hiddenCaptures;
        for (auto capture : binding.scopedCaptures) {
          auto value = resolveScoped(capture, nestedDepth + 1);
          if (!value)
            return {};
          selected.push_back(value->helper);
          hiddenCaptures.insert(hiddenCaptures.end(), value->captures.begin(),
                                value->captures.end());
        }
        std::vector<std::shared_ptr<const DomainShape>> selectedDomains;
        for (auto capture : binding.domainCaptures) {
          auto domain = resolveDomain(capture);
          if (!domain)
            return {};
          selectedDomains.push_back(domain->shape);
          hiddenCaptures.insert(hiddenCaptures.end(), domain->operands.begin(),
                                domain->operands.end());
        }
        auto identity = std::make_pair(computation.lexicalOwner.index,
                                       computation.expression);
        auto found = scopedTemplates.find(identity);
        DeclarationId source;
        if (found == scopedTemplates.end()) {
          Declaration helper = declarations[computation.lexicalOwner.index];
          helper.id = {uint32_t(declarations.size())};
          source = helper.id;
          helper.parent = computation.lexicalOwner;
          helper.kind =
              computation.signature.mode == ScopedSignature::Mode::Math
                  ? Declaration::Kind::Math
                  : Declaration::Kind::Local;
          helper.name =
              "scoped<" + std::to_string(computation.expression) + ">";
          helper.qualifiedName += "::" + helper.name;
          helper.symbol = "zks_" + digest(helper.qualifiedName);
          helper.isPublic = false;
          helper.anonymous = true;
          helper.abstract = false;
          helper.primitive.reset();
          helper.specifications.clear();
          helper.specificationBlock.reset();
          helper.relation.reset();
          helper.target.reset();
          helper.completes = false;
          helper.scopedOrigin =
              std::make_pair(computation.lexicalOwner, computation.expression);
          helper.roles.clear();
          helper.services.clear();
          helper.members.clear();
          helper.inputs.clear();
          helper.outputs.clear();
          helper.inputOrder.clear();
          helper.scopedInputs.clear();
          helper.domainInputs.clear();
          helper.domainArguments.clear();
          helper.domainResult.reset();
          helper.domainDefinition.reset();
          helper.finiteDefinition.reset();
          helper.dataPreconditions.clear();
          helper.body = computation.body;
          helper.effectAllowance =
              EffectSummary{computation.signature.allowance};
          for (unsigned i = 0; i < helper.body->inputs; ++i)
            helper.inputs.push_back({"input" + std::to_string(i),
                                     helper.body->values[i].type,
                                     {},
                                     binding.span});
          helper.outputs.push_back(
              {"result", computation.signature.result, {}, binding.span});
          for (const auto &capture : helper.body->scopedBindings)
            if (capture.parameter)
              helper.scopedInputs.push_back(
                  {"body" + std::to_string(*capture.parameter),
                   capture.signature, capture.span});
          for (const auto &capture : helper.body->domainBindings)
            if (capture.parameter)
              helper.domainInputs.push_back(
                  {"domain" + std::to_string(*capture.parameter), capture.item,
                   capture.span});
          declarations.push_back(std::move(helper));
          generatedTemplates.push_back(source);
          scopedTemplates.emplace(identity, source);
        } else
          source = found->second;
        std::vector<Type> arguments;
        for (const auto &parameter : declarations[source.index].parameters) {
          auto argument = types.substitute(parameterType(parameter), bindings,
                                           binding.span);
          if (!argument)
            return {};
          arguments.push_back(*argument);
        }
        std::vector<std::optional<ValueId>> authored(
            computation.signature.inputs.size());
        for (auto capture : binding.captures)
          authored.push_back(capture);
        auto inputs = closeInputs(types, body, authored, hiddenCaptures,
                                  binding.span, &bodyOrigins);
        if (!inputs)
          return {};
        auto helper = instantiate(source, arguments, depth + 1, selected,
                                  selectedDomains, inputs->layout);
        if (!helper)
          return {};
        height = std::max(height, heights.at(helper->index) + 1);
        std::vector<ValueId> operands;
        for (auto value : ArrayRef(inputs->operands)
                              .drop_front(computation.signature.inputs.size()))
          operands.push_back(*value);
        return resolved[index] = Environment{*helper, std::move(operands)};
      };
      // Even unused callback bodies are closed and checked. Creating a static
      // helper here does not execute the callback or move its capture
      // snapshots.
      for (unsigned i = 0; i < body.scopedBindings.size(); ++i)
        if (!resolveScoped(i, 1))
          return false;
      for (auto &op : body.operations) {
        if (std::holds_alternative<RoleAssembly>(op.action) &&
            !types.sharedData(body.values[op.results.front().index].type,
                              op.span, nullptr))
          return false;
        if (auto *invoke = std::get_if<ScopedInvoke>(&op.action)) {
          auto selected = resolveScoped(invoke->binding, 1);
          if (!selected)
            return false;
          auto operands = invoke->operands;
          operands.insert(operands.end(), selected->captures.begin(),
                          selected->captures.end());
          op.action =
              HelperCall{selected->helper, std::move(operands), {}, {}, {}, {}};
          continue;
        }
        if (const auto *finite = std::get_if<FiniteApplication>(&op.action)) {
          auto domain = resolveDomain(finite->domain);
          auto step = resolveScoped(finite->body, 1);
          if (!domain || !step)
            return false;
          std::optional<FiniteCallback> predicate;
          if (finite->predicate) {
            auto selected = resolveScoped(*finite->predicate, 1);
            if (!selected)
              return false;
            predicate = FiniteCallback{selected->helper, selected->captures};
          }
          op.action = FiniteComputation{finite->kind,
                                        domain->shape,
                                        domain->operands,
                                        finite->operands,
                                        {step->helper, step->captures},
                                        std::move(predicate)};
          continue;
        }
        if (!types.charge(1, op.span))
          return false;
        if (op.binding) {
          for (auto &argument : op.binding->arguments)
            if (!closeType(argument, bindings, op.span))
              return false;
          if (op.binding->target.module &&
              !closeType(*op.binding->target.module, bindings, op.span))
            return false;
          // Target and family retain their definition identities. The action
          // below selects instances; notation is never resolved at a caller.
        }
        if (auto *invocation = std::get_if<HostInvocation>(&op.action)) {
          if (body.stage != Body::Stage::Host)
            return types.fail("source.stage",
                              "Host invocation outside Host body", op.span);
          for (auto &argument : invocation->arguments)
            if (!closeType(argument, bindings, op.span))
              return false;
          for (auto value : invocation->operands)
            if (!types.hostData(body.values[value.index].type, op.span))
              return false;
          for (auto value : op.results)
            if (!types.hostData(body.values[value.index].type, op.span))
              return false;
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
        if (auto *send = std::get_if<OracleSend>(&op.action)) {
          if (send->maximum) {
            Type bound(Type::Kind::Natural);
            bound.dimension = *send->maximum;
            bound.symbolic = !bound.dimension.isClosed();
            if (!closeType(bound, bindings, op.span))
              return false;
            send->maximum = bound.dimension;
          }
          const auto &kind =
              body.values[op.results.front().index].type.arguments.front();
          if ((kind.arguments.size() == 2) == send->maximum.has_value())
            return types.fail("source.oracle-shape",
                              "closed oracle send bound differs from kind",
                              op.span);
        }
        if (auto *construction = std::get_if<OracleInstantiation>(&op.action)) {
          DeclarationId target = construction->callee;
          if (!closeCallable(target, construction->module,
                             construction->arguments, bindings, op.span))
            return false;
          auto instance = instantiate(target, construction->arguments,
                                      depth + 1, {}, {}, {});
          if (!instance)
            return false;
          construction->callee = *instance;
          height = std::max(height, heights.at(instance->index) + 1);
        } else if (auto *application =
                       std::get_if<ProtocolApplication>(&op.action)) {
          for (auto &argument : application->arguments)
            if (!closeType(argument, bindings, op.span))
              return false;
          DeclarationId target = application->callee;
          if (auto origin = declarations[target.index].origin) {
            application->arguments = declarations[target.index].staticArguments;
            target = *origin;
          }
          auto instance = instantiate(target, application->arguments, depth + 1,
                                      {}, {}, {});
          if (!instance)
            return false;
          height = std::max(height, heights.at(instance->index) + 1);
          application->callee = *instance;
        } else if (auto *call = std::get_if<HelperCall>(&op.action)) {
          DeclarationId target = call->callee;
          if (!closeCallable(target, call->module, call->arguments, bindings,
                             op.span))
            return false;
          if ((body.mode == Body::Mode::Math ||
               body.mode == Body::Mode::Oracle) &&
              declarations[target.index].kind == Declaration::Kind::Math &&
              declarations[target.index].finiteDefinition &&
              !declarations[target.index].abstract) {
            // Registered finite definitions have one canonical application.
            // Keep it at this occurrence so actual endpoints and container
            // facts remain available. Callback instances retain their ABI.
            const auto &source = declarations[target.index];
            if (!types.checkArguments(source, call->arguments, op.span))
              return false;
            if (!source.body || source.body->operations.size() != 1 ||
                source.domainInputs.size() != 1 ||
                call->domainArguments.size() != 1 ||
                call->scopedArguments.size() != source.scopedInputs.size() ||
                call->operands.size() != source.inputs.size() ||
                op.results.size() != source.outputs.size())
              return types.fail("source.finite", "invalid finite definition",
                                op.span);
            auto selectedBindings =
                callableSubstitution(source, call->arguments);
            auto matches = [&](Type expected, ValueId actual) {
              return closeType(expected, selectedBindings, op.span) &&
                     (expected == body.values[actual.index].type ||
                      types.fail("source.finite",
                                 "closed finite signature differs", op.span));
            };
            for (unsigned i = 0; i < source.inputs.size(); ++i)
              if (!matches(source.inputs[i].type, call->operands[i]))
                return false;
            for (unsigned i = 0; i < source.outputs.size(); ++i)
              if (!matches(source.outputs[i].type, op.results[i]))
                return false;
            auto item = source.domainInputs.front().item;
            if (!closeType(item, selectedBindings, op.span))
              return false;
            std::vector<ScopedSignature> signatures;
            for (const auto &parameter : source.scopedInputs) {
              auto signature = parameter.signature;
              for (auto &input : signature.inputs)
                if (!closeType(input, selectedBindings, op.span))
                  return false;
              if (!closeType(signature.result, selectedBindings, op.span))
                return false;
              signatures.push_back(std::move(signature));
            }
            auto callbackMatches = [&](unsigned index,
                                       const Environment &selected) {
              const auto &signature = signatures[index];
              const auto &helper = declarations[selected.helper.index];
              if (helper.inputs.size() !=
                      signature.inputs.size() + selected.captures.size() ||
                  helper.outputs.size() != 1 ||
                  helper.outputs.front().type != signature.result)
                return types.fail("source.finite",
                                  "closed finite callback signature differs",
                                  op.span);
              for (unsigned i = 0; i < signature.inputs.size(); ++i)
                if (helper.inputs[i].type != signature.inputs[i])
                  return types.fail("source.finite",
                                    "closed finite callback signature differs",
                                    op.span);
              return true;
            };
            const auto *application = std::get_if<FiniteApplication>(
                &source.body->operations.front().action);
            if (!application || application->domain != 0 ||
                application->body >= call->scopedArguments.size() ||
                (application->predicate &&
                 *application->predicate >= call->scopedArguments.size()))
              return types.fail("source.finite", "finite call mapping differs",
                                op.span);
            // Resolving a callback can grow declarations; keep no borrowed
            // declaration or body reference across that operation.
            const auto finite = *application;
            auto domain = resolveDomain(call->domainArguments.front());
            if (!domain)
              return false;
            if (item != domain->shape->nodes[domain->shape->result].item)
              return types.fail("source.finite-domain",
                                "closed domain item type differs", op.span);
            auto step = resolveScoped(call->scopedArguments[finite.body], 1);
            if (!step || !callbackMatches(finite.body, *step))
              return false;
            std::optional<FiniteCallback> predicate;
            if (finite.predicate) {
              auto selected =
                  resolveScoped(call->scopedArguments[*finite.predicate], 1);
              if (!selected || !callbackMatches(*finite.predicate, *selected))
                return false;
              predicate = FiniteCallback{selected->helper, selected->captures};
            }
            std::vector<ValueId> operands;
            for (auto operand : finite.operands) {
              if (!types.charge(1, op.span) ||
                  operand.index >= call->operands.size())
                return types.diagnostic
                           ? false
                           : types.fail("source.finite",
                                        "finite data mapping differs", op.span);
              operands.push_back(call->operands[operand.index]);
            }
            op.action = FiniteComputation{finite.kind,
                                          domain->shape,
                                          domain->operands,
                                          std::move(operands),
                                          {step->helper, step->captures},
                                          std::move(predicate)};
            continue;
          }
          std::vector<DeclarationId> selected;
          std::vector<ValueId> hiddenCaptures;
          for (auto argument : call->scopedArguments) {
            auto value = resolveScoped(argument, 1);
            if (!value)
              return false;
            selected.push_back(value->helper);
            hiddenCaptures.insert(hiddenCaptures.end(), value->captures.begin(),
                                  value->captures.end());
          }
          std::vector<std::shared_ptr<const DomainShape>> selectedDomains;
          for (auto argument : call->domainArguments) {
            auto domain = resolveDomain(argument);
            if (!domain)
              return false;
            selectedDomains.push_back(domain->shape);
            hiddenCaptures.insert(hiddenCaptures.end(),
                                  domain->operands.begin(),
                                  domain->operands.end());
          }
          ClosureLayout layout;
          if (!selected.empty() || !selectedDomains.empty()) {
            std::vector<std::optional<ValueId>> authored;
            for (auto operand : call->operands)
              authored.push_back(operand);
            auto inputs = closeInputs(types, body, authored, hiddenCaptures,
                                      op.span, &bodyOrigins);
            if (!inputs)
              return false;
            layout = std::move(inputs->layout);
            call->operands.clear();
            for (auto operand : inputs->operands)
              call->operands.push_back(*operand);
          }
          auto instance = instantiate(target, call->arguments, depth + 1,
                                      selected, selectedDomains, layout);
          call->scopedArguments.clear();
          call->domainArguments.clear();
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
          auto instance =
              instantiate(target, bulk->arguments, depth + 1, {}, {}, {});
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
                "selected index domain must be a positive u64 natural",
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
          std::vector<std::optional<ValueId>> authored(1 +
                                                       repeat->carried.size());
          for (auto capture : repeat->captures)
            authored.push_back(capture);
          auto inputs =
              closeInputs(types, body, authored, {}, op.span, &bodyOrigins);
          if (!inputs || repeat->region->inputs != authored.size())
            return types.diagnostic
                       ? false
                       : types.fail("source.closure-inputs",
                                    "protocol region input coverage differs",
                                    op.span);
          repeat->regionLayout = inputs->layout;
          auto copy = std::make_shared<Body>(*repeat->region);
          mapBodyValues(*copy, [&](ValueId value) {
            return ValueId{value.index < inputs->layout.inputs.size()
                               ? inputs->layout.inputs[value.index]
                               : value.index};
          });
          if (!closeBody(*copy, bindings, Body::Mode::Protocol, depth, height,
                         {}, {}))
            return false;
          repeat->region = std::move(copy);
        } else if (auto *control = std::get_if<LocalControl>(&op.action)) {
          std::vector<ValueId> captures;
          for (const auto &entry : environment)
            captures.insert(captures.end(), entry.captures.begin(),
                            entry.captures.end());
          std::vector<DomainEnvironment> selectedDomains;
          for (auto argument : control->domainArguments) {
            auto domain = resolveDomain(argument);
            if (!domain)
              return false;
            captures.insert(captures.end(), domain->operands.begin(),
                            domain->operands.end());
            control->domainShapes.push_back(domain->shape);
            selectedDomains.push_back(std::move(*domain));
          }
          const bool loop = control->kind == LocalControl::Kind::For;
          const unsigned header = loop ? 2 : 1;
          if (control->operands.size() < header)
            return types.fail("source.closure-inputs",
                              "control operand coverage differs", op.span);
          const unsigned forwarded = control->operands.size() - header;
          std::optional<std::vector<ValueId>> extraOperands;
          for (auto &region : control->regions) {
            if (region->inputs < forwarded ||
                (loop && (region->inputs != forwarded + 1 ||
                          control->carried > forwarded)))
              return types.fail("source.closure-inputs",
                                "control input coverage differs", op.span);
            const unsigned prefix = region->inputs - forwarded;
            std::vector<std::optional<ValueId>> authored(prefix);
            for (unsigned i = 0; i < forwarded; ++i)
              authored.push_back(
                  loop && i < control->carried
                      ? std::nullopt
                      : std::optional<ValueId>(control->operands[header + i]));
            auto selected = closeInputs(types, body, authored, captures,
                                        op.span, &bodyOrigins);
            if (!selected)
              return false;
            std::vector<ValueId> extras;
            std::vector<Value> hidden;
            for (auto input :
                 ArrayRef(selected->operands).drop_front(region->inputs)) {
              if (!input)
                return types.fail("source.closure-inputs",
                                  "unbound control capture", op.span);
              extras.push_back(*input);
              hidden.push_back(body.values[input->index]);
            }
            if (extraOperands &&
                (extraOperands->size() != extras.size() ||
                 !std::equal(extraOperands->begin(), extraOperands->end(),
                             extras.begin(), [](ValueId a, ValueId b) {
                               return a.index == b.index;
                             })))
              return types.fail("source.closure-inputs",
                                "control arms disagree on captures", op.span);
            extraOperands = std::move(extras);
            auto copy = std::make_shared<Body>(*region);
            auto inputs = appendBodyInputs(*copy, hidden);
            mapBodyValues(*copy, [&](ValueId value) {
              return ValueId{value.index < selected->layout.inputs.size()
                                 ? selected->layout.inputs[value.index]
                                 : value.index};
            });
            // MLIR's region interface forwards each physical invariant port.
            // Its yield suffix is distinct from logical uses inside the body.
            if (loop && !copy->stopped) {
              unsigned invariants = forwarded - control->carried;
              if (copy->results.size() < invariants)
                return types.fail("source.closure-inputs",
                                  "loop invariant results differ", op.span);
              for (unsigned i = 0; i < invariants; ++i) {
                if (region->results[region->results.size() - invariants + i]
                        .index != region->inputs - invariants + i)
                  return types.fail("source.closure-inputs",
                                    "source loop invariant yield differs",
                                    op.span);
                copy->results[copy->results.size() - invariants + i] = {
                    region->inputs - invariants + i};
              }
              copy->results.insert(copy->results.end(), inputs.begin(),
                                   inputs.end());
            }
            auto nested = environment;
            auto nestedDomains = selectedDomains;
            unsigned offset = 0;
            for (auto &entry : nested)
              for (auto &operand : entry.captures)
                operand = {selected->layout.captures[offset++]};
            for (auto &domain : nestedDomains)
              for (auto &operand : domain.operands)
                operand = {selected->layout.captures[offset++]};
            if (!closeBody(*copy, bindings, Body::Mode::Local, depth, height,
                           nested, nestedDomains))
              return false;
            control->regionLayouts.push_back(std::move(selected->layout));
            region = std::move(copy);
          }
          if (extraOperands)
            control->operands.insert(control->operands.end(),
                                     extraOperands->begin(),
                                     extraOperands->end());
          control->domainArguments.clear();
        }
      }
      auto effects = inferEffects(types, declarations, body);
      if (!effects)
        return false;
      if (!effects->dependencies.empty())
        return types.fail(
            "source.effect", "closed body retains callback effect dependencies",
            body.operations.empty() ? Span{} : body.operations.front().span);
      body.effects = std::move(*effects);
      body.scopedBindings.clear();
      body.domainBindings.clear();
      if (mode == Body::Mode::Math) {
        std::vector<Dependencies> inputs;
        for (unsigned i = 0; i < body.inputs; ++i)
          inputs.push_back({{i}, false});
        auto summary = summarizeBody(types, declarations, body, {}, inputs, {});
        if (!summary || summary->parameterized)
          return false;
        body.formationRequirements.clear();
        for (unsigned i = 0; i < body.values.size(); ++i)
          body.values[i].components = summary->values[i].inputs;
        for (const auto &requirement : summary->formation)
          body.formationRequirements.push_back(requirement.inputs);
        body.parameterizedSummary = false;
      }
      if (mode == Body::Mode::Local)
        body.formationRequirements.clear();
      body.parameterizedSummary = false;
      return true;
    };
    instantiate = [&](DeclarationId origin, ArrayRef<Type> args, unsigned depth,
                      ArrayRef<DeclarationId> scoped,
                      ArrayRef<std::shared_ptr<const DomainShape>> domains,
                      const ClosureLayout &providedLayout)
        -> std::optional<DeclarationId> {
      const auto &source = declarations[origin.index];
      if (depth > work.limits.callDepth) {
        types.fail("source.limit", "closed call depth limit exceeded",
                   source.span);
        return {};
      }
      auto mode = source.kind == Declaration::Kind::Oracle ? Body::Mode::Oracle
                  : source.kind == Declaration::Kind::Protocol
                      ? Body::Mode::Protocol
                  : (source.kind == Declaration::Kind::Local ||
                     source.kind == Declaration::Kind::EntryFunction)
                      ? Body::Mode::Local
                      : Body::Mode::Math;
      if ((!source.body && source.kind != Declaration::Kind::Relation &&
           source.kind != Declaration::Kind::Construction) ||
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
      if (scoped.size() != source.scopedInputs.size()) {
        types.fail("source.scoped", "specialization scoped arity differs",
                   source.span);
        return {};
      }
      for (auto selected : scoped) {
        if (!types.charge(1, source.span))
          return {};
        if (selected.index >= declarations.size()) {
          types.fail("source.effect",
                     "selected callback is outside the project", source.span);
          return {};
        }
        frame(key, declarations[selected.index].symbol);
      }
      if (domains.size() != source.domainInputs.size()) {
        types.fail("source.finite-domain",
                   "specialization domain arity differs", source.span);
        return {};
      }
      frame(key, "domains");
      for (const auto &domain : domains) {
        if (!domain || !types.charge(domain->identity.size() + 1, source.span))
          return {};
        frame(key, domain->identity);
      }
      auto layout = providedLayout;
      if (layout.inputs.empty() && source.inputs.size())
        for (unsigned i = 0; i < source.inputs.size(); ++i)
          layout.inputs.push_back(i);
      if (layout.inputs.size() != source.inputs.size()) {
        types.fail("source.closure-inputs",
                   "authored closure input arity differs", source.span);
        return {};
      }
      frame(key, "input-aliases");
      for (unsigned i = 0; i < layout.inputs.size(); ++i) {
        if (layout.inputs[i] > i ||
            layout.inputs[layout.inputs[i]] != layout.inputs[i]) {
          types.fail("source.closure-inputs",
                     "invalid authored alias partition", source.span);
          return {};
        }
        frame(key, std::to_string(layout.inputs[i]));
      }
      frame(key, "capture-inputs");
      for (auto port : layout.captures)
        frame(key, std::to_string(port));
      if (!types.charge(layout.inputs.size() + layout.captures.size() + 1,
                        source.span))
        return {};
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
      if (source.construction &&
          !types.chargeConstruction(*source.construction, source.span))
        return {};
      auto targetArguments = source.staticArguments;
      if (source.effectAllowance &&
          !types.charge(source.effectAllowance->dependencies.size() + 1,
                        source.span))
        return {};
      unsigned height = 1;
      Declaration result = source;
      if (source.effectAllowance) {
        std::vector<EffectSummary> effects;
        for (auto callback : scoped) {
          if (!types.charge(1, source.span))
            return {};
          if (callback.index >= declarations.size() ||
              !declarations[callback.index].body) {
            types.fail("source.effect", "selected callback has no effect body",
                       source.span);
            return {};
          }
          if (!types.charge(declarations[callback.index]
                                    .body->effects.dependencies.size() +
                                1,
                            source.span))
            return {};
          effects.push_back(declarations[callback.index].body->effects);
        }
        result.effectAllowance = substituteEffects(
            types, *source.effectAllowance, effects, source.span);
        if (!result.effectAllowance)
          return {};
      }
      DeclarationId id{uint32_t(declarations.size())};
      result.id = id;
      // checkArguments has discharged every template admission against args.
      result.admissions.clear();
      result.origin = origin;
      result.members.clear();
      result.staticArguments.assign(args.begin(), args.end());
      result.scopedArguments.assign(scoped.begin(), scoped.end());
      result.closureLayout = layout;
      result.domainArguments.assign(domains.begin(), domains.end());
      // Native participant carriers bound identifiers to 128 bytes. Reuse the
      // instance key for long declaration paths instead of narrowing source
      // names.
      if (!args.empty() || !scoped.empty() || !domains.empty() ||
          !layout.captures.empty() ||
          llvm::any_of(llvm::enumerate(layout.inputs),
                       [](const auto &input) {
                         return input.index() != input.value();
                       }) ||
          result.symbol.size() > 128)
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
      auto bindings = callableSubstitution(result, args);
      for (auto *ports : {&result.inputs, &result.outputs})
        for (auto &port : *ports) {
          if (!closeType(port.type, bindings, port.span) ||
              (result.kind == Declaration::Kind::EntryFunction &&
               !types.hostData(port.type, port.span)))
            return {};
          if (port.oracle && port.oracle->maximumRows &&
              !closeType(*port.oracle->maximumRows, bindings, port.span))
            return {};
          if (result.kind == Declaration::Kind::Protocol &&
              !types.oraclePort(port))
            return {};
        }
      if (result.oracleDefinition) {
        auto definition = closeOracleDefinition(types, *result.oracleDefinition,
                                                bindings, result.span);
        if (!definition)
          return {};
        // The predicate never recursively instantiates its owner. Publish the
        // reverse closed link here after obtaining its independent instance.
        auto predicate =
            instantiate(definition->admissibility, args, depth + 1, {}, {}, {});
        if (!predicate)
          return {};
        height = std::max(height, heights.at(predicate->index) + 1);
        definition->admissibility = *predicate;
        declarations[predicate->index].oraclePredicateOwner = id;
        result.oracleDefinition = std::move(definition);
      }
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
        auto selected =
            instantiate(subject.relation, subject.arguments, 1, {}, {}, {});
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
      if (result.body) {
        assert(result.body->mode == mode && "declaration body mode changed");
        auto body = std::make_shared<Body>(*result.body);
        std::vector<Value> hidden;
        std::vector<Environment> environment;
        unsigned offset = 0;
        for (unsigned i = 0; i < scoped.size(); ++i) {
          const auto &helper = declarations[scoped[i].index];
          Environment selected{scoped[i], {}};
          for (unsigned j = result.scopedInputs[i].signature.inputs.size();
               j < helper.inputs.size(); ++j) {
            if (offset >= layout.captures.size()) {
              types.fail("source.closure-inputs",
                         "missing hidden input mapping", result.span);
              return {};
            }
            auto position = layout.captures[offset++];
            auto port = helper.inputs[j];
            if (position > result.inputs.size()) {
              types.fail("source.closure-inputs",
                         "noncontiguous hidden input mapping", result.span);
              return {};
            }
            if (position == result.inputs.size()) {
              port.name = "capture" + std::to_string(hidden.size());
              result.inputs.push_back(port);
              hidden.push_back({port.type, {}, port.span});
            } else if (result.inputs[position].type != port.type) {
              types.fail("source.closure-inputs", "aliased input types differ",
                         result.span);
              return {};
            }
            selected.captures.push_back({position});
          }
          environment.push_back(std::move(selected));
        }
        std::vector<DomainEnvironment> domainEnvironment;
        for (unsigned i = 0; i < domains.size(); ++i) {
          const auto &domain = domains[i];
          auto item = types.substitute(result.domainInputs[i].item, bindings,
                                       result.span);
          if (!item || domain->result >= domain->nodes.size() ||
              *item != domain->nodes[domain->result].item) {
            if (!types.diagnostic)
              types.fail("source.finite-domain",
                         "closed domain item type differs", result.span);
            return {};
          }
          DomainEnvironment selected{domain, {}};
          for (const auto &type : domain->inputs) {
            if (offset >= layout.captures.size()) {
              types.fail("source.closure-inputs",
                         "missing domain input mapping", result.span);
              return {};
            }
            auto position = layout.captures[offset++];
            if (position > result.inputs.size()) {
              types.fail("source.closure-inputs",
                         "noncontiguous domain input mapping", result.span);
              return {};
            }
            if (position == result.inputs.size()) {
              result.inputs.push_back(
                  {"capture" + std::to_string(hidden.size()),
                   type,
                   {},
                   result.span});
              hidden.push_back({type, {}, result.span});
            } else if (result.inputs[position].type != type) {
              types.fail("source.closure-inputs",
                         "aliased domain input types differ", result.span);
              return {};
            }
            selected.operands.push_back({position});
          }
          domainEnvironment.push_back(std::move(selected));
        }
        if (offset != layout.captures.size() ||
            !types.charge(hidden.size() + 1, result.span))
          return {};
        appendBodyInputs(*body, hidden);
        mapBodyValues(*body, [&](ValueId value) {
          return ValueId{value.index < layout.inputs.size()
                             ? layout.inputs[value.index]
                             : value.index};
        });
        if (!closeBody(*body, bindings, mode, depth, height, environment,
                       domainEnvironment))
          return {};
        if (result.kind == Declaration::Kind::Math ||
            result.kind == Declaration::Kind::Relation)
          for (const auto &value : body->values)
            if (!types.mathematicalData(value.type, value.span))
              return {};
        auto assumptions = mapDataPreconditions(types, result.dataPreconditions,
                                                layout.inputs);
        if (!assumptions)
          return {};
        result.dataPreconditions = std::move(*assumptions);
        auto requirements = deriveDataPreconditions(
            types, declarations, result, *body,
            result.scopedOrigin || !result.scopedInputs.empty() ||
                !result.domainInputs.empty());
        if (!requirements)
          return {};
        result.dataPreconditions = std::move(*requirements);
        result.body = std::move(body);
      }
      if (result.construction) {
        auto &construction = *result.construction;
        for (auto &argument : targetArguments)
          if (!closeType(argument, bindings, result.span))
            return {};
        auto target =
            instantiate(*result.target, targetArguments, depth + 1, {}, {}, {});
        if (!target)
          return {};
        result.target = *target;
        for (auto *term : {&construction.provider, &construction.state})
          if (*term && !closeType(**term, bindings, result.span))
            return {};
        for (auto &argument : construction.arguments)
          if (!closeType(argument, bindings, result.span))
            return {};
        if (construction.parent) {
          auto parent =
              instantiate(*construction.parent, construction.arguments,
                          depth + 1, {}, {}, {});
          if (!parent)
            return {};
          construction.parent = *parent;
        }
        if (construction.initializer) {
          auto &factory = *construction.initializer;
          if (!closeCallable(factory.declaration, factory.module,
                             construction.initializerArguments, bindings,
                             result.span))
            return {};
          auto initializer = instantiate(factory.declaration,
                                         construction.initializerArguments,
                                         depth + 1, {}, {}, {});
          if (!initializer)
            return {};
          factory.declaration = *initializer;
        }
        if (construction.codec) {
          auto &codec = *construction.codec;
          if (!closeType(codec.provider, bindings, result.span) ||
              !closeType(codec.record, bindings, result.span))
            return {};
          for (auto *method :
               {&codec.initialize, &codec.write, &codec.finish}) {
            if (!closeCallable(method->target.declaration,
                               method->target.module, method->arguments,
                               bindings, result.span))
              return {};
            auto closed = instantiate(method->target.declaration,
                                      method->arguments, depth + 1, {}, {}, {});
            if (!closed)
              return {};
            method->target.declaration = *closed;
          }
        }
        for (auto &application : construction.applications) {
          for (auto &argument : application.arguments)
            if (!closeType(argument, bindings, application.span))
              return {};
          auto child =
              instantiate(application.construction, application.arguments,
                          depth + 1, {}, {}, {});
          if (!child)
            return {};
          application.construction = *child;
        }
        for (auto &rule : construction.rules) {
          for (auto *value : {&rule.payload, &rule.chunks})
            if (*value && !closeType(**value, bindings, rule.span))
              return {};
          for (auto &argument : rule.arguments)
            if (!closeType(argument, bindings, rule.span))
              return {};
          auto handler =
              instantiate(rule.handler, rule.arguments, depth + 1, {}, {}, {});
          if (!handler)
            return {};
          rule.handler = *handler;
        }
      }
      if (result.oracleDefinition &&
          !checkOracleDefinition(types, declarations, result))
        return {};
      result.scopedInputs.clear();
      result.domainInputs.clear();
      result.inputOrder.clear();
      for (unsigned i = 0; i < result.inputs.size(); ++i)
        result.inputOrder.push_back({Declaration::InputSlot::Kind::Data, i});
      for (unsigned i = 0; i < result.services.size(); ++i)
        result.inputOrder.push_back({Declaration::InputSlot::Kind::Service, i});
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
    bool function =
        declarations[selected.index].kind == Declaration::Kind::EntryFunction;
    auto target = function ? std::optional(selected)
                           : declarations[selected.index].target;
    auto args = declarations[selected.index].staticArguments;
    if (!target)
      return types.fail("source.entry", "Entry has no checked target",
                        declarations[selected.index].span);
    auto instance = instantiate(*target, args, 1, {}, {}, {});
    if (!instance)
      return false;
    if (!function && !types.checkProofEntry(declarations[selected.index],
                                            declarations[instance->index]))
      return false;
    if (const auto *proof = declarations[selected.index].proof();
        proof && proof->selectedConstruction) {
      auto constructionArguments = proof->constructionArguments;
      auto construction = instantiate(*proof->selectedConstruction,
                                      constructionArguments, 1, {}, {}, {});
      if (!construction)
        return false;
      std::get<ProofEntry>(declarations[selected.index].configuration)
          .selectedConstruction = *construction;
    }
    const auto &inputs = declarations[instance->index].inputs;
    for (unsigned i = 0; i < inputs.size(); ++i) {
      const auto &port = inputs[i];
      if (operation == HostInvocation::Kind::Verify &&
          !llvm::is_contained(port.roles,
                              declarations[selected.index].proof()->verifier))
        continue;
      // Whole key ports use Entry setup initialization. Exact setup coverage is
      // checked from the closed layout before closeEntry publishes its handle.
      bool key = port.type.kind == Type::Kind::Builtin &&
                 (port.type.domain == "prover_key" ||
                  port.type.domain == "verifier_key");
      bool initialized = llvm::any_of(
          declarations[selected.index].setups, [&](const SetupSlot &slot) {
            return llvm::any_of(slot.inputs, [&](const InputSelector &input) {
              return input.port == i && input.path.empty();
            });
          });
      if (key && initialized) {
        if (!types.executableType(port.type, port.span))
          return false;
      } else if (port.oracle ? !types.oraclePort(port)
                             : !types.ingress(port.type, port.span))
        return false;
    }
    // Compare canonical typed terms, including parameters absent from runtime
    // inputs. Source names are aliases; one closed identity has one ABI.
    std::map<std::tuple<std::string, std::string, std::string, std::string>,
             const Declaration *>
        opaqueInstances;
    for (const auto &decl : declarations) {
      if (!decl.origin || !decl.relation ||
          decl.relation->kind != RelationDefinition::Kind::Opaque)
        continue;
      json::Array arguments;
      for (const auto &argument : decl.staticArguments) {
        if (!types.chargeType(argument, decl.span))
          return false;
        auto encoded = encodeStaticTerm(argument);
        if (!encoded) {
          consumeError(encoded.takeError());
          return types.fail("source.relation",
                            "opaque static argument is not closed", decl.span);
        }
        arguments.push_back(std::move(*encoded));
      }
      std::string canonical;
      raw_string_ostream(canonical) << json::Value(std::move(arguments));
      const auto &definition = *decl.relation;
      auto [at, added] = opaqueInstances.emplace(
          std::make_tuple(definition.externalKind, definition.key,
                          definition.revision, canonical),
          &decl);
      if (added)
        continue;
      const auto &previous = *at->second;
      if (definition.purposes != previous.relation->purposes ||
          decl.inputs.size() != previous.inputs.size())
        return types.fail(
            "source.relation",
            "one opaque instance has conflicting logical signatures", decl.span,
            {previous.span});
      for (unsigned i = 0; i < decl.inputs.size(); ++i) {
        if (!types.chargeType(decl.inputs[i].type, decl.span) ||
            !types.chargeType(previous.inputs[i].type, previous.span))
          return false;
        if (decl.inputs[i].type != previous.inputs[i].type)
          return types.fail(
              "source.relation",
              "one opaque instance has conflicting logical signatures",
              decl.span, {previous.span});
      }
    }
    // Dormant closed definitions are part of the selected source closure too.
    // Open templates were checked eagerly and cannot have monomorphic SSA.
    for (unsigned i = 0; i < templates; ++i)
      if (declarations[i].kind == Declaration::Kind::Oracle &&
          declarations[i].parameters.empty() &&
          !instantiate(DeclarationId{i}, {}, 1, {}, {}, {}))
        return false;
    declarations[selected.index].target = *instance;
    for (auto id : generatedTemplates)
      declarations[id.index].body.reset();
    for (unsigned i = 0; i < templates; ++i)
      declarations[i].body.reset();
    return true;
  };
  return close() ? Error::success() : types.takeError();
}
} // namespace zkc::language::detail
