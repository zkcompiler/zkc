#include "PIR.h"
#include "../Resolution/Project.h"
#include "OutputWork.h"
#include "zkc/Frontend/Diagnostic.h"
#include "zkc/Source/Codec.h"
#include <map>
#include <set>
#include <type_traits>

using namespace llvm;
namespace zkc::frontend::lowering {
namespace {
Expected<source::Body> lowerBody(const model::Module &module,
                                 const model::Body &body) {
  source::Body result;
  for (const auto &instruction : body) {
    auto value = std::visit(
        [&](const auto &v) -> Expected<source::Instruction::Value> {
          using T = std::decay_t<decltype(v)>;
          if constexpr (std::is_same_v<T, model::Call>) {
            // A complete model has resolved every call to a declaration of
            // the kind the call names; lowering never repairs it.
            if (v.target.index >= module.declarations.size())
              report_fatal_error("lowering reached a call to no declaration");
            const auto &target = module.declarations[v.target.index];
            auto kind = target.kind;
            bool algorithm = kind == Declaration::Kind::Function ||
                             kind == Declaration::Kind::Configuration;
            using K = model::Call::Kind;
            switch (v.kind) {
            case K::Operation:
              if (kind != Declaration::Kind::Operation &&
                  kind != Declaration::Kind::Binding)
                break;
              return source::Instruction::Value(
                  source::Operation{target.name, v.staticArguments,
                                    v.attributes, v.inputs, v.outputs});
            case K::Algorithm:
              if (!algorithm)
                break;
              return source::Instruction::Value(source::AlgorithmCall{
                  target.name, v.inputs, v.outputs, v.staticArguments});
            case K::Local:
              if (!algorithm)
                break;
              return source::Instruction::Value(
                  source::LocalCall{v.role, target.name, v.inputs, v.outputs});
            case K::Protocol:
              if (kind != Declaration::Kind::Dependency)
                break;
              return source::Instruction::Value(
                  source::ProtocolCall{target.name, v.inputs, v.outputs});
            }
            report_fatal_error("lowering reached a call whose kind differs "
                               "from its declaration");
          } else if constexpr (std::is_same_v<T, model::Loop>) {
            auto nested = lowerBody(module, v.body);
            if (!nested)
              return nested.takeError();
            return source::Instruction::Value(source::Loop{
                v.count, v.carried, v.captures, std::move(*nested), v.outputs});
          } else if constexpr (std::is_same_v<T, model::For>) {
            auto nested = lowerBody(module, v.body);
            if (!nested)
              return nested.takeError();
            return source::Instruction::Value(
                source::For{v.induction, v.lower, v.upper, v.carried,
                            v.captures, std::move(*nested), v.outputs});
          } else if constexpr (std::is_same_v<T, model::Conditional>) {
            auto left = lowerBody(module, v.thenBody);
            if (!left)
              return left.takeError();
            auto right = lowerBody(module, v.elseBody);
            if (!right)
              return right.takeError();
            return source::Instruction::Value(
                source::Conditional{v.condition, v.captures, std::move(*left),
                                    std::move(*right), v.outputs});
          } else if constexpr (std::is_same_v<T, model::Match>) {
            source::Match match{v.input, v.captures, {}, v.outputs};
            for (const auto &arm : v.arms) {
              auto nested = lowerBody(module, arm.body);
              if (!nested)
                return nested.takeError();
              match.arms.push_back(
                  {arm.alternative, arm.payload, std::move(*nested)});
            }
            return source::Instruction::Value(std::move(match));
          } else {
            return source::Instruction::Value(v);
          }
        },
        instruction.value);
    if (!value)
      return value.takeError();
    source::Instruction out;
    out.location = instruction.location;
    out.site = instruction.site;
    out.value = std::move(*value);
    result.push_back(std::move(out));
  }
  return result;
}
} // namespace
struct SourceEmitter {
  static model::EmittedSource
  finish(model::CheckedSource checked, source::Content content,
         const std::map<DeclId, std::string> &names) {
    auto model = std::move(checked).takeModel();
    for (const auto &[id, name] : names)
      model->declarations.at(id.index).loweredName = name;
    return model::EmittedSource(std::move(model), std::move(content));
  }
};
Expected<model::EmittedSource> lower(model::CheckedSource &&checked,
                                     WorkBudget &budget) {
  const auto &model = checked.get();
  constexpr auto account = WorkAccount::Output;
  if (auto error = work::charge(budget, account))
    return error;
  if (model.construction) {
    for (auto count : {model.construction->publicBindings.size(),
                       model.construction->draws.size()})
      if (auto error = work::charge(budget, account, count))
        return error;
    for (const auto &binding : model.construction->publicBindings)
      if (auto error = work::charge(budget, account, binding.ports.size()))
        return error;
    if (auto error = source::checkStructure(*model.construction))
      return error;
    return SourceEmitter::finish(std::move(checked), *model.construction, {});
  }
  // Metadata has no callable bodies; those are supplied by plans below.
  for (auto count :
       {model.metadata.bindings.size(), model.metadata.instances.size(),
        model.metadata.entries.size(), model.metadata.configurations.size(),
        model.metadata.relations.size(), model.metadata.relationViews.size()})
    if (auto error = work::charge(budget, account, count))
      return error;
  for (const auto &binding : model.metadata.bindings)
    if (auto error =
            work::charge(budget, account, binding.application.arguments.size()))
      return error;
  for (const auto &configuration : model.metadata.configurations)
    for (auto count :
         {configuration.arguments.size(), configuration.implementations.size()})
      if (auto error = work::charge(budget, account, count))
        return error;
  for (const auto &instance : model.metadata.instances) {
    for (auto count : {instance.parameters.size(), instance.dependencies.size(),
                       instance.roles.size()})
      if (auto error = work::charge(budget, account, count))
        return error;
    for (const auto &parameter : instance.parameters)
      if (const auto *ingress =
              std::get_if<source::FamilyIngress>(&parameter.second)) {
        if (auto error =
                work::charge(budget, account, ingress->selectors.size()))
          return error;
        for (const auto &selector : ingress->selectors)
          if (auto error =
                  work::charge(budget, account, selector.arguments.size()))
            return error;
      }
  }
  source::Module out = model.metadata;
  std::map<DeclId, std::string> names;
  for (const auto &plan : model.bodies) {
    if (!plan.emit)
      continue;
    if (auto error = work::charge(budget, account))
      return error;
    const auto &declaration = model.declarations.at(plan.declaration.index);
    for (auto count : {plan.roles.size(), plan.naturalParameters.size(),
                       plan.dependencies.size(), declaration.parameters.size(),
                       declaration.requirements.size()})
      if (auto error = work::charge(budget, account, count))
        return error;
    for (const auto &requirement : declaration.requirements)
      if (auto error =
              work::charge(budget, account, requirement.arguments.size()))
        return error;
    for (const auto &dependency : plan.dependencies)
      if (auto error =
              work::charge(budget, account, dependency.agreements.size()))
        return error;
    for (const auto *ports : {&declaration.inputs, &declaration.outputs})
      for (const auto &port : *ports) {
        // Charge the authored port even if its flattened layout has no leaves.
        if (auto error = work::charge(budget, account))
          return error;
        auto count = model.types.at(port.type.index).kind == Type::Kind::Logical
                         ? size_t(1)
                         : model.layouts.at(port.type).size();
        if (auto error = work::charge(budget, account, count))
          return error;
      }
    std::optional<source::Body> body;
    if (plan.body) {
      if (auto error = chargeBody(budget, account, *plan.body))
        return error;
      auto lowered = lowerBody(model, *plan.body);
      if (!lowered)
        return lowered.takeError();
      body = std::move(*lowered);
    }
    const auto &d = model.declarations.at(plan.declaration.index);
    names.emplace(plan.declaration, d.name);
    auto inputs = [&] {
      std::vector<source::Parameter> flat;
      for (const auto &p : d.inputs)
        for (const auto &leaf : model.leaves(p))
          flat.push_back({leaf.name, model.spelling(leaf.type)});
      return flat;
    };
    auto outputs = [&] {
      source::Names flat;
      for (const auto &p : d.outputs)
        for (const auto &leaf : model.leaves(p))
          flat.push_back(model.spelling(leaf.type));
      return flat;
    };
    if (d.kind == Declaration::Kind::Protocol) {
      source::Protocol p;
      p.location = d.location;
      p.name = d.name;
      p.roles = plan.roles;
      p.parameters = plan.naturalParameters;
      p.dependencies = plan.dependencies;
      p.body = body;
      for (const auto &port : d.inputs)
        for (const auto &leaf : model.leaves(port))
          p.arguments.push_back(
              {leaf.name, leaf.role, model.spelling(leaf.type)});
      for (const auto &port : d.outputs)
        for (const auto &leaf : model.leaves(port))
          p.results.push_back({leaf.role, model.spelling(leaf.type)});
      out.protocols.push_back(std::move(p));
    } else if (d.generic) {
      source::GenericFunction f;
      f.location = d.location;
      f.name = d.name;
      for (DeclId id : d.parameters) {
        const auto &parameter = model.declarations.at(id.index);
        f.parameters.push_back({parameter.name, parameter.sort});
      }
      for (const auto &requirement : d.requirements) {
        source::Requirement r;
        r.location = requirement.location;
        r.predicate = requirement.predicate;
        for (DomainId argument : requirement.arguments)
          r.arguments.push_back(model.spelling(argument));
        f.requirements.push_back(std::move(r));
      }
      f.arguments = inputs();
      f.results = outputs();
      f.body = *body;
      out.definitions.push_back(std::move(f));
    } else {
      source::Function f;
      f.location = d.location;
      f.name = d.name;
      f.origin = plan.origin;
      f.arguments = inputs();
      f.results = outputs();
      f.body = body;
      out.functions.push_back(std::move(f));
    }
  }
  // Generic source definitions are also the origin anchors used by the
  // independent instantiator. Allocate those anchors from the same exact
  // project identities as ordinary and checked functions. No carrier extension
  // or downstream hash-to-source guess is needed.
  assert(model.resolution && "checked source retains resolved project input");
  {
    std::map<std::string, std::string> renamed;
    std::set<std::string> reserved;
    auto reserve = [&](const auto &declarations) {
      for (const auto &d : declarations)
        reserved.insert(d.name);
    };
    reserve(out.functions);
    reserve(out.protocols);
    reserve(out.bindings);
    reserve(out.configurations);
    reserve(out.instances);
    reserve(out.entries);
    for (auto &f : out.definitions) {
      auto name = f.name;
      if (const auto *d = model.resolution->lookup(name))
        f.name = model.resolution->origin(d->identity);
      if (!reserved.insert(f.name).second)
        return diagnostic(
            model.resolution->input, f.location.value_or(source::Span{}),
            "source-origin-collision",
            "a generic origin conflicts with another emitted declaration");
      renamed.emplace(std::move(name), f.name);
    }
    for (auto &[id, name] : names)
      if (model.declarations.at(id.index).generic &&
          model.declarations.at(id.index).kind != Declaration::Kind::Protocol)
        if (auto found = renamed.find(name); found != renamed.end())
          name = found->second;
    for (auto &configuration : out.configurations)
      if (auto it = renamed.find(configuration.base); it != renamed.end())
        configuration.base = it->second;
    auto calls = [&](source::Body &body) {
      source::walk(body, [&](source::Instruction &instruction) {
        if (auto *call = instruction.get<source::AlgorithmCall>())
          if (auto it = renamed.find(call->callee); it != renamed.end())
            call->callee = it->second;
      });
    };
    for (auto &f : out.definitions)
      calls(f.body);
    for (auto &f : out.functions)
      if (f.body)
        calls(*f.body);
    for (auto &p : out.protocols)
      if (p.body)
        calls(*p.body);
  }
  if (auto error = source::checkStructure(out))
    return error;
  return SourceEmitter::finish(std::move(checked), std::move(out), names);
}
} // namespace zkc::frontend::lowering
