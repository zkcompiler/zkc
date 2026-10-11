#include "SignatureWitness.h"
#include "Effects.h"
#include "Internal.h"
#include "llvm/ADT/STLExtras.h"
namespace zkc::language::detail {
namespace {
bool checkOrigins(Semantics &types, const Declaration &decl,
                  const SyntaxDeclaration &source,
                  const ScopedParameter &parameter,
                  const SyntaxScopedSignature &written) {
  auto refuse = [&](llvm::StringRef message) {
    return types.fail("source.scoped-witness", message, parameter.span);
  };
  const auto &signature = parameter.signature;
  if (!types.charge(written.inputLabels.size() + source.domainInputs.size() +
                        written.itemOrigins.size() +
                        parameter.itemOrigins.size() + 1,
                    parameter.span))
    return false;
  if (written.inputLabels.size() != signature.inputs.size() ||
      written.inputLabels != parameter.inputLabels ||
      source.domainInputs.size() != decl.domainInputs.size())
    return refuse("callback source input coverage differs");
  std::map<std::string, unsigned> labels, domains;
  for (unsigned i = 0; i < written.inputLabels.size(); ++i) {
    const auto &label = written.inputLabels[i];
    if (!types.charge(label.size() + 1, parameter.span))
      return false;
    if (!label.empty() && !labels.emplace(label, i).second)
      return refuse("duplicate callback source label");
  }
  for (unsigned i = 0; i < source.domainInputs.size(); ++i) {
    const auto &name = source.domainInputs[i].name;
    if (!types.charge(name.size() + 1, parameter.span))
      return false;
    if (name != decl.domainInputs[i].name || !domains.emplace(name, i).second)
      return refuse("callback source domain differs");
  }
  std::map<unsigned, unsigned> expected;
  for (const auto &condition : written.itemOrigins) {
    if (!types.charge(condition.input.size() + condition.domain.size() + 1,
                      condition.span))
      return false;
    auto input = labels.find(condition.input);
    auto domain = domains.find(condition.domain);
    if (input == labels.end() || domain == domains.end() ||
        signature.inputs[input->second] !=
            decl.domainInputs[domain->second].item ||
        !expected.emplace(input->second, domain->second).second)
      return refuse("invalid authored callback item origin");
  }
  return parameter.itemOrigins == expected ||
         refuse("callback item origins differ from authored selectors");
}

bool checkMemberInputs(Semantics &types, const Declaration &required,
                       const Declaration &provided,
                       const Substitution &bindings) {
  auto refuse = [&] {
    return types.fail("source.scoped-witness",
                      "implementation callback contract differs from interface",
                      provided.span);
  };
  if (!types.charge(required.inputOrder.size() + required.domainInputs.size() +
                        required.scopedInputs.size() + 1,
                    provided.span))
    return false;
  if (required.kind != provided.kind ||
      required.inputOrder.size() != provided.inputOrder.size() ||
      required.domainInputs.size() != provided.domainInputs.size() ||
      required.scopedInputs.size() != provided.scopedInputs.size())
    return refuse();
  for (unsigned i = 0; i < required.inputOrder.size(); ++i)
    if (required.inputOrder[i].kind != provided.inputOrder[i].kind ||
        required.inputOrder[i].index != provided.inputOrder[i].index)
      return refuse();
  auto sameType = [&](const Type &expected, const Type &actual) {
    auto resolved = types.substitute(expected, bindings, provided.span);
    return resolved && (*resolved == actual || refuse());
  };
  for (unsigned i = 0; i < required.domainInputs.size(); ++i)
    if (!sameType(required.domainInputs[i].item, provided.domainInputs[i].item))
      return false;
  for (unsigned i = 0; i < required.scopedInputs.size(); ++i) {
    const auto &expected = required.scopedInputs[i];
    const auto &actual = provided.scopedInputs[i];
    if (!types.charge(expected.itemOrigins.size() + actual.itemOrigins.size() +
                          expected.signature.inputs.size() + 1,
                      provided.span))
      return false;
    if (expected.itemOrigins != actual.itemOrigins ||
        expected.signature.mode != actual.signature.mode ||
        expected.signature.allowance != actual.signature.allowance ||
        expected.signature.inputs.size() != actual.signature.inputs.size())
      return refuse();
    for (unsigned j = 0; j < expected.signature.inputs.size(); ++j)
      if (!sameType(expected.signature.inputs[j], actual.signature.inputs[j]))
        return false;
    if (!sameType(expected.signature.result, actual.signature.result))
      return false;
  }
  return true;
}
} // namespace
llvm::Error checkSignatureSources(const CheckedStorage &storage, Work &work) {
  Semantics types(storage.declarations, storage.assets, work);
  size_t retained = 0;
  for (const auto &decl : storage.declarations) {
    if (!types.charge(1, decl.span))
      return types.takeError();
    auto found = storage.signatureSources.find(decl.id.index);
    if (found == storage.signatureSources.end()) {
      if (!decl.scopedInputs.empty() || decl.effectAllowance)
        return failure("source.scoped-witness", "missing signature source",
                       decl.span);
      continue;
    }
    ++retained;
    auto refuse = [&] {
      return failure("source.scoped-witness",
                     "contract differs from authored signature", decl.span);
    };
    if (!found->second)
      return refuse();
    const auto &source = *found->second;
    if (!types.charge(source.scopedInputs.size() +
                          source.effectDependencies.size() + 1,
                      decl.span))
      return types.takeError();
    if (decl.scopedInputs.size() != source.scopedInputs.size())
      return refuse();
    for (unsigned slot = 0; slot < decl.scopedInputs.size(); ++slot) {
      const auto &written = source.scopedInputs[slot].scoped;
      const auto &parameter = decl.scopedInputs[slot];
      if (!written || written->mode != parameter.signature.mode ||
          written->allowance != parameter.signature.allowance)
        return refuse();
      if (!checkOrigins(types, decl, source, parameter, *written))
        return types.takeError();
    }
    std::optional<EffectSummary> expected;
    if (source.effects) {
      expected = EffectSummary{*source.effects};
      for (const auto &name : source.effectDependencies) {
        if (!types.charge(source.scopedInputs.size() + 1, decl.span))
          return types.takeError();
        auto input = llvm::find_if(source.scopedInputs, [&](const auto &port) {
          return port.name == name;
        });
        if (input == source.scopedInputs.end() || !input->scoped)
          return refuse();
        expected->dependencies.emplace(
            unsigned(input - source.scopedInputs.begin()),
            input->scoped->allowance);
      }
      if (!joinEffects(types, *expected, EffectSummary{}, decl.span))
        return types.takeError();
    }
    if (expected != decl.effectAllowance)
      return refuse();
  }
  if (retained != storage.signatureSources.size())
    return failure("source.scoped-witness", "invalid signature source owner");
  return llvm::Error::success();
}
llvm::Error checkComponentContracts(const CheckedStorage &storage, Work &work) {
  Semantics types(storage.declarations, storage.assets, work);
  for (const auto &component : storage.declarations) {
    if (!types.charge(1, component.span))
      return types.takeError();
    if (component.kind != Declaration::Kind::Component ||
        !component.implementation)
      continue;
    const auto *interface = types.typeDeclaration(*component.implementation);
    if (!interface)
      return failure("source.scoped-witness", "missing component interface",
                     component.span);
    if (!types.charge(component.parameters.size() + 1, component.span) ||
        !types.chargeType(*component.implementation, component.span))
      return types.takeError();
    auto bindings =
        types.substitution(*interface, component.implementation->arguments);
    Type self(Type::Kind::Component, component.qualifiedName);
    for (const auto &parameter : component.parameters)
      self.arguments.push_back(parameterType(parameter));
    bindings.emplace("self:" + interface->qualifiedName, std::move(self));
    for (auto requiredId : interface->members) {
      if (!types.charge(component.members.size() + 1, component.span))
        return types.takeError();
      if (requiredId.index >= storage.declarations.size())
        return failure("source.scoped-witness", "invalid interface member",
                       component.span);
      const auto &required = storage.declarations[requiredId.index];
      if (required.kind != Declaration::Kind::Local &&
          required.kind != Declaration::Kind::Math)
        continue;
      const Declaration *provided = nullptr;
      for (auto id : component.members) {
        if (id.index >= storage.declarations.size())
          return failure("source.scoped-witness", "invalid component member",
                         component.span);
        const auto &member = storage.declarations[id.index];
        if (member.name == required.name)
          provided = &member;
      }
      if (!provided || !provided->body)
        return failure("source.scoped-witness", "missing implementation member",
                       component.span);
      if (!checkMemberInputs(types, required, *provided, bindings))
        return types.takeError();
      if (!effectsWithin(types, provided->body->effects,
                         required.effectAllowance.value_or(EffectSummary{}),
                         component.span)) {
        types.fail("source.scoped-witness",
                   "implementation exceeds interface effect contract",
                   component.span);
        return types.takeError();
      }
    }
  }
  return llvm::Error::success();
}
} // namespace zkc::language::detail
