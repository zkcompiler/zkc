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
                        signature.itemOrigins.size() + 1,
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
  return signature.itemOrigins == expected ||
         refuse("callback item origins differ from authored selectors");
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
llvm::Error checkComponentEffects(const CheckedStorage &storage, Work &work) {
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
      if (!provided || !provided->body ||
          !effectsWithin(types, provided->body->effects,
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
