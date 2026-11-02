#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Instances.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/TypeProperties.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringMap.h"

namespace zkc::protocol {
namespace {
const OperationShape *findOperationShape(llvm::StringRef key) {
  static const auto catalog = [] {
    llvm::StringMap<const OperationShape *> entries;
    for (const auto &k : operationShapes())
      entries.try_emplace(k.key, &k);
    return entries;
  }();
  auto found = catalog.find(key);
  return found == catalog.end() ? nullptr : found->second;
}
} // namespace
const ComputationContract *computationContract(llvm::StringRef key) {
  const auto *facets = operationContracts(key);
  return facets && facets->mathematical ? &*facets->mathematical : nullptr;
}
const ComputationContract *admitMathematicalMeaning(
    const BindingApplication &application, llvm::ArrayRef<BoundType> inputs,
    llvm::ArrayRef<BoundType> outputs, llvm::ArrayRef<std::string> parameters) {
  auto *facet = computationContract(application.contract);
  if (!facet)
    return nullptr;
  auto signature = resolveLogicalBinding(application);
  if (!signature) {
    llvm::consumeError(signature.takeError());
    return nullptr;
  }
  if (inputs != llvm::ArrayRef<BoundType>(signature->inputs) ||
      outputs != llvm::ArrayRef<BoundType>(signature->outputs))
    return nullptr;
  if (auto error = checkParameters(application, parameters,
                                   zkc::protocol::ParameterStage::Logical)) {
    llvm::consumeError(std::move(error));
    return nullptr;
  }
  return facet;
}
const ComputationContract *admitComputationContract(
    const BindingApplication &application, llvm::ArrayRef<BoundType> inputs,
    llvm::ArrayRef<BoundType> outputs, llvm::ArrayRef<std::string> parameters) {
  if (!application.implementation.empty())
    return nullptr;
  return admitMathematicalMeaning(application, inputs, outputs, parameters);
}
bool isHistoryTransition(llvm::StringRef key) {
  const auto *contracts = operationContracts(key);
  return contracts && contracts->history.has_value();
}
const CosetConvention *cosetConvention(llvm::StringRef field) {
  // A prime field's declared two-adic convention, which its extensions along
  // BaseField share: even a nonbase extension shift uses the base root and
  // two-adicity. Cosets list `shift * root^i` in order.
  struct Conventions {
    llvm::StringMap<CosetConvention> roots;
    llvm::StringMap<const CosetConvention *> fields;
  };
  static const Conventions conventions = [] {
    Conventions result;
    for (const auto &row : instances::domains()) {
      if (!row.field || !row.field->twoAdic)
        continue;
      const auto &facts = *row.field->twoAdic;
      if (facts.ordering != "powers")
        llvm::report_fatal_error(
            llvm::Twine("unknown coset ordering of ") + row.identity, false);
      result.roots.try_emplace(
          row.identity,
          CosetConvention{facts.convention, row.identity, facts.maximalRoot,
                          "shift * root(size)^i; i = 0..size-1",
                          facts.twoAdicity});
    }
    for (const auto &row : instances::domains()) {
      const instances::Domain *link = &row;
      while (link && link->field && !link->field->twoAdic &&
             link->field->extension &&
             link->field->extension->over ==
                 instances::ExtensionBase::BaseField) {
        const instances::Domain *base = nullptr;
        for (const auto &member : link->members)
          if (member.member == "BaseField")
            base = instances::domain(member.identity);
        link = base;
      }
      if (link && link->field && link->field->twoAdic)
        result.fields.try_emplace(row.identity,
                                  &result.roots.find(link->identity)->second);
    }
    return result;
  }();
  auto found = conventions.fields.find(field);
  return found == conventions.fields.end() ? nullptr : found->second;
}
const OperationContracts *operationContracts(llvm::StringRef key) {
  const auto *application = findOperationShape(key);
  return application ? &application->contracts : nullptr;
}
const SamplingContract *samplingContract(llvm::StringRef key) {
  auto *c = operationContracts(key);
  return c && c->sampling ? &*c->sampling : nullptr;
}
bool isAcceptanceGuard(llvm::StringRef key) {
  auto *c = operationContracts(key);
  return c && c->acceptanceGuard;
}
bool isConjunction(llvm::StringRef key) {
  auto *c = operationContracts(key);
  return c && c->conjunction;
}
bool isPublicReplay(llvm::StringRef key) {
  auto *c = operationContracts(key);
  return c && c->publicReplay;
}
bool isConstructionDraw(llvm::StringRef key) {
  auto *c = samplingContract(key);
  return c && !c->derivedCounterpart.empty();
}
bool hasUnclassifiedProviderEffect(llvm::StringRef key) {
  const auto *k = findOperationShape(key);
  if (!k)
    return true;
  if (k->contracts.sampling || k->contracts.observation)
    return false;
  if (key.starts_with("resource_unit."))
    return true;
  const generic::Operation *declaration = nullptr;
  for (const auto &candidate : executableOperationContracts())
    if (candidate.name == key) {
      declaration = &candidate;
      break;
    }
  if (!declaration)
    return true;
  const auto &signature = declaration->signature;
  const auto &scope = signature.scope;
  // A Type formal carries no copy bound. Propagate this uncertainty through
  // applications instead of classifying only the outer port constructor.
  std::vector<bool> affineTerms;
  auto potentiallyAffine = [&](llvm::StringRef head,
                               llvm::ArrayRef<unsigned> arguments) {
    const auto *permissions = typePermissions(head);
    return !permissions || !permissions->copy ||
           llvm::any_of(arguments, [&](unsigned i) {
             return i >= affineTerms.size() || affineTerms[i];
           });
  };
  for (auto [i, term] : llvm::enumerate(scope.terms)) {
    bool affine = scope.sorts[i] == "Type";
    if (affine && term.arguments)
      affine = potentiallyAffine(term.name, *term.arguments);
    affineTerms.push_back(affine);
  }
  return llvm::any_of(signature.inputs, [&](const generic::Type &type) {
    return potentiallyAffine(type.constructor, type.arguments);
  });
}
} // namespace zkc::protocol
