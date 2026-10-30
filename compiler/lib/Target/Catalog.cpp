#include "zkc/Target/Catalog.h"
#include "NativePlanTypes.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Refusal.h"

using namespace llvm;
using namespace mlir;
using namespace zkc::protocol;
namespace zkc::target {
namespace {
MLIRContext *contextOf(const NativeBindingApplication &application) {
  if (application.context)
    return application.context;
  if (application.valueType)
    return application.valueType.getContext();
  for (auto argument : application.arguments)
    if (argument)
      return argument.getContext();
  return nullptr;
}
struct NativeDiagnostics {
  std::string code = "binding-signature", detail;
  ScopedDiagnosticHandler capture;
  explicit NativeDiagnostics(MLIRContext *context)
      : capture(context, [&](Diagnostic &diagnostic) {
          if (detail.empty()) {
            auto refusals = diagnostics::refusals(diagnostic);
            if (!refusals.empty())
              code = refusals.front().code;
          }
          detail += diagnostic.str();
          return success();
        }) {}
  Error refusal() { return error(code, detail); }
};
const generic::Operation *operation(StringRef contract) {
  for (const auto &entry : executableOperationContracts())
    if (entry.name == contract)
      return &entry;
  return nullptr;
}
StringRef domainOf(Type type) {
  auto interface =
      dyn_cast_or_null<CatalogTypeInterface>(logicalValueType(type));
  auto application =
      interface ? interface.getCatalogApplication() : std::nullopt;
  if (application && application->arguments.size() == 1)
    if (auto identity = dyn_cast<StringAttr>(application->arguments[0]))
      return identity.getValue();
  return {};
}
// A facet and an exact installed descriptor jointly identify the contraction
// port. Lexical identity is policy; the resolved signature is installation.
Expected<FunctionType>
resolveDiagonal(const NativeBindingApplication &application,
                const ImplementationCatalog &catalog) {
  auto installed = resolveNativeApplication(application, true, {}, catalog);
  if (!installed)
    return installed.takeError();
  const auto *facts = operationContracts(application.contract);
  if (!facts || bool(facts->diagonalMap) == bool(facts->linearContraction))
    return error("binding-contraction");
  bool producer = facts->diagonalMap.has_value();
  auto ports = producer ? installed->getResults() : installed->getInputs();
  unsigned index = producer ? facts->diagonalMap->result
                            : facts->linearContraction->valuesOperand;
  if (index >= ports.size() ||
      !isDiagonalRepresentation(
          cast<runtime::RepresentedType>(ports[index]).getRepresentation()))
    return error("binding-contraction");
  return *installed;
}
bool isResident(StringRef representation) {
  return representation == "blst/fr" || representation == "blst/g1" ||
         representation == "blst/g2" ||
         representation == "halo2curves-axiom/bn254.fr" ||
         representation == "halo2curves-axiom/bn254.g1" ||
         representation == "halo2curves-axiom/bn254.g2";
}
struct ImplementationPreference {
  StringRef contract, domain, implementation;
};
constexpr ImplementationPreference preferredImplementations[] = {
    {"curve.scale", "bls12-381.g2", "blst/resident/curve.scale"},
    {"curve.scale_each", "bls12-381.g2", "blst/resident/curve.scale_each"},
    {"curve.vector_scale", "bls12-381.g2", "blst/resident/curve.vector_scale"},
    {"pairing.check", "bls12-381.fr", "blst/resident/pairing.check"},
};
class InstalledCandidates final : public CandidateCatalog {
public:
  Expected<std::vector<std::string>>
  implementations(const NativeBindingApplication &application) const override {
    auto fallback = defaultNativeImplementation(application);
    if (!fallback) {
      auto terminal = handleErrors(
          fallback.takeError(), [](const Refusal &refusal) -> Error {
            if (refusal.code == "binding-implementation")
              return Error::success();
            return error(refusal.code, refusal.detail);
          });
      if (terminal)
        return terminal;
      return std::vector<std::string>{};
    }
    std::vector<std::string> choices;
    for (const auto &[contract, domain, implementation] :
         preferredImplementations) {
      if (application.contract != contract ||
          application.arguments.size() != 1 ||
          application.arguments.front() !=
              StringAttr::get(contextOf(application), domain) ||
          *fallback == implementation)
        continue;
      const auto *entry =
          installedImplementations().find(contract, implementation);
      if (!entry || entry->requiresExplicitSelection)
        continue;
      auto candidate = application;
      candidate.implementation = implementation.str();
      candidate.valueType = {};
      auto installed = resolveNativeApplication(candidate);
      if (!installed) {
        auto terminal = handleErrors(
            installed.takeError(), [](const Refusal &refusal) -> Error {
              if (refusal.code == "binding-implementation")
                return Error::success();
              return error(refusal.code, refusal.detail);
            });
        if (terminal)
          return terminal;
        continue;
      }
      choices.push_back(implementation.str());
    }
    choices.push_back(std::move(*fallback));
    return choices;
  }
  std::vector<NativeBindingApplication> conversions(Type from,
                                                    Type to) const override {
    auto source = dyn_cast_or_null<runtime::RepresentedType>(from);
    auto target = dyn_cast_or_null<runtime::RepresentedType>(to);
    if (!source || !target || from == to ||
        source.getLogical() != target.getLogical())
      return {};
    auto context = from.getContext();
    auto signature = FunctionType::get(context, {from}, {to});
    if (isResident(source.getRepresentation()) ||
        isResident(target.getRepresentation()))
      return {{"representation.convert",
               {TypeAttr::get(source.getLogical())},
               "native/representation.convert",
               signature,
               context}};
    if (planTypeConstructor(from) != "table")
      return {};
    return {{"table.relayout",
             {StringAttr::get(context, domainOf(from))},
             "arkworks/table.relayout",
             signature,
             context}};
  }
};
} // namespace
Expected<FunctionType>
resolveNativeApplication(const NativeBindingApplication &application,
                         bool physical, Type familyLayout,
                         const ImplementationCatalog &catalog) {
  auto context = contextOf(application);
  if (!context)
    return error("binding-declaration-context");
  NativeDiagnostics diagnostics(context);
  auto request = application;
  if (!physical)
    request.valueType = {};
  auto signature = resolveInstalledSignature(
      [&] { return emitError(UnknownLoc::get(context)); }, context, request,
      physical, catalog, familyLayout);
  if (!signature)
    return diagnostics.refusal();
  if (physical && application.valueType && !familyLayout &&
      signature != application.valueType)
    return error("binding-signature");
  return signature;
}
Expected<NativeBindingChoice> readPlanBinding(runtime::BindingOp declaration) {
  if (!declaration)
    return error("binding-declaration-context");
  NativeDiagnostics diagnostics(declaration.getContext());
  auto native =
      readNativeBinding([&] { return declaration.emitOpError(); }, declaration);
  if (failed(native))
    return diagnostics.refusal();
  NativeBindingApplication application{
      declaration.getContract().str(),
      {declaration.getArguments().begin(), declaration.getArguments().end()},
      declaration.getImplementation().str(),
      native->physical ? native->valueType : FunctionType{},
      declaration.getContext()};
  return NativeBindingChoice{declaration.getSymName().str(),
                             std::move(application)};
}
Expected<std::string>
defaultNativeImplementation(const NativeBindingApplication &application) {
  auto context = contextOf(application);
  if (!context)
    return error("binding-declaration-context");
  NativeDiagnostics diagnostics(context);
  auto emit = [&] { return emitError(UnknownLoc::get(context)); };
  if (!resolveLogicalSignature(emit, context, application.contract,
                               application.arguments))
    return diagnostics.refusal();
  if (resourceUnitContract(application.contract))
    return "logical/" + application.contract;
  auto terms = resolveBindingTerms(emit, context, application.contract,
                                   application.arguments);
  if (failed(terms))
    return diagnostics.refusal();
  const auto *logical = operation(application.contract);
  const ImplementationDescriptor *selected = nullptr;
  for (const auto &entry : installedImplementations().all()) {
    if (entry.contract != application.contract)
      continue;
    if (auto e = checkImplementationScope(entry, logical->signature.scope))
      return e;
    if (installedImplementations().preferred(entry.contract, entry.provider) !=
        &entry)
      continue;
    if (entry.compatibility !=
        ImplementationDescriptor::Compatibility::Independent) {
      auto identity = dyn_cast<StringAttr>((*terms)[entry.providerTerm]);
      if (!identity || installedDomains().defaultProvider(
                           identity.getValue()) != entry.provider)
        continue;
    }
    if (selected)
      return error("binding-implementation");
    selected = &entry;
  }
  if (!selected)
    return error("binding-implementation");
  auto candidate = application;
  candidate.implementation = selected->identity;
  candidate.valueType = {};
  auto admitted = resolveNativeApplication(
      candidate, selected->family == ImplementationDescriptor::Family::Exact);
  if (!admitted)
    return admitted.takeError();
  return selected->identity;
}
std::vector<std::string> CandidateCatalog::diagonalImplementations(
    const NativeBindingApplication &application) const {
  return diagonalCandidates(application, installedImplementations());
}
std::vector<std::string>
diagonalCandidates(const NativeBindingApplication &application,
                   const ImplementationCatalog &catalog) {
  std::vector<std::string> result;
  for (const auto &entry : catalog.all()) {
    if (entry.contract != application.contract)
      continue;
    auto candidate = application;
    candidate.implementation = entry.identity;
    candidate.valueType = {};
    auto admitted = resolveDiagonal(candidate, catalog);
    if (!admitted) {
      consumeError(admitted.takeError());
      continue;
    }
    result.push_back(entry.identity);
  }
  llvm::sort(result);
  return result;
}
Expected<FunctionType>
resolveDiagonalImplementation(const NativeBindingApplication &application) {
  return resolveDiagonal(application, installedImplementations());
}
const CandidateCatalog &installedCandidates() {
  static const InstalledCandidates catalog;
  return catalog;
}
Error checkDirectConversion(const NativeBindingApplication &application,
                            Type from, Type to) {
  if (auto e = checkPhysicalType(from))
    return e;
  if (auto e = checkPhysicalType(to))
    return e;
  if (from.getContext() != to.getContext() ||
      logicalValueType(from) != logicalValueType(to) || from == to ||
      (application.contract != "representation.convert" &&
       application.contract != "table.relayout"))
    return error("binding-no-conversion");
  auto signature = FunctionType::get(from.getContext(), {from}, {to});
  if (application.valueType != signature)
    return error("binding-no-conversion");
  auto installed = resolveNativeApplication(application);
  if (!installed)
    return installed.takeError();
  return *installed == signature ? Error::success()
                                 : error("binding-no-conversion");
}
} // namespace zkc::target
