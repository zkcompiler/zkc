#include "zkc/Target/Catalog.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Support/Json.h"

using namespace llvm;
using namespace zkc::protocol;
namespace zkc::target {
namespace {
// Facets identify the contraction port; exact installed descriptors identify
// its available implementation. Representation spelling grants no provider.
Expected<std::vector<BindingApplication>>
diagonalAlternatives(BindingApplication source,
                     const ImplementationCatalog &catalog) {
  source.implementation.clear();
  auto logical = resolveBinding(source, false);
  if (!logical)
    return logical.takeError();
  const auto *facts = operationContracts(source.contract);
  if (!facts || bool(facts->diagonalMap) == bool(facts->linearContraction))
    return error("binding-contraction");
  const bool producer = facts->diagonalMap.has_value();
  const auto &ports = producer ? logical->outputs : logical->inputs;
  unsigned index = producer ? facts->diagonalMap->result
                            : facts->linearContraction->valuesOperand;
  if (index >= ports.size())
    return error("binding-contraction");
  const auto &port = ports[index];
  const auto *representation = installedDomains().representationForLayout(
      port.kind, port.identity, "diagonal");
  if (!representation || !isDiagonalRepresentation(representation->identity))
    return error("binding-contraction");
  std::vector<BindingApplication> candidates;
  for (const auto &entry : catalog.all()) {
    if (entry.contract != source.contract)
      continue;
    for (const auto &override : entry.representations) {
      if (override.kind != port.kind || override.domain != port.identity ||
          override.identity != representation->identity ||
          override.port != index || override.output != producer)
        continue;
      auto candidate = source;
      candidate.implementation = entry.identity;
      candidates.push_back(std::move(candidate));
      break;
    }
  }
  // Installed-domain registration order is not a preference policy.
  llvm::sort(candidates, [](const auto &a, const auto &b) {
    return a.implementation < b.implementation;
  });
  return candidates;
}

Expected<BoundOperation> resolveDiagonal(const BindingApplication &application,
                                         const ImplementationCatalog &catalog) {
  // Full Contracts admission precedes any diagonal-specific checks. In
  // particular, nominal arguments and backend realization remain mandatory.
  auto installed = resolveBinding(application, true, catalog);
  if (!installed)
    return installed.takeError();
  const auto *facts = operationContracts(application.contract);
  if (!facts || bool(facts->diagonalMap) == bool(facts->linearContraction))
    return error("binding-contraction");
  const bool producer = facts->diagonalMap.has_value();
  const auto &ports = producer ? installed->outputs : installed->inputs;
  unsigned index = producer ? facts->diagonalMap->result
                            : facts->linearContraction->valuesOperand;
  if (index >= ports.size() ||
      !isDiagonalRepresentation(ports[index].representation))
    return error("binding-contraction");
  return installed;
}

class InstalledCandidates final : public CandidateCatalog {
public:
  Expected<std::vector<std::string>>
  implementations(const BindingApplication &application) const override {
    auto fallback = defaultImplementation(application);
    if (!fallback) {
      // Absence is an empty preference menu, so the checked numerical caller
      // can advance its owning occurrence. Malformed applications and unknown
      // errors remain failures of the catalog query.
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
    return std::vector<std::string>{std::move(*fallback)};
  }
  std::vector<BindingApplication>
  conversions(const BoundType &from, const BoundType &to) const override {
    if (from.kind == to.kind && from.identity == to.identity &&
        from.arguments == to.arguments && !(from == to) &&
        (StringRef(from.representation).starts_with("blst/") ||
         StringRef(to.representation).starts_with("blst/"))) {
      auto logical = erasePhysicalType(from);
      return {{"representation.convert",
               {logical.spelling()},
               "native/representation.convert",
               {from.spelling(), to.spelling()}}};
    }
    if (from.kind != "table" || to.kind != "table" ||
        from.identity != to.identity || from == to)
      return {};
    // Contracts currently installs only this adapter. Extending candidate
    // policy cannot extend that cross-language implementation boundary.
    BindingApplication candidate{
        "table.relayout",
        {from.identity, from.representation, to.representation},
        "arkworks/table.relayout"};
    // The proposer admits the exact candidate and preserves typed failures.
    // Filtering here would erase malformed/generic errors into an empty menu.
    return {std::move(candidate)};
  }
};
} // namespace
std::vector<std::string> CandidateCatalog::diagonalImplementations(
    const BindingApplication &application) const {
  return diagonalCandidates(application, installedImplementations());
}
std::vector<std::string>
diagonalCandidates(const BindingApplication &application,
                   const ImplementationCatalog &catalog) {
  auto candidates = diagonalAlternatives(application, catalog);
  if (!candidates) {
    consumeError(candidates.takeError());
    return {};
  }
  std::vector<std::string> result;
  for (const auto &candidate : *candidates) {
    auto installed = resolveDiagonal(candidate, catalog);
    if (!installed) {
      consumeError(installed.takeError());
      continue;
    }
    result.push_back(candidate.implementation);
  }
  return result;
}

Expected<BoundOperation>
resolveDiagonalImplementation(const BindingApplication &application) {
  return resolveDiagonal(application, installedImplementations());
}

const CandidateCatalog &installedCandidates() {
  static const InstalledCandidates catalog;
  return catalog;
}
Error checkDirectConversion(const BindingApplication &application,
                            const BoundType &from, const BoundType &to) {
  auto logical = erasePhysicalType(from);
  bool resident =
      application.contract == "representation.convert" &&
      application.arguments == std::vector<std::string>{logical.spelling()} &&
      application.physicalArguments ==
          std::vector<std::string>{from.spelling(), to.spelling()};
  bool table = from.kind == "table" && to.kind == "table" &&
               application.contract == "table.relayout" &&
               application.arguments ==
                   std::vector<std::string>{from.identity, from.representation,
                                            to.representation};
  if (from.kind != to.kind || from.identity != to.identity ||
      !(erasePhysicalType(from) == erasePhysicalType(to)) || from == to ||
      (!resident && !table))
    return error("binding-no-conversion");
  auto installed = resolveBinding(application, true);
  if (!installed)
    return installed.takeError();
  if (installed->inputs != std::vector<BoundType>{from} ||
      installed->outputs != std::vector<BoundType>{to})
    return error("binding-no-conversion");
  return Error::success();
}
} // namespace zkc::target
