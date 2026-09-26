#include "zkc/Target/Catalog.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Support/Json.h"

using namespace llvm;
using namespace zkc::protocol;
namespace zkc::target {
namespace {
// Derive from the logical contract's semantic facet and installed layout.
// This is deliberately not a second list of supported operation names.
Expected<BindingApplication> diagonalAlternative(BindingApplication source) {
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
  auto family = StringRef(representation->identity).split('.').first;
  source.implementation = (family + "-diagonal/" + source.contract).str();
  return source;
}

class InstalledCandidates final : public CandidateCatalog {
public:
  Expected<std::vector<std::string>>
  implementations(const BindingApplication &application) const override {
    auto fallback = defaultImplementation(application);
    if (!fallback)
      return fallback.takeError();
    return std::vector<std::string>{std::move(*fallback)};
  }
  std::vector<BindingApplication>
  conversions(const BoundType &from, const BoundType &to) const override {
    if (from.kind != "table" || to.kind != "table" ||
        from.identity != to.identity || from == to)
      return {};
    // Contracts currently installs only this adapter. Extending candidate
    // policy cannot extend that cross-language implementation boundary.
    BindingApplication candidate{
        "table.relayout",
        {from.identity, from.representation, to.representation},
        "arkworks/table.relayout"};
    if (auto e = checkDirectConversion(candidate, from, to)) {
      consumeError(std::move(e));
      return {};
    }
    return {std::move(candidate)};
  }
};
} // namespace
std::vector<std::string> CandidateCatalog::diagonalImplementations(
    const BindingApplication &application) const {
  auto candidate = diagonalAlternative(application);
  if (!candidate) {
    consumeError(candidate.takeError());
    return {};
  }
  auto installed = resolveDiagonalImplementation(*candidate);
  if (!installed) {
    consumeError(installed.takeError());
    return {};
  }
  return {candidate->implementation};
}

Expected<BoundOperation>
resolveDiagonalImplementation(const BindingApplication &application) {
  // Full Contracts admission precedes any diagonal-specific checks. In
  // particular, nominal arguments and backend realization remain mandatory.
  auto installed = resolveBinding(application, true);
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

const CandidateCatalog &installedCandidates() {
  static const InstalledCandidates catalog;
  return catalog;
}
Error checkDirectConversion(const BindingApplication &application,
                            const BoundType &from, const BoundType &to) {
  if (from.kind != "table" || to.kind != "table" ||
      from.identity != to.identity || from == to ||
      application.contract != "table.relayout" ||
      application.arguments != std::vector<std::string>{from.identity,
                                                        from.representation,
                                                        to.representation})
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
