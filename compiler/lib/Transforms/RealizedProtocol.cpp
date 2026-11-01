#include "RealizedProtocol.h"
#include "OracleCommonRealization.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
Expected<RealizedProtocol>
RealizedProtocol::realize(PreparedProtocol prepared,
                          const protocol::OracleRealizationPolicy &policy) {
  auto original = prepared.module.get();
  if (!original)
    return error("oracle-realization-source");
  auto roots = protocol::resolveOracleRealizationSelection(original, policy);
  if (!roots)
    return roots.takeError();
  auto normalized = policy;
  normalized.roots = std::move(*roots);
  auto selection = protocol::encodeOracleRealizationPolicy(normalized);
  if (!selection)
    return selection.takeError();
  // Use the selection codec's sorted inventory and deterministic compact JSON
  // printer, matching the C++/Rust wire policy rather than object iteration.
  ownJsonStrings(*selection);
  auto selectionText = printJson(*selection);
  auto actual = protocol::emitOracleRealization(original, policy);
  if (!actual)
    return actual.takeError();
  auto facts = protocol::checkOracleRealization(original, *actual, policy);
  if (!facts)
    return facts.takeError();
  // Retain a bounded external publication, not an input to native checking.
  auto record = protocol::exportOracleRealization(original, *actual, policy);
  if (!record)
    return record.takeError();
  return RealizedProtocol(std::move(prepared), std::move(actual->module),
                          std::move(*facts), std::move(record->data),
                          std::move(*selection), std::move(record->bytes),
                          std::move(selectionText), policy);
}
OwningOpRef<ModuleOp> RealizedProtocol::authoredSnapshot() const {
  return prepared.originalSnapshot();
}
OwningOpRef<ModuleOp> RealizedProtocol::preparedSnapshot() const {
  return prepared.snapshot();
}
OwningOpRef<ModuleOp> RealizedProtocol::candidateSnapshot() const {
  return candidate
             ? OwningOpRef<ModuleOp>(cast<ModuleOp>(candidate.get()->clone()))
             : OwningOpRef<ModuleOp>();
}
Expected<RealizedProtocol::ObservationSnapshot>
RealizedProtocol::observationSnapshot() const {
  if (!candidate)
    return error("oracle-realization-source");
  IRMapping mapping;
  ObservationSnapshot result{
      OwningOpRef<ModuleOp>(cast<ModuleOp>(candidate.get()->clone(mapping))),
      {}};
  for (Operation *request : facts.openingRequests) {
    auto *copy = mapping.lookupOrNull(request);
    if (!copy)
      return error("oracle-common-body", "missing cloned opening request");
    result.dataExchanges.push_back(copy);
  }
  return result;
}
OwningOpRef<ModuleOp> RealizedProtocol::project(bool simplify) const {
  auto actual = candidateSnapshot();
  if (!actual)
    return {};
  // The actual-body reader established the complete prepared candidate:
  // original ordinary siblings and the closed oracle generation grammar.
  return PreparedProtocol::projectOwned(std::move(actual), simplify,
                                        prepared.policy);
}
} // namespace zkc::mathematical
