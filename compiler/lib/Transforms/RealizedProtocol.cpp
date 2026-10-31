#include "RealizedProtocol.h"
#include "OracleCommonRealization.h"
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
  auto selectionText = printJson(*selection);
  auto actual = protocol::emitOracleRealization(original, policy);
  if (!actual)
    return actual.takeError();
  auto record = protocol::serializeOracleRealization(original, *actual, policy);
  if (!record)
    return record.takeError();
  // Consume the serialized proposal through the separate reader, including
  // rederived interfaces/contracts, actual common SSA and every helper body.
  if (auto failure = protocol::checkOracleRealization(original, *actual->module,
                                                      *record, policy))
    return std::move(failure);
  return RealizedProtocol(std::move(prepared), std::move(actual->module),
                          std::move(*record), std::move(selectionText));
}
OwningOpRef<ModuleOp> RealizedProtocol::originalSnapshot() const {
  return prepared.snapshot();
}
OwningOpRef<ModuleOp> RealizedProtocol::candidateSnapshot() const {
  return candidate
             ? OwningOpRef<ModuleOp>(cast<ModuleOp>(candidate.get()->clone()))
             : OwningOpRef<ModuleOp>();
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
