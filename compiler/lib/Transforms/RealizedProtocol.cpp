#include "RealizedProtocol.h"
#include "OracleCommonPlan.h"
#include "OracleCommonRealization.h"
#include "OracleNativeCommon.h"
#include "OracleOwnedRealization.h"
#include "OraclePublication.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
OwningOpRef<ModuleOp> boundedSnapshot(ModuleOp subject) {
  if (!subject)
    return {};
  protocol::OracleNativeWork work;
  // Charge the copy as well as inspecting its complete storage first.
  for (unsigned pass = 0; pass < 2; ++pass)
    if (auto e = protocol::boundOracleNativeIR(subject, &work)) {
      consumeError(std::move(e));
      return {};
    }
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(subject->clone()));
}
} // namespace
Expected<RealizedProtocol>
RealizedProtocol::realize(PreparedProtocol prepared,
                          const protocol::OracleRealizationPolicy &policy) {
  auto original = prepared.module.get();
  if (!original)
    return error("oracle-realization-source");
  protocol::OracleNativeWork work;
  auto actual =
      protocol::OracleOwnedRealization::create(original, policy, work);
  if (!actual)
    return actual.takeError();
  // Source admission and the one complete independent pair check precede
  // publication. No mutable subject or caller-supplied evidence enters here.
  for (const auto &root : actual->selections)
    if (!work.charge(1 + root.entry.size() + root.path.size() +
                     root.realization.scheme.size()))
      return error("oracle-common-limit");
  protocol::OracleRealizationPolicy normalized;
  normalized.order = actual->policy.order;
  normalized.authentication = actual->policy.authentication;
  normalized.roots = actual->selections;
  if (!protocol::reserveOraclePolicy(normalized, work))
    return error("oracle-common-limit");
  auto selection = protocol::encodeOracleRealizationPolicy(normalized);
  if (!selection)
    return selection.takeError();
  // Use the selection codec's sorted inventory and deterministic compact JSON
  // printer, matching the C++/Rust wire policy rather than object iteration.
  auto selectionSize = protocol::reserveOraclePublication(*selection, work);
  if (!selectionSize)
    return selectionSize.takeError();
  if (!work.chargeProduct(2, *selectionSize))
    return error("oracle-common-limit");
  ownJsonStrings(*selection);
  auto selectionText = printJson(*selection);
  // Retain a bounded external publication, not an input to native checking.

  auto record = actual->publish(work);

  if (!record)
    return record.takeError();
  // The check's source operation handles belong to the retained source clone.
  // Transfer that exact source as well as its candidate, never a second copy.
  prepared.module = std::move(actual->actual.original);
  return RealizedProtocol(std::move(prepared), std::move(actual->actual.module),
                          std::move(actual->facts), std::move(record->data),
                          std::move(*selection), std::move(record->bytes),
                          std::move(selectionText), std::move(actual->policy));
}
OwningOpRef<ModuleOp> RealizedProtocol::authoredSnapshot() const {
  return boundedSnapshot(prepared.original.get());
}
OwningOpRef<ModuleOp> RealizedProtocol::preparedSnapshot() const {
  return boundedSnapshot(prepared.module.get());
}
OwningOpRef<ModuleOp> RealizedProtocol::candidateSnapshot() const {
  return boundedSnapshot(candidate.get());
}
Expected<RealizedProtocol::ObservationSnapshot>
RealizedProtocol::observationSnapshot() const {
  if (!candidate)
    return error("oracle-realization-source");
  protocol::OracleNativeWork work;
  for (unsigned pass = 0; pass < 2; ++pass)
    if (auto e = protocol::boundOracleNativeIR(candidate.get(), &work))
      return std::move(e);
  IRMapping mapping;
  ObservationSnapshot result{
      OwningOpRef<ModuleOp>(cast<ModuleOp>(candidate.get()->clone(mapping))),
      {}};
  for (Operation *request : facts.openingRequests) {
    if (!work.charge())
      return error("oracle-common-limit");
    auto *copy = mapping.lookupOrNull(request);
    if (!copy)
      return error("oracle-common-body", "missing cloned opening request");
    result.dataExchanges.push_back(copy);
  }
  return result;
}
OwningOpRef<ModuleOp> RealizedProtocol::project(bool simplify) const {
  if (!candidate)
    return {};
  // The actual-body reader established the complete prepared candidate:
  // original ordinary siblings and the closed oracle generation grammar.
  return PreparedProtocol::projectAssociated(candidate.get(), simplify,
                                             prepared.policy);
}
} // namespace zkc::mathematical
