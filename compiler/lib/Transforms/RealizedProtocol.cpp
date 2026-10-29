#include "RealizedProtocol.h"
#include "OracleCommonRealization.h"
#include "zkc/Support/Refusal.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
Expected<RealizedProtocol> RealizedProtocol::ideal(PreparedProtocol prepared) {
  auto original = std::move(prepared.module);
  if (!original)
    return error("oracle-realization-source");
  auto actual = protocol::emitIdealOracleRealization(*original);
  if (!actual)
    return actual.takeError();
  auto record = protocol::serializeIdealOracleRealization(*original, *actual);
  if (!record)
    return record.takeError();
  // Consume the serialized proposal through the separate reader, including
  // rederived interfaces/contracts, actual common SSA and every helper body.
  if (auto failure = protocol::checkIdealOracleRealization(
          *original, *actual->module, *record))
    return std::move(failure);
  return RealizedProtocol(std::move(original), std::move(actual->module),
                          std::move(*record));
}
OwningOpRef<ModuleOp> RealizedProtocol::originalSnapshot() const {
  return original
             ? OwningOpRef<ModuleOp>(cast<ModuleOp>(original.get()->clone()))
             : OwningOpRef<ModuleOp>();
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
  return PreparedProtocol(std::move(actual)).project(simplify);
}
} // namespace zkc::mathematical
