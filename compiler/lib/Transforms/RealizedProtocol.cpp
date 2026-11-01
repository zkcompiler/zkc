#include "RealizedProtocol.h"
#include "OracleCommonRealization.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringSet.h"

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
  ObservationSnapshot result{candidateSnapshot(), {}};
  if (!result.module)
    return error("oracle-realization-source");
  // This record is the private owner's checked edge, never caller-supplied
  // evidence. Its exact vocabulary and all candidate bodies were rederived by
  // checkOracleRealization before this owner could be constructed.
  auto decoded = json::parse(record);
  if (!decoded)
    return decoded.takeError();
  auto *root = decoded->getAsObject();
  auto *entries = root ? root->getArray("entries") : nullptr;
  if (!entries)
    return error("oracle-realization-record");
  auto unit =
      cast<protocol_ir::ProtocolModuleOp>(result.module->getBody()->front());
  SymbolTable symbols(unit);
  for (const auto &entry : *entries) {
    auto *row = entry.getAsObject();
    auto name = row ? row->getString("entry") : std::nullopt;
    auto *occurrences = row ? row->getArray("occurrences") : nullptr;
    if (!name || !occurrences)
      return error("oracle-realization-record");
    auto function = symbols.lookup<protocol_ir::MathematicalOp>(*name);
    if (!function)
      return error("oracle-realization-record");
    llvm::StringSet<> requests;
    for (const auto &occurrence : *occurrences) {
      auto *item = occurrence.getAsObject();
      if (item && item->getString("purpose") == "opening_request") {
        auto site = item->getString("site");
        if (!site || !requests.insert(*site).second)
          return error("oracle-realization-record");
      }
    }
    function.walk([&](protocol_ir::ExchangeOp exchange) {
      if (requests.erase(exchange.getSite()))
        result.dataExchanges.push_back(exchange);
    });
    if (!requests.empty())
      return error("oracle-realization-record");
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
