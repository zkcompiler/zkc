#include "OraclePrivateComposite.h"
#include "OracleEmissionAccounting.h"
#include "OracleVerificationContext.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
OraclePrivateComposite::OraclePrivateComposite(OwningOpRef<ModuleOp> candidate,
                                               OracleVirtualFunctionWork work)
    : candidate(std::move(candidate)), work(std::move(work)) {
  this->work.scratch = *this->candidate;
}
OraclePrivateComposite::~OraclePrivateComposite() = default;

Expected<std::unique_ptr<OraclePrivateComposite>>
OraclePrivateComposite::create(OwningOpRef<ModuleOp> candidate,
                               ModuleOp prepared,
                               OracleVirtualFunctionWork work) {
  return begin(std::move(candidate), prepared, std::move(work));
}

Expected<std::unique_ptr<OraclePrivateComposite>>
OraclePrivateComposite::begin(OwningOpRef<ModuleOp> candidate,
                              ModuleOp prepared,
                              OracleVirtualFunctionWork work) {
  if (!candidate || !prepared ||
      candidate.get()->getContext() != prepared.getContext() ||
      !hasSingleElement(candidate->getBody()->getOperations()))
    return error("oracle-common-body");
  auto result = std::unique_ptr<OraclePrivateComposite>(
      new OraclePrivateComposite(std::move(candidate), std::move(work)));
  return oracleExpectedWithWork(
      result->work.getWork(),
      [&]() -> Expected<std::unique_ptr<OraclePrivateComposite>> {
        auto sourceBound =
            OracleNativeSourcePreflight::read(prepared, result->work.getWork());
        if (!sourceBound)
          return sourceBound.takeError();
        if (!sourceBound->reserveTraversal(prepared))
          return error("oracle-common-limit");
        result->source =
            OwningOpRef<ModuleOp>(cast<ModuleOp>(prepared->clone()));
        auto retained = OracleNativeSourcePreflight::read(
            *result->source, result->work.getWork());
        if (!retained)
          return retained.takeError();
        if (failed(retained->admit()))
          return error("oracle-common-body");
        result->sourcePreflight =
            std::make_unique<OracleNativeSourcePreflight>(std::move(*retained));
        result->work.source = result->sourcePreflight.get();
        auto unit = dyn_cast<protocol_ir::ProtocolModuleOp>(
            result->candidate->getBody()->front());
        if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
          return error("oracle-common-body");
        result->emission = std::make_unique<OracleEmissionSession>(
            result->work.getWork(), unit);
        result->emission->own();
        return std::move(result);
      });
}

Expected<OracleQueryController> OraclePrivateComposite::controller(
    const OracleAnchorStorage &storage, StringRef role,
    protocol_ir::OracleKindAttr root, OracleQuerySize capacity,
    OracleControllerAccess access) {
  return emitOracleQueryController(*candidate, *source, storage, role, root,
                                   capacity, work, access);
}
Expected<OracleMerkleFunctions>
OraclePrivateComposite::merkle(protocol_ir::OracleKindAttr kind,
                               StringRef scheme, OracleLeafGrouping grouping,
                               OracleLeafOrder order) {
  return emitOracleMerkleWithWork(*candidate, kind, scheme, grouping, order,
                                  work.getWork());
}
Expected<OracleQueryResponse>
OraclePrivateComposite::response(const OracleQueryExchange &exchange) {
  return emitOracleQueryResponse(*candidate, exchange, work);
}
Expected<OracleQueryDemand>
OraclePrivateComposite::demand(const OracleAnchorStorage &storage,
                               const OracleQueryController &controller,
                               protocol_ir::OracleKindAttr root) {
  return emitOracleQueryDemand(*candidate, storage, controller, root, work);
}
Expected<OracleQueryWindow> OraclePrivateComposite::window(
    const OracleQueryController &controller, const OracleQueryDemand &demand,
    const OracleQueryExchange &exchange, const OracleQueryResponse &response,
    uint64_t capacity) {
  return emitOracleQueryWindow(*candidate, controller, demand, exchange,
                               response, capacity, work);
}
Expected<OracleQueryBatch>
OraclePrivateComposite::batch(ArrayRef<OracleQueryBatchRoot> roots) {
  return emitOracleQueryBatch(*candidate, roots, work);
}
Expected<OraclePrivateComposite::Finished> OraclePrivateComposite::finish() {
  return oracleExpectedWithWork(work.getWork(), [&]() -> Expected<Finished> {
    emission->finish();
    emission.reset();
    work.scratch = {};
    work.source = nullptr;
    auto checked = OracleVerificationContext::read(*candidate, work.getWork());
    if (!checked)
      return checked.takeError();
    return Finished{std::move(candidate), std::move(work)};
  });
}
} // namespace zkc::protocol
