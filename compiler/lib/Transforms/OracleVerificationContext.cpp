#include "OracleVerificationContext.h"
#include "../Dialect/AdmissionPrivate.h"
#include "OracleNativeCommon.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Support/Refusal.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
mlir::LogicalResult OracleNativeSourcePreflight::admit() const {
  try {
    zkc::detail::NativeTypeWorkScope types(work->types, [&](uint64_t amount) {
      if (!work->charge(amount))
        throw OracleAccountingLimit{};
    });
    if (!work->charge(0))
      return mlir::failure();
    if (admitted)
      return mlir::success();
    if (!reserveTraversal(source))
      return mlir::failure();
    facts::Work control([&](uint64_t amount) { return work->charge(amount); });
    auto closure = std::make_shared<SourceExecutionClosure>();
    if (mlir::failed(
            zkc::detail::admitStageWithWork(source, control, closure.get())))
      return mlir::failure();
    admittedClosure = std::move(closure);
    admitted = true;
    return mlir::success();
  } catch (const OracleAccountingLimit &) {
    return mlir::failure();
  }
}
namespace {
Error reserveContext(ModuleOp module, OracleNativeWork &work,
                     const OracleNativeSourcePreflight &preflight) {
  if (auto e = checkOracleNativePreflight(module, work, &preflight))
    return e;
  // The structural verifier constructs the complete source-execution closure
  // during its charged walk. Retain that exact result instead of traversing
  // the same immutable module again only to reconstruct it for this reader.
  return Error::success();
}
} // namespace
Expected<OracleVerificationContext>
OracleVerificationContext::read(ModuleOp module, OracleNativeWork &work,
                                const OracleNativeSourcePreflight &preflight) {
  return oracleExpectedWithWork(
      work, [&]() -> Expected<OracleVerificationContext> {
        if (auto e = reserveContext(module, work, preflight))
          return std::move(e);
        if (!module || !hasSingleElement(module.getBody()->getOperations()))
          return error("oracle-verification-source");
        auto unit =
            dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
        if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
          return error("oracle-verification-source");
        if (failed(preflight.admit()))
          return error(work.exhausted ? "oracle-common-limit"
                                      : "oracle-verification-source");
        return OracleVerificationContext(
            module, unit, preflight.admittedClosure, work, preflight);
      });
}
Expected<OracleVerificationContext> OracleVerificationContext::readCandidate(
    ModuleOp module, OracleNativeWork &work,
    const OracleNativeSourcePreflight &preflight) {
  return oracleExpectedWithWork(
      work, [&]() -> Expected<OracleVerificationContext> {
        if (auto e = reserveContext(module, work, preflight))
          return std::move(e);
        if (!module || !hasSingleElement(module.getBody()->getOperations()))
          return error("oracle-verification-source");
        auto unit =
            dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
        if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
          return error("oracle-verification-source");
        if (!preflight.reserveTraversal(module))
          return error("oracle-common-limit");
        zkc::detail::NativeTypeWorkScope types(
            work.types, [&](uint64_t amount) {
              if (!work.charge(amount))
                throw OracleAccountingLimit{};
            });
        auto closure = std::make_shared<SourceExecutionClosure>();
        if (failed(zkc::detail::verifyStageStructure(module, closure.get())))
          return error("oracle-verification-source");
        return OracleVerificationContext(module, unit, std::move(closure), work,
                                         preflight);
      });
}
Expected<OracleVerificationContext>
OracleVerificationContext::read(ModuleOp module) {
  auto work = std::make_shared<OracleNativeWork>();
  auto bounded = OracleNativeSourcePreflight::read(module, *work);
  if (!bounded)
    return bounded.takeError();
  auto preflight =
      std::make_shared<OracleNativeSourcePreflight>(std::move(*bounded));
  auto result = read(module, *work, *preflight);
  if (!result)
    return result.takeError();
  result->ownedWork = std::move(work);
  result->ownedPreflight = std::move(preflight);
  return result;
}
Expected<OracleVerificationContext>
OracleVerificationContext::readCandidate(ModuleOp module) {
  auto work = std::make_shared<OracleNativeWork>();
  auto bounded = OracleNativeSourcePreflight::read(module, *work);
  if (!bounded)
    return bounded.takeError();
  auto preflight =
      std::make_shared<OracleNativeSourcePreflight>(std::move(*bounded));
  auto result = readCandidate(module, *work, *preflight);
  if (!result)
    return result.takeError();
  result->ownedWork = std::move(work);
  result->ownedPreflight = std::move(preflight);
  return result;
}
Expected<OracleVerificationContext>
OracleVerificationContext::read(ModuleOp module, OracleNativeWork &work) {
  auto bounded = OracleNativeSourcePreflight::read(module, work);
  if (!bounded)
    return bounded.takeError();
  auto preflight =
      std::make_shared<OracleNativeSourcePreflight>(std::move(*bounded));
  auto result = read(module, work, *preflight);
  if (!result)
    return result.takeError();
  result->ownedPreflight = std::move(preflight);
  return result;
}
Expected<OracleVerificationContext>
OracleVerificationContext::readCandidate(ModuleOp module,
                                         OracleNativeWork &work) {
  auto bounded = OracleNativeSourcePreflight::read(module, work);
  if (!bounded)
    return bounded.takeError();
  auto preflight =
      std::make_shared<OracleNativeSourcePreflight>(std::move(*bounded));
  auto result = readCandidate(module, work, *preflight);
  if (!result)
    return result.takeError();
  result->ownedPreflight = std::move(preflight);
  return result;
}
Expected<SmallVector<CommonControlRequirement>>
OracleVerificationContext::complete(
    protocol_ir::ProtocolModuleOp original,
    ArrayRef<zkc::detail::OracleRepeatCount> counts, facts::Work &work) const {
  for (const auto &count : counts)
    if (!work.charge() || count.candidate != module ||
        count.source != original->getParentOfType<ModuleOp>() ||
        count.originalEntry->getParentOp() != original.getOperation())
      return error(work.exhausted() ? "common-control-capacity"
                                    : "common-control-provenance");
  zkc::detail::OracleCountEquations equations(original, counts);
  return zkc::detail::completeCommonControl(unit, work, &equations);
}
} // namespace zkc::protocol
