#include "zkc/Contracts/Domains.h"
#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"

using namespace mlir;
namespace zkc::protocol::type_adapters {
namespace {
// These facts select native carriers, not admission. Neither an unknown scheme
// nor a scheme with conflicting carrier facts has an implicit PCS fallback.
enum class Carrier { Missing, PCS, Oracle };
Carrier carrierFor(llvm::StringRef identity) {
  const auto &domains = installedDomains();
  bool pcs = domains.hasFact("MultilinearOpening", {identity.str()});
  bool oracle = domains.hasFact("VectorCommitment", {identity.str()});
  if (pcs == oracle)
    return Carrier::Missing;
  return pcs ? Carrier::PCS : Carrier::Oracle;
}

template <bool AllowPCS, bool AllowOracle>
Type decodeObject(MLIRContext *context, const BoundType &type) {
  auto carrier = carrierFor(type.identity);
  if (AllowPCS && carrier == Carrier::PCS)
    return loadedType<ObjectType>(context, type.identity, type.kind);
  if (AllowOracle && carrier == Carrier::Oracle)
    return loadedType<OracleObjectType>(context, type.identity, type.kind);
  return {};
}

template <bool AllowPCS, bool AllowOracle>
std::optional<BoundType> encodeObject(Type type, llvm::StringRef constructor) {
  if constexpr (AllowPCS)
    if (auto object = dyn_cast<ObjectType>(type))
      if (object.getKind() == constructor &&
          carrierFor(object.getScheme()) == Carrier::PCS)
        return BoundType{constructor.str(), object.getScheme().str(), {}};
  if constexpr (AllowOracle)
    if (auto object = dyn_cast<OracleObjectType>(type))
      if (object.getKind() == constructor &&
          carrierFor(object.getScheme()) == Carrier::Oracle)
        return BoundType{constructor.str(), object.getScheme().str(), {}};
  return std::nullopt;
}

} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Commitment.inc"
