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
Type constructObject(llvm::function_ref<InFlightDiagnostic()> emit,
                     MLIRContext *context, llvm::StringRef constructor,
                     llvm::ArrayRef<Attribute> arguments) {
  auto scheme = cast<StringAttr>(arguments[0]).getValue();
  auto carrier = carrierFor(scheme);
  if (AllowPCS && carrier == Carrier::PCS)
    return loadedCheckedType<zkc::commitment::PolynomialObjectType>(
        emit, context, scheme, constructor);
  if (AllowOracle && carrier == Carrier::Oracle)
    return loadedCheckedType<zkc::commitment::VectorObjectType>(
        emit, context, scheme, constructor);
  return {};
}

template <bool AllowPCS, bool AllowOracle>
Type decodeObject(MLIRContext *context, const BoundType &type) {
  auto carrier = carrierFor(type.identity);
  if (AllowPCS && carrier == Carrier::PCS)
    return loadedType<zkc::commitment::PolynomialObjectType>(
        context, type.identity, type.kind);
  if (AllowOracle && carrier == Carrier::Oracle)
    return loadedType<zkc::commitment::VectorObjectType>(context, type.identity,
                                                         type.kind);
  return {};
}

template <bool AllowPCS, bool AllowOracle>
std::optional<llvm::StringRef> objectScheme(Type type,
                                            llvm::StringRef constructor) {
  if constexpr (AllowPCS)
    if (auto object = dyn_cast<zkc::commitment::PolynomialObjectType>(type))
      if (object.getKind() == constructor &&
          carrierFor(object.getScheme()) == Carrier::PCS)
        return object.getScheme();
  if constexpr (AllowOracle)
    if (auto object = dyn_cast<zkc::commitment::VectorObjectType>(type))
      if (object.getKind() == constructor &&
          carrierFor(object.getScheme()) == Carrier::Oracle)
        return object.getScheme();
  return std::nullopt;
}
template <bool AllowPCS, bool AllowOracle>
std::optional<llvm::SmallVector<Attribute>>
objectArguments(Type type, llvm::StringRef constructor) {
  auto scheme = objectScheme<AllowPCS, AllowOracle>(type, constructor);
  if (!scheme)
    return std::nullopt;
  return llvm::SmallVector<Attribute>{
      StringAttr::get(type.getContext(), *scheme)};
}
template <bool AllowPCS, bool AllowOracle>
std::optional<BoundType> encodeObject(Type type, llvm::StringRef constructor) {
  auto scheme = objectScheme<AllowPCS, AllowOracle>(type, constructor);
  if (!scheme)
    return std::nullopt;
  return BoundType{constructor.str(), scheme->str(), {}};
}

} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Commitment.inc"
