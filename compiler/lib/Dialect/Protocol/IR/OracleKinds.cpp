#include "zkc/Contracts/OracleKinds.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Protocol/IR/ProtocolTypes.h"
#include "llvm/Support/Error.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol_ir {
namespace {
Expected<protocol::OracleKindSignature> signature(StringRef identity,
                                                  ArrayAttr arguments) {
  std::vector<protocol::TypeArgument> typed;
  if (!arguments || arguments.size() > 2)
    return createStringError(inconvertibleErrorCode(),
                             "oracle kind requires typed arguments");
  for (auto argument : arguments) {
    if (auto type = dyn_cast<TypeAttr>(argument)) {
      auto logical = protocol::encodeBoundType(type.getValue(), false);
      if (!logical)
        return logical.takeError();
      if (protocol::decodeBoundType(type.getContext(), *logical) !=
          type.getValue())
        return createStringError(
            inconvertibleErrorCode(),
            "oracle kind requires canonical logical types");
      typed.push_back(
          protocol::TypeArgument::typeArgument(std::move(*logical)));
    } else if (auto natural = dyn_cast<IntegerAttr>(argument);
               natural && natural.getType().isUnsignedInteger(64))
      typed.push_back(protocol::TypeArgument::naturalArgument(
          natural.getValue().getZExtValue()));
    else
      return createStringError(
          inconvertibleErrorCode(),
          "oracle kind arguments must be types or ui64 naturals");
  }
  return protocol::oracleKindSignature(identity, typed);
}
Type associatedType(
    OracleKindAttr kind,
    protocol::BoundType protocol::OracleKindSignature::*member) {
  auto checked = signature(kind.getIdentity(), kind.getArguments());
  if (!checked) {
    consumeError(checked.takeError());
    return {};
  }
  return protocol::decodeBoundType(kind.getContext(), (*checked).*member);
}
} // namespace
LogicalResult
OracleKindAttr::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                       StringRef identity, ArrayAttr arguments) {
  auto checked = signature(identity, arguments);
  if (!checked)
    return emit() << toString(checked.takeError());
  return success();
}
Type OracleKindAttr::getDataType() const {
  return associatedType(*this, &protocol::OracleKindSignature::data);
}
Type OracleKindAttr::getQueryType() const {
  return associatedType(*this, &protocol::OracleKindSignature::query);
}
Type OracleKindAttr::getAnswerType() const {
  return associatedType(*this, &protocol::OracleKindSignature::answer);
}
std::vector<protocol::OracleShapeDimension>
OracleKindAttr::getShapeDimensions() const {
  auto checked = signature(getIdentity(), getArguments());
  if (!checked) {
    consumeError(checked.takeError());
    return {};
  }
  return checked->shape;
}
std::optional<uint64_t> OracleKindAttr::getStaticShape(StringRef name) const {
  for (const auto &dimension : getShapeDimensions())
    if (dimension.name == name)
      return dimension.extent;
  return {};
}
LogicalResult
OracleKindAttr::verifyShapeBounds(llvm::function_ref<InFlightDiagnostic()> emit,
                                  DictionaryAttr bounds) const {
  if (!bounds)
    return emit() << "oracle requires named shape bounds";
  unsigned dynamic = 0;
  for (const auto &dimension : getShapeDimensions()) {
    auto bound = bounds.getAs<IntegerAttr>(dimension.name);
    if (dimension.extent) {
      if (bounds.get(dimension.name))
        return emit() << "static oracle dimension cannot have a dynamic bound";
    } else {
      ++dynamic;
      if (!bound || !bound.getType().isUnsignedInteger(64))
        return emit() << "dynamic oracle dimension requires a named ui64 bound";
    }
  }
  if (bounds.size() != dynamic)
    return emit() << "oracle shape bounds contain an unknown dimension";
  return success();
}
LogicalResult
OracleHandleType::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                         OracleKindAttr kind) {
  if (!kind)
    return emit() << "oracle handle needs a checked kind";
  return OracleKindAttr::verify(emit, kind.getIdentity(), kind.getArguments());
}
LogicalResult
OracleSequenceType::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                           OracleKindAttr kind, uint64_t) {
  // The bound is a logical natural, including zero. Execution admission and
  // append/index checks enforce their own work and size limits.
  return OracleHandleType::verify(emit, kind);
}
} // namespace zkc::protocol_ir
