#include "zkc/Contracts/OracleKinds.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Dialect/Protocol/IR/ProtocolTypes.h"
#include "zkc/Dialect/TypeFormation.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol_ir {
namespace {
struct NativeKindSignature {
  Type data, query, answer;
  std::optional<uint64_t> rows;
};
FailureOr<NativeKindSignature>
signature(llvm::function_ref<InFlightDiagnostic()> emit, StringRef identity,
          ArrayAttr arguments) {
  auto refuse = [&](StringRef detail) -> FailureOr<NativeKindSignature> {
    emit() << detail;
    return failure();
  };
  if (identity != "table")
    return refuse("unsupported oracle kind");
  if (!arguments || (arguments.size() != 1 && arguments.size() != 2))
    return refuse("oracle table needs a row type and optional static rows");
  auto row = dyn_cast<TypeAttr>(arguments[0]);
  if (!row || row.getContext() != arguments.getContext() ||
      row.getValue().getContext() != arguments.getContext())
    return refuse("oracle table requires a logical row in its context");
  std::optional<uint64_t> rows;
  if (arguments.size() == 2) {
    auto value = dyn_cast<IntegerAttr>(arguments[1]);
    if (!value || !value.getType().isUnsignedInteger(64) ||
        value.getContext() != arguments.getContext())
      return refuse("oracle table static rows must be ui64");
    rows = value.getValue().getZExtValue();
  }
  auto policy = mathematical::nativeTypePolicy(row.getValue());
  if (!policy || !policy->total || !policy->shared || policy->affine)
    return refuse("oracle table rows require formed total shared data");
  auto interface = dyn_cast<CatalogTypeInterface>(row.getValue());
  auto application =
      interface ? interface.getCatalogApplication() : std::nullopt;
  auto collection = protocol::oracleTableCollectionConstructor(
      application ? application->constructor : StringRef{});
  SmallVector<Attribute> parameters;
  if (collection == "sequence")
    parameters.push_back(row);
  else
    parameters = application->arguments;
  auto data = constructLogicalType(emit, arguments.getContext(),
                                   {collection, parameters});
  auto query =
      constructLogicalType(emit, arguments.getContext(), {"index", {}});
  if (!data || !query)
    return failure();
  return NativeKindSignature{data, query, row.getValue(), rows};
}
FailureOr<NativeKindSignature> signature(OracleKindAttr kind) {
  return signature(
      [&] {
        auto diagnostic = emitError(UnknownLoc::get(kind.getContext()));
        diagnostic.abandon();
        return diagnostic;
      },
      kind.getIdentity(), kind.getArguments());
}
Type associatedType(OracleKindAttr kind, Type NativeKindSignature::*member) {
  auto checked = signature(kind);
  return succeeded(checked) ? (*checked).*member : Type{};
}
} // namespace
LogicalResult
OracleKindAttr::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                       StringRef identity, ArrayAttr arguments) {
  return success(succeeded(signature(emit, identity, arguments)));
}
Type OracleKindAttr::getDataType() const {
  return associatedType(*this, &NativeKindSignature::data);
}
Type OracleKindAttr::getQueryType() const {
  return associatedType(*this, &NativeKindSignature::query);
}
Type OracleKindAttr::getAnswerType() const {
  return associatedType(*this, &NativeKindSignature::answer);
}
std::vector<protocol::OracleShapeDimension>
OracleKindAttr::getShapeDimensions() const {
  auto checked = signature(*this);
  if (failed(checked))
    return {};
  return {{"rows", checked->rows}};
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
