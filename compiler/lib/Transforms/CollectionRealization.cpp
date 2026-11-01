#include "CollectionRealization.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Interfaces/Collection.h"

using namespace mlir;
namespace zkc::mathematical {
std::optional<CollectionRealization> collectionRealization(Type type) {
  auto collection = dyn_cast_if_present<CollectionTypeInterface>(type);
  if (!collection)
    return std::nullopt;
  CollectionRealization result{collection.getElementType(),
                               type,
                               collection.getRank(),
                               collection.getStaticExtent(0),
                               {},
                               {},
                               {},
                               {},
                               {}};
  auto application = [](llvm::StringRef contract,
                        SmallVector<Attribute> arguments = {}) {
    return NativeBindingApplication{contract.str(), std::move(arguments), ""};
  };
  switch (collection.getCollectionKind()) {
  case CollectionKind::FieldVector: {
    auto domain = cast<algebra::FieldType>(result.element).getDomain();
    auto argument = StringAttr::get(type.getContext(), domain);
    result.length = application("vector.length", {argument});
    result.get = application("vector.get", {argument});
    result.empty = application("vector.empty", {argument});
    result.append = application("vector.append", {argument});
    break;
  }
  case CollectionKind::GroupVector: {
    auto domain = cast<algebra::GroupType>(result.element).getDomain();
    auto argument = StringAttr::get(type.getContext(), domain);
    result.length = application("curve.length", {argument});
    result.get = application("curve.get", {argument});
    result.empty = application("curve.empty", {argument});
    result.append = application("curve.append", {argument});
    break;
  }
  case CollectionKind::Indices:
    result.length = application("indices.length");
    result.get = application("indices.at");
    result.empty = application("indices.empty");
    result.append = application("indices.append");
    break;
  case CollectionKind::Sequence: {
    auto argument = TypeAttr::get(result.element);
    result.length = application("sequence.length", {argument});
    result.get = application("sequence.at", {argument});
    result.empty = application("sequence.empty", {argument});
    result.append = application("sequence.append", {argument});
    break;
  }
  case CollectionKind::FieldMatrix: {
    auto domain = cast<algebra::FieldType>(result.element).getDomain();
    auto argument = StringAttr::get(type.getContext(), domain);
    result.length = application("matrix.dimension", {argument});
    result.get = application("matrix.get", {argument});
    break;
  }
  case CollectionKind::FieldArray: {
    auto domain = cast<algebra::FieldType>(result.element).getDomain();
    auto argument = StringAttr::get(type.getContext(), domain);
    auto extent = IntegerAttr::get(
        IntegerType::get(type.getContext(), 64, IntegerType::Unsigned),
        *result.staticExtent);
    result.storage = data::FieldVectorType::get(type.getContext(), domain);
    result.get = application("field_array.get", {argument, extent});
    result.empty = application("vector.empty", {argument});
    result.append = application("vector.append", {argument});
    result.wrap = application("field_array.from_vector", {argument, extent});
    break;
  }
  case CollectionKind::Bytes:
  case CollectionKind::FixedVector:
    return std::nullopt;
  }
  return result;
}
} // namespace zkc::mathematical
