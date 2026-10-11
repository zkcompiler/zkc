#include "CollectionRealization.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Bindings.h"
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
                        std::vector<std::string> arguments = {}) {
    return protocol::BindingApplication{contract.str(), std::move(arguments),
                                        ""};
  };
  switch (collection.getCollectionKind()) {
  case CollectionKind::FieldVector: {
    auto domain = cast<algebra::FieldType>(result.element).getDomain().str();
    result.length = application("vector.length", {domain});
    result.get = application("vector.get", {domain});
    result.empty = application("vector.empty", {domain});
    result.append = application("vector.append", {domain});
    break;
  }
  case CollectionKind::GroupVector: {
    auto domain = cast<algebra::GroupType>(result.element).getDomain().str();
    result.length = application("curve.length", {domain});
    result.get = application("curve.get", {domain});
    result.empty = application("curve.empty", {domain});
    result.append = application("curve.append", {domain});
    break;
  }
  case CollectionKind::Indices:
    result.length = application("indices.length");
    result.get = application("indices.at");
    result.empty = application("indices.empty");
    result.append = application("indices.append");
    break;
  case CollectionKind::Sequence: {
    auto element = protocol::encodeBoundType(result.element, false);
    if (!element) {
      llvm::consumeError(element.takeError());
      return std::nullopt;
    }
    auto argument = element->spelling();
    result.length = application("sequence.length", {argument});
    result.get = application("sequence.at", {argument});
    result.empty = application("sequence.empty", {argument});
    result.append = application("sequence.append", {argument});
    break;
  }
  case CollectionKind::FieldMatrix: {
    auto domain = cast<algebra::FieldType>(result.element).getDomain().str();
    result.length = application("matrix.dimension", {domain});
    result.get = application("matrix.get", {domain});
    break;
  }
  case CollectionKind::FieldArray: {
    auto domain = cast<algebra::FieldType>(result.element).getDomain().str();
    auto extent = std::to_string(*result.staticExtent);
    result.storage = algebra::FieldVectorType::get(type.getContext(), domain);
    result.get = application("field_array.get", {domain, extent});
    result.empty = application("vector.empty", {domain});
    result.append = application("vector.append", {domain});
    result.wrap = application("field_array.from_vector", {domain, extent});
    break;
  }
  case CollectionKind::Bytes:
  case CollectionKind::FixedVector:
    return std::nullopt;
  }
  return result;
}
} // namespace zkc::mathematical
