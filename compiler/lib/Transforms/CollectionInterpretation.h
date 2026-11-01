#ifndef ZKC_TRANSFORMS_COLLECTIONINTERPRETATION_H
#define ZKC_TRANSFORMS_COLLECTIONINTERPRETATION_H

#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include <optional>
#include <string>
#include <vector>

namespace zkc::mathematical {
/// Reader-owned expectations reconstructed from the source's nominal type.
/// This deliberately does not call the producer's collection recipe selector.
/// Candidate readers still check the actual operation, binding, operands,
/// parameters and result types at each occurrence.
struct CollectionInterpretation {
  mlir::Type element;
  llvm::SmallVector<mlir::Attribute> arguments;
  llvm::StringRef length, access, empty, append;
  std::optional<uint64_t> staticExtent;
  bool matrix = false;
};
inline CollectionInterpretation interpretCollection(mlir::Type type) {
  CollectionInterpretation result;
  if (auto vector = mlir::dyn_cast<data::FieldVectorType>(type)) {
    result.element = vector.getElementType();
    result.arguments = {
        mlir::StringAttr::get(type.getContext(), vector.getDomain())};
    result.length = "vector.length";
    result.access = "vector.get";
    result.empty = "vector.empty";
    result.append = "vector.append";
  } else if (auto groups = mlir::dyn_cast<data::GroupVectorType>(type)) {
    result.element = groups.getElementType();
    result.arguments = {
        mlir::StringAttr::get(type.getContext(), groups.getDomain())};
    result.length = "curve.length";
    result.access = "curve.get";
    result.empty = "curve.empty";
    result.append = "curve.append";
  } else if (mlir::isa<data::IndicesType>(type)) {
    result.element = mlir::IntegerType::get(type.getContext(), 64,
                                            mlir::IntegerType::Unsigned);
    result.length = "indices.length";
    result.access = "indices.at";
    result.empty = "indices.empty";
    result.append = "indices.append";
  } else if (auto matrix = mlir::dyn_cast<data::FieldMatrixType>(type)) {
    result.element = matrix.getElementType();
    result.arguments = {
        mlir::StringAttr::get(type.getContext(), matrix.getDomain())};
    result.length = "matrix.dimension";
    result.access = "matrix.get";
    result.matrix = true;
  } else if (auto array = mlir::dyn_cast<data::FieldArrayType>(type)) {
    result.element = array.getElementType();
    result.arguments = {
        mlir::StringAttr::get(type.getContext(), array.getDomain()),
        mlir::IntegerAttr::get(
            mlir::IntegerType::get(type.getContext(), 64,
                                   mlir::IntegerType::Unsigned),
            array.getLength())};
    result.staticExtent = array.getLength();
    result.access = "field_array.get";
  } else if (auto sequence = mlir::dyn_cast<data::SequenceType>(type)) {
    result.element = sequence.getElementType();
    result.arguments = {mlir::TypeAttr::get(result.element)};
    result.length = "sequence.length";
    result.access = "sequence.at";
    result.empty = "sequence.empty";
    result.append = "sequence.append";
  }
  return result;
}
} // namespace zkc::mathematical
#endif
