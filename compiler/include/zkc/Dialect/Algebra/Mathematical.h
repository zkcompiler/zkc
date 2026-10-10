#ifndef ZKC_DIALECT_ALGEBRA_MATHEMATICAL_H
#define ZKC_DIALECT_ALGEBRA_MATHEMATICAL_H

#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Types.h"
#include "mlir/Support/LogicalResult.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringRef.h"
#include <cstdint>
#include <utility>

namespace mlir {
class SymbolTableCollection;
} // namespace mlir
namespace zkc::algebra {
class MapRealizeOp;
// Finite data formation; arrays acquire polynomial meaning only through poly.
inline constexpr uint64_t MaximumArrayLength = 1048576;
bool isFieldArray(mlir::Type type);
bool isCanonicalFieldLiteral(llvm::StringRef field, llvm::StringRef value);
/// The one admitted scalar field of a checked pointwise map signature, or a
/// null type. Rowwise inputs and the single result are dynamic vectors
/// (`tensor<?xF>`); the other inputs are scalars `F`. At least one input must
/// be rowwise. This is formation only; the scalar formula is checked by
/// MapFormulas and by its realization.
mlir::Type mapField(mlir::FunctionType type, llvm::ArrayRef<bool> rowwise);
/// Formation of the scalar formulas that checked maps read. Every operation of
/// the mapped helper and of each helper it calls, used or not, must be a Ring
/// operation in the map's field or a call whose operands and results are that
/// field. Each helper body is read once per field for one verification, without
/// expansion; a refusal ends that verification. The caller first admits the
/// helper closure's structure and bounds. Ring depth and node limits apply to
/// the expanded formula during preparation.
class MapFormulas {
public:
  explicit MapFormulas(mlir::SymbolTableCollection &tables) : tables(tables) {}
  mlir::LogicalResult verify(MapRealizeOp map);

private:
  mlir::SymbolTableCollection &tables;
  llvm::DenseSet<std::pair<mlir::Operation *, mlir::Type>> admitted;
};
} // namespace zkc::algebra
#endif
