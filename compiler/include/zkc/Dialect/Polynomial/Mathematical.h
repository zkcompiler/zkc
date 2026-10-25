#ifndef ZKC_DIALECT_POLYNOMIAL_MATHEMATICAL_H
#define ZKC_DIALECT_POLYNOMIAL_MATHEMATICAL_H

#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Operation.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"

namespace zkc::poly {
// These are implementation admission bounds, not polynomial identities.
inline constexpr uint64_t MaximumPolynomialArity = 32;
inline constexpr uint64_t MaximumDomainLength = 64;

// Closed free-polynomial family consumed by coefficient/evaluation expansion.
// Dialect ownership alone does not make quotient or executable operations part
// of this normalization family.
bool isPolynomialNormalizationOperation(mlir::Operation *operation);

mlir::LogicalResult verifyDomain(mlir::Operation *owner, llvm::StringRef field,
                                 mlir::ArrayAttr points);

class RecipeOp;
class RealizeOp;
mlir::FailureOr<unsigned> recipeDegree(RecipeOp recipe);
mlir::Type residualStateType(RecipeOp recipe);
mlir::FailureOr<mlir::FunctionType> realizationType(RealizeOp realization);

// Derived upper bounds in variable order. Unknown values are never a degree
// certificate. This view belongs to the current SSA and is invalid after edits.
struct Degrees {
  llvm::DenseMap<mlir::Value, llvm::SmallVector<uint64_t>> bounds;
};
// A generic helper with formal polynomial inputs may defer observations whose
// bounds depend on those inputs. Such observations must be checked again after
// call substitution; deferral is never a degree certificate.
mlir::LogicalResult deriveDegrees(mlir::Block &body, Degrees &result,
                                  bool deferUnknownObservations = false);
// Call after degree validation in a verified flat block. Remove dead polynomial
// constructors and observations in reverse SSA order, retaining live bounds.
void eraseUnusedPolynomials(mlir::Block &body, Degrees &degrees);
} // namespace zkc::poly
#endif
