#ifndef ZKC_DIALECT_ALGEBRA_PARAMETERS_H
#define ZKC_DIALECT_ALGEBRA_PARAMETERS_H
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Dialect/Algebra/IR/AlgebraAttrs.h"
namespace zkc::algebra {
/// Construct an exact canonical value without parsing or reducing modulo p.
llvm::Expected<FieldLiteralAttr> makeFieldLiteral(FieldType,
                                                  const llvm::APInt &);
/// Whether the exact literal denotes a natural in the prime subfield.
bool isPrimeSubfieldLiteral(FieldLiteralAttr);
/// Decode canonical external literals without reduction or identity coercion.
/// Native consumers inspect FieldLiteralAttr directly, not its byte spelling.
llvm::Expected<FieldLiteralAttr> decodeFieldLiteral(FieldType, llvm::StringRef);
llvm::Expected<std::string> encodeFieldLiteral(FieldLiteralAttr);
/// Explicit Ring interchange boundaries. Order, repeated input nodes, sharing
/// and unused input slots are preserved exactly. This does not authorize a
/// numerical call, change charged work, or grant an algebraic rewrite law.
llvm::Expected<RingExpressionAttr>
importRingExpression(mlir::MLIRContext *, const ring::Expression &);
llvm::Expected<ring::Expression> exportRingExpression(RingExpressionAttr);
/// Canonical Ring bytes and their exact size, read directly from native data.
/// Size admission counts output without building or reparsing a string. This
/// matters because the numerical work contract charges the encoded body size.
llvm::Expected<std::string> encodeRingExpression(RingExpressionAttr);
llvm::Expected<uint64_t> ringExpressionByteSize(RingExpressionAttr);
} // namespace zkc::algebra
#endif
