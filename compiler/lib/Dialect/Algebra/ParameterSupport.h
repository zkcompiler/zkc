#ifndef ZKC_DIALECT_ALGEBRA_PARAMETERSUPPORT_H
#define ZKC_DIALECT_ALGEBRA_PARAMETERSUPPORT_H
#include "zkc/Dialect/Algebra/IR/AlgebraAttrs.h"
#include <optional>
namespace zkc::algebra {
struct LiteralPresentation {
  llvm::APInt modulus;
  unsigned width;
  bool binary;
};
std::optional<LiteralPresentation> literalPresentation(FieldType);
bool isPrimeSubfieldLiteral(FieldLiteralAttr);
} // namespace zkc::algebra
#endif
