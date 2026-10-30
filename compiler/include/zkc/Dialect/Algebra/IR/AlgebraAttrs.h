#ifndef ZKC_DIALECT_ALGEBRA_IR_ALGEBRAATTRS_H
#define ZKC_DIALECT_ALGEBRA_IR_ALGEBRAATTRS_H
#include "mlir/IR/BuiltinAttributes.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Algebra/IR/algebraEnums.h.inc"
namespace zkc::algebra {
class FieldLiteralAttr;
class RingNodeAttr;
} // namespace zkc::algebra
#define GET_ATTRDEF_CLASSES
#include "zkc/Dialect/Algebra/IR/algebraAttrs.h.inc"
#endif
