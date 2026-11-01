#ifndef ZKC_DIALECT_RUNTIME_IR_RUNTIMEATTRS_H
#define ZKC_DIALECT_RUNTIME_IR_RUNTIMEATTRS_H
#include "mlir/IR/BuiltinAttributes.h"
#include "zkc/Dialect/Algebra/IR/AlgebraAttrs.h"
#include "zkc/Dialect/Runtime/IR/RuntimeDialect.h"
#include "zkc/Dialect/Runtime/IR/runtimeParameterEnums.h.inc"
namespace zkc::runtime {
class OriginStepAttr;
} // namespace zkc::runtime
#define GET_ATTRDEF_CLASSES
#include "zkc/Dialect/Runtime/IR/runtimeAttrs.h.inc"
#endif
