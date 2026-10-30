#ifndef ZKC_DIALECT_DATA_IR_DATAATTRS_H
#define ZKC_DIALECT_DATA_IR_DATAATTRS_H
#include "mlir/IR/Attributes.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/Types.h"
#include "zkc/Dialect/Data/IR/DataDialect.h"
namespace zkc::data {
class LayoutAttr;
class LayoutFieldAttr;
class LayoutAlternativeAttr;
} // namespace zkc::data
#define GET_ATTRDEF_CLASSES
#include "zkc/Dialect/Data/IR/dataAttrs.h.inc"
#endif
