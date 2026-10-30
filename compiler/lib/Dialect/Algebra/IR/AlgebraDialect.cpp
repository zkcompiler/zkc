#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Algebra/IR/AlgebraAttrs.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/TypeAdapters.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Algebra/IR/algebraDialect.cpp.inc"
#include "zkc/Dialect/Algebra/IR/algebraEnums.cpp.inc"
#define GET_ATTRDEF_CLASSES
#include "zkc/Dialect/Algebra/IR/algebraAttrs.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Algebra/IR/algebraOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Algebra/IR/algebraTypes.cpp.inc"

void zkc::algebra::AlgebraDialect::initialize() {
  addAttributes<
#define GET_ATTRDEF_LIST
#include "zkc/Dialect/Algebra/IR/algebraAttrs.cpp.inc"
      >();
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Algebra/IR/algebraTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Algebra/IR/algebraOps.cpp.inc"
      >();
  zkc::protocol::type_adapters::attachCatalogTypeModels(*this);
}
Operation *zkc::algebra::AlgebraDialect::materializeConstant(
    OpBuilder &builder, Attribute value, Type type, Location location) {
  auto literal = dyn_cast<FieldLiteralAttr>(value);
  if (!literal || literal.getType() != type ||
      failed(FieldLiteralAttr::verify([&] { return emitError(location); },
                                      literal.getField(), literal.getValue())))
    return nullptr;
  return ConstantFieldOp::create(builder, location, type, literal);
}
