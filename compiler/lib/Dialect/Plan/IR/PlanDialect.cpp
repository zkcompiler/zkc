#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Plan/IR/PlanOps.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Plan/IR/planDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Plan/IR/planOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Plan/IR/planTypes.cpp.inc"

void zkc::plan::PlanDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Plan/IR/planTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Plan/IR/planOps.cpp.inc"
      >();
}

LogicalResult zkc::plan::BoolConstantOp::verify() {
  auto type = zkc::protocol::encodeBoundType(getOutput().getType(), true);
  if (!type) {
    llvm::consumeError(type.takeError());
    return zkc::diagnostics::emit(emitOpError(), "native-boolean-type");
  }
  if (type->spelling() != "bool@native.bool/0")
    return zkc::diagnostics::emit(emitOpError(), "native-boolean-type");
  return success();
}

Type zkc::plan::DataType::parse(AsmParser &parser) {
  Type logical;
  std::string representation;
  SmallVector<Type> children;
  if (parser.parseLess() || parser.parseType(logical) || parser.parseComma() ||
      parser.parseString(&representation))
    return {};
  if (succeeded(parser.parseOptionalComma())) {
    if (parser.parseLSquare())
      return {};
    if (failed(parser.parseOptionalRSquare())) {
      if (parser.parseCommaSeparatedList([&]() {
            Type child;
            if (parser.parseType(child))
              return failure();
            children.push_back(child);
            return success();
          }) ||
          parser.parseRSquare())
        return {};
    }
  }
  if (parser.parseGreater())
    return {};
  auto type = get(parser.getContext(), logical, representation, children);
  auto admitted = zkc::protocol::encodeBoundType(type, true);
  if (!admitted) {
    parser.emitError(parser.getNameLoc(), llvm::toString(admitted.takeError()));
    return {};
  }
  return type;
}
void zkc::plan::DataType::print(AsmPrinter &printer) const {
  printer << "<" << getLogical() << ", ";
  printer.printString(getRepresentation());
  if (!getChildren().empty()) {
    printer << ", [";
    llvm::interleaveComma(getChildren(), printer,
                          [&](Type child) { printer << child; });
    printer << "]";
  }
  printer << ">";
}
