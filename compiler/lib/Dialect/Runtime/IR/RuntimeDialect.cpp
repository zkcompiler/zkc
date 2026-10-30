#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeAdapters.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Runtime/IR/runtimeDialect.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Runtime/IR/runtimeTypes.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Runtime/IR/runtimeOps.cpp.inc"
void zkc::runtime::RuntimeDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Runtime/IR/runtimeTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Runtime/IR/runtimeOps.cpp.inc"
      >();
  zkc::protocol::type_adapters::attachCatalogTypeModels(*this);
}

Type zkc::runtime::RepresentedType::parse(AsmParser &parser) {
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
void zkc::runtime::RepresentedType::print(AsmPrinter &printer) const {
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
