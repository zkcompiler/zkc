#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Runtime/IR/RuntimeAttrs.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeAdapters.h"
#include "zkc/Dialect/TypeFormation.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Runtime/IR/runtimeDialect.cpp.inc"
#include "zkc/Dialect/Runtime/IR/runtimeEnums.cpp.inc"
#include "zkc/Dialect/Runtime/IR/runtimeParameterEnums.cpp.inc"
#define GET_ATTRDEF_CLASSES
#include "zkc/Dialect/Runtime/IR/runtimeAttrs.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Runtime/IR/runtimeTypes.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Runtime/IR/runtimeOps.cpp.inc"
void zkc::runtime::RuntimeDialect::initialize() {
  addAttributes<
#define GET_ATTRDEF_LIST
#include "zkc/Dialect/Runtime/IR/runtimeAttrs.cpp.inc"
      >();
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

LogicalResult zkc::runtime::CapabilityType::verify(
    llvm::function_ref<InFlightDiagnostic()> emit, CapabilityKind kind,
    StringRef identity) {
  if (!symbolizeCapabilityKind(static_cast<uint32_t>(kind)) ||
      (kind == CapabilityKind::ResourceUnit
           ? !protocol::resourceUnitDomain(identity)
           : !protocol::installedDomains().admitsLogicalType(
                 stringifyCapabilityKind(kind), identity)))
    return diagnostics::emit(emit(), "capability-type",
                             "unknown resource kind or nominal identity");
  return success();
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
  return getChecked([&] { return parser.emitError(parser.getNameLoc()); },
                    parser.getContext(), logical, representation, children);
}
LogicalResult zkc::runtime::RepresentedType::verify(
    llvm::function_ref<InFlightDiagnostic()> emit, Type logical,
    StringRef representation, ArrayRef<Type> children) {
  return verifyRepresentedType(emit, logical, representation, children);
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
