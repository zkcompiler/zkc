//===- PirTypes.cpp - Protocol IR types -------------------------*- C++ -*-===//
#include "zkc/Dialect/Pir/PirTypes.h"

#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Pir/PirDialect.h"
#include "llvm/ADT/TypeSwitch.h"

#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Pir/PirOpsTypes.cpp.inc"

/// `!pir.val<"scalar">` or `!pir.val<profile "logup_column">`.
///
/// The marker is a keyword rather than an inferred property of the string:
/// resolving a name against the vocabulary and falling back to "it must be a
/// class" would turn a mistyped profile into a class nobody declared, which
/// is the one failure mode a closed registry exists to prevent.
mlir::Type zkc::pir::ValType::parse(mlir::AsmParser &parser) {
  if (parser.parseLess())
    return {};
  bool profiled = succeeded(parser.parseOptionalKeyword("profile"));
  std::string name;
  if (parser.parseString(&name) || parser.parseGreater())
    return {};
  return ValType::get(parser.getContext(), name, profiled);
}

void zkc::pir::ValType::print(mlir::AsmPrinter &printer) const {
  printer << "<";
  if (getProfiled())
    printer << "profile ";
  printer << "\"" << getValueClass() << "\">";
}

void zkc::pir::PirDialect::registerTypes() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Pir/PirOpsTypes.cpp.inc"
      >();
}
