#include "mlir/IR/Builders.h"
#include "mlir/IR/Diagnostics.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "llvm/Support/raw_ostream.h"

// Exercise the registered hook for every owned operation, including operations
// that no current source fixture happens to use. In particular this catches a
// dialect overriding the strict registration policy in its ODS declaration.
int main() {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  mlir::Builder builder(&context);
  auto unknown = builder.getDictionaryAttr({builder.getNamedAttr(
      "zkc_unrecognized_property", builder.getUnitAttr())});
  std::string diagnostic;
  std::vector<zkc::diagnostics::RefusalInfo> codes;
  mlir::ScopedDiagnosticHandler handler(&context, [&](mlir::Diagnostic &d) {
    codes = zkc::diagnostics::refusals(d);
    llvm::raw_string_ostream stream(diagnostic);
    d.print(stream);
    return mlir::success();
  });
  unsigned checked = 0, failures = 0;
  for (auto name : context.getRegisteredOperations()) {
    if (!llvm::is_contained(
            llvm::ArrayRef<llvm::StringRef>{"pir", "plan", "algebra", "poly",
                                            "pcs", "oracle", "claim",
                                            "relation"},
            name.getDialectNamespace()) ||
        name.getOpPropertyByteSize() == 0)
      continue;
    ++checked;
    // No semantic verification is needed: conversion must reject the unknown
    // key before operands, regions or required property values are inspected.
    mlir::OperationState state(builder.getUnknownLoc(), name);
    auto *operation = mlir::Operation::create(state);
    diagnostic.clear();
    codes.clear();
    auto converted = name.setOpPropertiesFromAttribute(
        name, operation->getPropertiesStorage(), unknown,
        [&] { return mlir::emitError(builder.getUnknownLoc()); });
    operation->destroy();
    if (mlir::succeeded(converted) || codes.size() != 1 ||
        codes[0].code != "mlir-unknown-property") {
      llvm::errs() << name.getStringRef()
                   << ": missing strict property refusal: " << diagnostic
                   << '\n';
      ++failures;
    }
  }
  llvm::outs() << checked << " owned operation property schemas checked\n";
  return failures || checked == 0;
}
