#ifndef ZKC_COMPILER_COMPILATIONSTATE_H
#define ZKC_COMPILER_COMPILATIONSTATE_H
#include "../Transforms/RealizedProtocol.h"
#include "mlir/IR/Location.h"
#include "zkc/Compiler/Compilation.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Transforms/EndpointClosure.h"
namespace zkc {
struct Compilation::Storage {
  mlir::MLIRContext context;
  mlir::OwningOpRef<mlir::ModuleOp> module;
  LinearContractionStats statistics;
  std::shared_ptr<const CheckedEndpoint> endpoint;
  std::shared_ptr<const mathematical::RealizedProtocol> realization;
  explicit Storage(const mlir::DialectRegistry &registry) : context(registry) {
    mlir::DialectRegistry builtins;
    registerDialects(builtins);
    context.appendDialectRegistry(builtins);
    context.printOpOnDiagnostic(false);
  }
};
} // namespace zkc
#endif
