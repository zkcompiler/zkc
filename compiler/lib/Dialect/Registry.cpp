#include "zkc/Dialect/Registry.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "zkc/Dialect/BuiltinHeaders.h.inc"
#include "zkc/Dialect/ContributionHeaders.h.inc"
#include "zkc/Interfaces/Mathematical.h"

namespace zkc {
char DialectRegistrationError::ID;
namespace {
template <typename... Dialects> struct DialectSet {
  static void registerIn(mlir::DialectRegistry &registry) {
    registry.insert<Dialects...>();
  }
  static bool loadedIn(mlir::MLIRContext &context) {
    return (bool(context.getLoadedDialect<Dialects>()) && ...);
  }
};
using ProtocolDialects = DialectSet<mlir::func::FuncDialect
#include "zkc/Dialect/ContributionDialects.inc"
#include "zkc/Dialect/NativeDialects.inc"
                                    >;
} // namespace
void registerNativeDialects(mlir::DialectRegistry &registry) {
  ProtocolDialects::registerIn(registry);
  registry.insert<mlir::arith::ArithDialect, mlir::tensor::TensorDialect>();
  registerMathematicalInterfaces(registry);
}
void registerDialects(mlir::DialectRegistry &registry) {
  registerNativeDialects(registry);
  registry.insert<zkc::table::TableDialect>();
}
bool hasProtocolDialects(mlir::MLIRContext &context) {
  return ProtocolDialects::loadedIn(context);
}
} // namespace zkc
