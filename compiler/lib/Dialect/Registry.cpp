#include "zkc/Dialect/Registry.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/BuiltinHeaders.h.inc"
#include "zkc/Dialect/ContributionHeaders.h.inc"

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
#include "zkc/Dialect/BuiltinDialects.inc"
#include "zkc/Dialect/ContributionDialects.inc"
                                    >;
} // namespace
void registerDialects(mlir::DialectRegistry &registry) {
  ProtocolDialects::registerIn(registry);
}
bool hasProtocolDialects(mlir::MLIRContext &context) {
  return ProtocolDialects::loadedIn(context);
}
} // namespace zkc
