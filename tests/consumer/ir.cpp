#include "zkc/Dialect/IR.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"

// Core IR verifies programmatically built operations without a carrier adapter.
int main() {
  mlir::DialectRegistry registry;
  zkc::registerNativeDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  if (!zkc::hasProtocolDialects(context) ||
      context.getLoadedDialect<zkc::table::TableDialect>())
    return 1;
  mlir::OpBuilder builder(&context);
  mlir::OwningOpRef<mlir::ModuleOp> module(
      mlir::ModuleOp::create(builder.getUnknownLoc()));
  builder.setInsertionPointToEnd(module->getBody());
  mlir::OperationState state(builder.getUnknownLoc(), "protocol.module");
  state.addAttribute("profile",
                     zkc::protocol_ir::ProfileAttr::get(
                         &context, zkc::protocol_ir::Profile::ProtocolExec));
  state.addRegion();
  auto *unit = builder.create(state);
  auto *body = builder.createBlock(&unit->getRegion(0));
  if (mlir::failed(mlir::verify(*module)))
    return 2;
  // A locally valid pure helper is outside the protocol_exec grammar. The
  // mandatory region verifier must reject it even without Translation linked.
  builder.setInsertionPointToEnd(body);
  auto helper =
      mlir::func::FuncOp::create(builder, builder.getUnknownLoc(), "unexpected",
                                 builder.getFunctionType({}, {}));
  helper.setPrivate();
  builder.setInsertionPointToEnd(helper.addEntryBlock());
  mlir::func::ReturnOp::create(builder, builder.getUnknownLoc());
  mlir::ScopedDiagnosticHandler expected(
      &context, [](mlir::Diagnostic &) { return mlir::success(); });
  return mlir::succeeded(mlir::verify(*module)) ? 3 : 0;
}
