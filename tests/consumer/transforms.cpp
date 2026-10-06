#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Pass/PassRegistry.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"

// This client constructs SSA directly and links no frontend or translation.
int main() {
  mlir::DialectRegistry registry;
  zkc::registerNativeDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  mlir::OpBuilder builder(&context);
  auto location = builder.getUnknownLoc();
  mlir::OwningOpRef<mlir::ModuleOp> module(mlir::ModuleOp::create(location));
  builder.setInsertionPointToEnd(module->getBody());
  mlir::OperationState root(location, "protocol.module");
  root.addAttribute("profile",
                    zkc::protocol_ir::ProfileAttr::get(
                        &context, zkc::protocol_ir::Profile::Protocol));
  root.addRegion();
  auto *unit = builder.create(root);
  builder.createBlock(&unit->getRegion(0));
  mlir::OperationState definition(location, "protocol.func");
  auto roles = builder.getStrArrayAttr({"P"});
  definition.addAttribute("sym_name", builder.getStringAttr("main"));
  definition.addAttribute(
      "function_type",
      mlir::TypeAttr::get(builder.getFunctionType({}, {builder.getI1Type()})));
  definition.addAttribute("roles", roles);
  definition.addAttribute("input_roles", builder.getArrayAttr({}));
  definition.addAttribute("output_roles", builder.getArrayAttr({roles}));
  definition.addRegion();
  auto *function = builder.create(definition);
  builder.createBlock(&function->getRegion(0));
  auto value = mlir::arith::ConstantOp::create(builder, location,
                                               builder.getBoolAttr(true));
  zkc::protocol_ir::MathematicalReturnOp::create(
      builder, location, mlir::ValueRange{value.getResult()});
  mlir::PassManager pipeline(&context);
  pipeline.addPass(zkc::protocol::createProjectProtocolPass());
  pipeline.addPass(zkc::protocol::createSimplifyParticipantPass());
  if (failed(pipeline.run(*module)))
    return 1;
  mlir::OwningOpRef<mlir::ModuleOp> original(
      mlir::cast<mlir::ModuleOp>(module->clone()));
  mlir::PassManager lowering(&context);
  lowering.addPass(zkc::protocol::createLowerMathPass());
  if (failed(lowering.run(*module)) ||
      failed(zkc::mathematical::verifyProjectionPreserved(*original, *module)))
    return 1;
  pipeline.clear();
  pipeline.addPass(zkc::protocol::createSelectPhysicalPass());
  if (failed(pipeline.run(*module)) || failed(mlir::verify(*module)))
    return 1;
  // Passes publish a new body in the builtin module; reacquire its unit.
  auto scope = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
      module->getBody()->front());
  if (scope.getProfile() != zkc::protocol_ir::Profile::Physical ||
      scope.getExecutionContract() !=
          zkc::protocol_ir::ExecutionContract::Program)
    return 2;
  unsigned literals = 0;
  module->walk([&](zkc::plan::BoolConstantOp) { ++literals; });
  if (literals != 1)
    return 3;
  mlir::OwningOpRef<mlir::ModuleOp> changed(
      mlir::cast<mlir::ModuleOp>(module->clone()));
  changed->walk([&](zkc::plan::BoolConstantOp value) {
    value->setAttr("value", builder.getBoolAttr(false));
  });
  if (failed(mlir::verify(*changed)))
    return 4;
  mlir::ScopedDiagnosticHandler expected(
      &context, [](mlir::Diagnostic &) { return mlir::success(); });
  if (succeeded(
          zkc::mathematical::verifyProjectionPreserved(*module, *changed)))
    return 5;
  return mlir::PassInfo::lookup("zkc-lower-math") ? 6 : 0;
}
