#include "mlir/IR/Builders.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Pass/PassRegistry.h"
#include "zkc/Compiler/Pipelines.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Compile.h"
#include "zkc/Frontend/Library.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Target/Source.h"
#include "zkc/Transforms/Passes.h"

int main() {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto field = zkc::FieldType::get(&context, "f7");
  if (field.getDomain() != "f7")
    return 1;
  const zkc::frontend::Input input(
      R"pir(module {
        library(namespace="consumer", name="install", version="1", resolution="test");
        interface Cell {
          type Value copy drop;
          local id(x: Value) -> Value;
        }
        component BoolCell: Cell {
          type Value = bool;
          local id(x: Value) -> Value { return x; }
        }
        fn Client<C: Cell>(x: C::Value) -> C::Value { return C::id(x); }
        link Checked = Client<BoolCell>;
        fn Identity(x: index) -> index { x }
      })pir",
      "consumer.pir");
  auto analysis = zkc::frontend::analyzeProtocol(input);
  auto checked = analysis.checkedModule();
  if (!checked) {
    llvm::consumeError(checked.takeError());
    return 2;
  }
  auto content = zkc::frontend::lower(*checked);
  if (!content) {
    llvm::consumeError(content.takeError());
    return 3;
  }
  zkc::source::Document document(std::move(*content));
  if (auto error = zkc::frontend::checkProtocolDocument(document)) {
    llvm::consumeError(std::move(error));
    return 4;
  }
  // Exercise the installed public library API as well as source elaboration.
  zkc::frontend::library::QualifiedDecl name{
      {"consumer", "install", "1", "test"}, {}, "Client"};
  if (zkc::frontend::library::identity(name).empty())
    return 5;
  // Linking and building pipelines do not implicitly register global passes.
  if (mlir::PassInfo::lookup("lower-pir-to-plan"))
    return 6;
  mlir::PassManager tables(&context), participants(&context);
  zkc::buildTablePipeline(tables, true, "lazy");
  zkc::buildParticipantPipeline(participants);
  if (mlir::PassInfo::lookup("lower-pir-to-plan"))
    return 7;
  zkc::registerCompilerPasses();
  zkc::registerCompilerPipelines();
  zkc::registerCompilerPasses();
  zkc::registerCompilerPipelines();
  if (!mlir::PassInfo::lookup("lower-pir-to-plan"))
    return 8;
  mlir::PassManager registered(&context);
  if (mlir::failed(mlir::parsePassPipeline(
          "builtin.module(zkc-table-pipeline{simplify=true physical=lazy})",
          registered)))
    return 9;
  return 0;
}
