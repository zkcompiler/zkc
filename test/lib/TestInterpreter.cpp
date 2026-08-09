//===- TestInterpreter.cpp - interpreter boundary test pass -----*- C++ -*-===//

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Dialect/Oir/OirOps.h"
#include "zkc/Interpreter/ExecutionProfile.h"
#include "zkc/Interpreter/Interpreter.h"

using namespace mlir;

namespace {

/// Exercise the public interpreter API without the zkc-run driver's earlier
/// identity gate. This is test-only plumbing: production receives no bypass or
/// weaker execution mode.
struct TestOirExecutePass
    : public PassWrapper<TestOirExecutePass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestOirExecutePass)

  StringRef getArgument() const override { return "test-oir-execute"; }
  StringRef getDescription() const override {
    return "exercise the public OIR interpreter trust boundary";
  }

  void runOnOperation() override {
    llvm::StringMap<std::string> statement;
    for (zkc::oir::ArtifactOp artifact :
         getOperation().getOps<zkc::oir::ArtifactOp>()) {
      auto result = zkc::interpreter::execute(
          artifact, zkc::interpreter::toyProfile(), statement, {});
      if (!result) {
        artifact.emitOpError() << llvm::toString(result.takeError());
        return signalPassFailure();
      }
    }
  }
};

} // namespace

namespace zkc {
namespace test {
void registerTestInterpreterPass() { PassRegistration<TestOirExecutePass>(); }
} // namespace test
} // namespace zkc
