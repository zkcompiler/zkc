//===- TestSealEngine.cpp - direct seal-engine adapter --------------------===//

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Registry/ProtocolEnvironment.h"
#include "zkc/Semantics/SealEngine.h"
#include "llvm/Support/Error.h"

#include <string>

using namespace mlir;

namespace {

struct TestSealEnginePass
    : public PassWrapper<TestSealEnginePass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestSealEnginePass)

  TestSealEnginePass() = default;
  TestSealEnginePass(const TestSealEnginePass &other) : PassWrapper(other) {}

  StringRef getArgument() const override { return "test-seal-engine-direct"; }
  StringRef getDescription() const override {
    return "seal open PIR through the library-level SealEngine";
  }

  Option<std::string> protocolVocabularyPath{
      *this, "protocol-vocabulary", llvm::cl::desc("protocol vocabulary")};
  Option<std::string> constructionProfileRegistryPath{
      *this, "construction-profile-registry",
      llvm::cl::desc("construction-profile registry")};

  void runOnOperation() override {
    ModuleOp module = getOperation();
    auto environment = zkc::registry::ProtocolEnvironment::loadFromFiles(
        protocolVocabularyPath, constructionProfileRegistryPath);
    if (!environment) {
      module.emitError() << llvm::toString(environment.takeError());
      return signalPassFailure();
    }

    SmallVector<zkc::pir::ProtocolOp> protocols(
        module.getOps<zkc::pir::ProtocolOp>());
    if (protocols.empty()) {
      module.emitError() << "test-seal-engine-direct found no open protocol";
      return signalPassFailure();
    }

    zkc::semantics::SealEngine engine(*environment);
    for (zkc::pir::ProtocolOp protocol : protocols)
      if (failed(engine.seal(protocol)))
        signalPassFailure();
  }
};

} // namespace

namespace zkc::test {
void registerTestSealEnginePass() { PassRegistration<TestSealEnginePass>(); }
} // namespace zkc::test
