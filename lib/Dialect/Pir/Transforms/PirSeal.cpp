//===- PirSeal.cpp - pass adapters for the seal engine ----------*- C++ -*-===//

#include "zkc/Dialect/Pir/Transforms/Passes.h"

#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Registry/ProtocolEnvironment.h"
#include "zkc/Semantics/SealEngine.h"

namespace zkc::pir {

#define GEN_PASS_DEF_PIRSEAL
#define GEN_PASS_DEF_PIRRECHECK
#include "zkc/Dialect/Pir/Transforms/Passes.h.inc"

} // namespace zkc::pir

using namespace llvm;
using namespace mlir;

namespace {

FailureOr<zkc::registry::ProtocolEnvironment>
loadEnvironment(ModuleOp module, StringRef boundary,
                StringRef protocolVocabularyPath,
                StringRef constructionProfilePath) {
  if (protocolVocabularyPath.empty()) {
    module.emitError() << "[zkc-E248] " << boundary
                       << " requires a protocol-vocabulary authority";
    return failure();
  }
  auto environment = zkc::registry::ProtocolEnvironment::loadFromFiles(
      protocolVocabularyPath, constructionProfilePath);
  if (!environment) {
    module.emitError() << boundary << ": " << toString(environment.takeError());
    return failure();
  }
  return std::move(*environment);
}

class PirSealPass : public zkc::pir::impl::PirSealBase<PirSealPass> {
public:
  using PirSealBase::PirSealBase;

  void runOnOperation() override {
    SmallVector<zkc::pir::SealedOp> authoredSealed(
        getOperation().getOps<zkc::pir::SealedOp>());
    if (!authoredSealed.empty()) {
      getOperation().emitError()
          << "[zkc-E202] pir-seal accepts open pir.protocol roots only; "
             "pre-existing pir.sealed is never seal input";
      return signalPassFailure();
    }

    SmallVector<zkc::pir::ProtocolOp> protocols(
        getOperation().getOps<zkc::pir::ProtocolOp>());
    if (protocols.empty()) {
      getOperation().emitError()
          << "[zkc-E202] pir-seal found no open pir.protocol to judge";
      return signalPassFailure();
    }

    auto environment =
        loadEnvironment(getOperation(), "pir-seal", protocolVocabulary,
                        constructionProfileRegistry);
    if (failed(environment))
      return signalPassFailure();

    zkc::semantics::SealEngine engine(*environment);
    bool anyFailed = false;
    for (zkc::pir::ProtocolOp protocol : protocols)
      if (failed(engine.seal(protocol)))
        anyFailed = true;
    if (anyFailed)
      return signalPassFailure();

    SmallVector<zkc::pir::SealedOp> minted(
        getOperation().getOps<zkc::pir::SealedOp>());
    if (minted.size() != protocols.size() ||
        !getOperation().getOps<zkc::pir::ProtocolOp>().empty()) {
      getOperation().emitError()
          << "[zkc-E202] pir-seal did not replace every open protocol with "
             "exactly one newly minted sealed root";
      signalPassFailure();
    }
  }
};

class PirRecheckPass : public zkc::pir::impl::PirRecheckBase<PirRecheckPass> {
public:
  using PirRecheckBase::PirRecheckBase;

  void runOnOperation() override {
    auto environment =
        loadEnvironment(getOperation(), "pir-recheck", protocolVocabulary,
                        constructionProfileRegistry);
    if (failed(environment))
      return signalPassFailure();

    SmallVector<zkc::pir::SealedOp> sealedOps(
        getOperation().getOps<zkc::pir::SealedOp>());
    if (sealedOps.empty()) {
      getOperation().emitError()
          << "pir-recheck found no sealed artifact to re-judge";
      return signalPassFailure();
    }

    zkc::semantics::SealEngine engine(*environment);
    for (zkc::pir::SealedOp sealed : sealedOps)
      if (failed(engine.recheck(sealed)))
        signalPassFailure();
  }
};

} // namespace
