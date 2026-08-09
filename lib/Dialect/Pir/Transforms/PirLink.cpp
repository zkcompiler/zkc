//===- PirLink.cpp - pass adapter for static protocol linking ---*- C++ -*-===//

#include "zkc/Dialect/Pir/Transforms/Passes.h"

#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Registry/ProtocolEnvironment.h"
#include "zkc/Semantics/LinkEngine.h"

namespace zkc::pir {

#define GEN_PASS_DEF_PIRLINK
#include "zkc/Dialect/Pir/Transforms/Passes.h.inc"

} // namespace zkc::pir

using namespace llvm;
using namespace mlir;

namespace {

class PirLinkPass : public zkc::pir::impl::PirLinkBase<PirLinkPass> {
public:
  using PirLinkBase::PirLinkBase;

  void runOnOperation() override {
    zkc::pir::ProtocolOp producerOp, consumerOp;
    unsigned producerMatches = 0;
    unsigned consumerMatches = 0;
    for (auto protocol : getOperation().getOps<zkc::pir::ProtocolOp>()) {
      if (protocol.getProtocolName() == producer) {
        ++producerMatches;
        if (!producerOp)
          producerOp = protocol;
      }
      if (protocol.getProtocolName() == consumer) {
        ++consumerMatches;
        if (!consumerOp)
          consumerOp = protocol;
      }
    }
    if (producerMatches != 1 || consumerMatches != 1 ||
        producerOp == consumerOp) {
      getOperation().emitError()
          << "[zkc-E701] pir-link resolves exactly one distinct open protocol "
             "for each name; got producer '"
          << producer << "' (" << producerMatches << " matches), consumer '"
          << consumer << "' (" << consumerMatches << " matches)";
      return signalPassFailure();
    }

    if (protocolVocabulary.empty()) {
      getOperation().emitError()
          << "[zkc-E248] pir-link requires a protocol-vocabulary authority";
      return signalPassFailure();
    }
    auto environment = zkc::registry::ProtocolEnvironment::loadFromFiles(
        protocolVocabulary, constructionProfileRegistry);
    if (!environment) {
      getOperation().emitError()
          << "pir-link: " << toString(environment.takeError());
      return signalPassFailure();
    }

    zkc::semantics::LinkEngine engine(*environment);
    if (failed(engine.link(producerOp, consumerOp, producerPrefix,
                           consumerPrefix)))
      signalPassFailure();
  }
};

} // namespace
