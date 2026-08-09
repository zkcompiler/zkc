//===- TestKzgBatchCore.cpp - exact KZG transform core tests ----*- C++ -*-===//

#include "Dialect/Pir/Transforms/ProtocolArtifacts.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Artifact/Artifact.h"
#include "zkc/Dialect/Pir/Transforms/KzgBatchOpen.h"
#include "zkc/Dialect/Pir/Transforms/Projection.h"
#include "zkc/Encoding/EncodingDomain.h"
#include "zkc/Registry/ConstructionProfileRegistry.h"
#include "zkc/Registry/ProtocolEnvironment.h"
#include "zkc/Registry/ProtocolVocabulary.h"
#include "zkc/Semantics/SealEngine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <string>
#include <vector>

using namespace mlir;

namespace {

constexpr llvm::StringLiteral kBatchSpace =
    "52435875175126190479447740508185965837690552500527637822603658699938581184"
    "513";

template <typename RegistryT>
llvm::Expected<RegistryT> loadRegistry(llvm::StringRef path) {
  return RegistryT::loadFromFile(path);
}

struct TestKzgBatchCorePass
    : public PassWrapper<TestKzgBatchCorePass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestKzgBatchCorePass)

  TestKzgBatchCorePass() = default;
  TestKzgBatchCorePass(const TestKzgBatchCorePass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override { return "test-kzg-batch-core"; }
  StringRef getDescription() const override {
    return "test exact one-application KZG PIR transform mechanics";
  }

  Option<std::string> protocolVocabularyPath{
      *this, "protocol-vocabulary", llvm::cl::desc("protocol vocabulary")};
  Option<std::string> constructionProfileRegistryPath{
      *this, "construction-profile-registry",
      llvm::cl::desc("construction-profile registry")};

  void runOnOperation() override {
    ModuleOp module = getOperation();
    auto fail = [&](const llvm::Twine &message) {
      module.emitError() << message;
      signalPassFailure();
    };

    auto vocabulary =
        loadRegistry<zkc::registry::ProtocolVocabulary>(protocolVocabularyPath);
    if (!vocabulary)
      return fail(llvm::toString(vocabulary.takeError()));
    auto profiles = loadRegistry<zkc::registry::ConstructionProfileRegistry>(
        constructionProfileRegistryPath);
    if (!profiles)
      return fail(llvm::toString(profiles.takeError()));
    zkc::registry::ProtocolEnvironment environment(std::move(*vocabulary),
                                                   std::move(*profiles));

    auto protocols = module.getOps<zkc::pir::ProtocolOp>();
    if (!llvm::hasSingleElement(protocols))
      return fail("fixture must contain exactly one open protocol");
    zkc::pir::ProtocolOp authored = *protocols.begin();
    authored->setDiscardableAttr(
        "pir.test_note",
        StringAttr::get(authored.getContext(), "preserve-through-seal"));

    auto sourceSealed = zkc::semantics::SealEngine(environment).seal(authored);
    if (failed(sourceSealed))
      return fail("source protocol failed the seal judgment");
    auto preserved = dyn_cast_or_null<StringAttr>(
        (*sourceSealed)->getDiscardableAttr("pir.test_note"));
    if (!preserved || preserved.getValue() != "preserve-through-seal")
      return fail("in-memory seal lost discardable source metadata");
    auto sourceSnapshot = zkc::artifact::snapshotArtifact(*sourceSealed);
    if (!sourceSnapshot)
      return fail(llvm::toString(sourceSnapshot.takeError()));
    auto sourceArtifact =
        zkc::artifact::admitArtifact(std::move(*sourceSnapshot), environment);
    if (!sourceArtifact)
      return fail(llvm::toString(sourceArtifact.takeError()));
    auto sourceReads = zkc::pir::deriveVerifierProofReads(*sourceArtifact);
    if (!sourceReads)
      return fail(llvm::toString(sourceReads.takeError()));
    if (sourceReads->size() != 2)
      return fail("unbatched KZG source must have exactly two proof reads");
    auto sourceProjection = zkc::pir::projectArtifact(
        *sourceArtifact, zkc::pir::EndpointKind::Verifier);
    if (!sourceProjection)
      return fail(llvm::toString(sourceProjection.takeError()));

    auto beforeStorage =
        zkc::pir::openAdmittedProtocolForTransform(*sourceArtifact);
    if (!beforeStorage)
      return fail(llvm::toString(beforeStorage.takeError()));
    auto beforeProtocols =
        beforeStorage->module().getOps<zkc::pir::ProtocolOp>();
    if (!llvm::hasSingleElement(beforeProtocols))
      return fail("reopened artifact must contain exactly one open protocol");
    zkc::pir::ProtocolOp before = *beforeProtocols.begin();
    auto applications =
        zkc::pir::discoverSamePointKzgBatchOpenApplications(before);
    if (!applications)
      return fail(llvm::toString(applications.takeError()));
    if (applications->size() != 1)
      return fail("fixture must discover exactly one KZG batch application");
    const zkc::pir::KzgBatchOpenApplication application = applications->front();
    if (application.membersAnchor != "sha256:"
                                     "96642ac9a6b160285952fc491ea0043a2cad98fe3"
                                     "2f8de0dd6b3893f5932aa93" ||
        application.pointAnchor !=
            "sha256:"
            "a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64")
      return fail("KZG application has the wrong exact derived anchors");
    if (application.orderedClaims.size() != 2 ||
        application.orderedClaims[0].claimIndex != 0 ||
        application.orderedClaims[1].claimIndex != 1)
      return fail("KZG application has the wrong canonical claim order");

    auto recognized = zkc::pir::recognizeSamePointKzgBatchOpenApplication(
        before, application.orderedClaims);
    if (!recognized || !(*recognized == application))
      return fail(recognized ? "recognition changed the canonical application"
                             : llvm::toString(recognized.takeError()));

    std::vector<zkc::pir::KzgBatchOpenClaimRef> reversed =
        application.orderedClaims;
    std::reverse(reversed.begin(), reversed.end());
    auto reordered =
        zkc::pir::recognizeSamePointKzgBatchOpenApplication(before, reversed);
    if (reordered)
      return fail("reordered consumed claims unexpectedly recognized");
    llvm::consumeError(reordered.takeError());

    OpBuilder builder(before);
    builder.setInsertionPointAfter(before);
    auto wrongSuite =
        cast<zkc::pir::ProtocolOp>(builder.clone(*before.getOperation()));
    for (auto check : wrongSuite.getBody().front().getOps<zkc::pir::CheckOp>())
      check.setParamsAttr(DictionaryAttr::get(
          wrongSuite.getContext(),
          {{StringAttr::get(wrongSuite.getContext(), "suite"),
            StringAttr::get(wrongSuite.getContext(), "not-bls12-381")}}));
    auto wrongSuiteApplications =
        zkc::pir::discoverSamePointKzgBatchOpenApplications(wrongSuite);
    if (!wrongSuiteApplications || !wrongSuiteApplications->empty())
      return fail(wrongSuiteApplications
                      ? "wrong-suite KZG checks entered the transform domain"
                      : llvm::toString(wrongSuiteApplications.takeError()));
    wrongSuite.erase();

    builder.setInsertionPointAfter(before);
    auto after =
        cast<zkc::pir::ProtocolOp>(builder.clone(*before.getOperation()));
    auto reduction = zkc::pir::realizeSamePointKzgBatchOpenApplication(
        after, application, kBatchSpace);
    if (!reduction)
      return fail(llvm::toString(reduction.takeError()));
    if (reduction->getClaims().size() != 2 ||
        reduction->getOuts().size() != 1 ||
        reduction->getContract() != "kzg_batch")
      return fail("realized KZG reduction has the wrong exact shape");

    auto replay = zkc::pir::checkSamePointKzgBatchOpenApplication(
        before, after, application, kBatchSpace);
    if (!replay || !*replay)
      return fail(replay ? "deterministic KZG replay rejected"
                         : llvm::toString(replay.takeError()));

    builder.setInsertionPointAfter(after);
    auto wrong =
        cast<zkc::pir::ProtocolOp>(builder.clone(*after.getOperation()));
    bool changed = false;
    for (auto challenge : wrong.getBody().front().getOps<zkc::pir::ChalOp>())
      if (challenge.getDomain().starts_with("batch_open.")) {
        challenge.setSpace("17");
        changed = true;
      }
    if (!changed)
      return fail("realized KZG protocol has no batch challenge");
    auto wrongReplay = zkc::pir::checkSamePointKzgBatchOpenApplication(
        before, wrong, application, kBatchSpace);
    if (!wrongReplay || *wrongReplay)
      return fail(wrongReplay ? "mutated KZG result passed replay"
                              : llvm::toString(wrongReplay.takeError()));
    wrong.erase();

    auto remaining = zkc::pir::discoverSamePointKzgBatchOpenApplications(after);
    if (!remaining)
      return fail(llvm::toString(remaining.takeError()));
    if (!remaining->empty())
      return fail("realized protocol still exposes the consumed KZG group");

    auto finalSealed = zkc::semantics::SealEngine(environment).seal(after);
    if (failed(finalSealed))
      return fail("transformed protocol failed the seal judgment");
    auto finalSnapshot = zkc::artifact::snapshotArtifact(*finalSealed);
    if (!finalSnapshot)
      return fail(llvm::toString(finalSnapshot.takeError()));
    auto finalArtifact =
        zkc::artifact::admitArtifact(std::move(*finalSnapshot), environment);
    if (!finalArtifact)
      return fail(llvm::toString(finalArtifact.takeError()));
    auto finalReads = zkc::pir::deriveVerifierProofReads(*finalArtifact);
    if (!finalReads)
      return fail(llvm::toString(finalReads.takeError()));
    if (finalReads->size() != 1)
      return fail("batched KZG result must have exactly one proof read");
    if (sourceReads->front().codecId != "bls_g1_be48" ||
        finalReads->front().codecId != "bls_g1_be48" ||
        sourceReads->front().codecDigest != finalReads->front().codecDigest)
      return fail("KZG proof reads did not preserve the exact codec");
    auto finalProjection = zkc::pir::projectArtifact(
        *finalArtifact, zkc::pir::EndpointKind::Verifier);
    if (!finalProjection)
      return fail(llvm::toString(finalProjection.takeError()));
    if (!zkc::encoding::isLowerHex64(sourceProjection->id()) ||
        !zkc::encoding::isLowerHex64(finalProjection->id()) ||
        sourceProjection->id() == finalProjection->id())
      return fail("source and final projections have invalid identities");

    llvm::outs() << "applications: 1\n"
                 << "canonical-claims: 0,1\n"
                 << "reordered: refused\n"
                 << "wrong-suite: declined\n"
                 << "replay: accepted\n"
                 << "mutated-replay: refused\n"
                 << "source-reads: " << sourceReads->size() << " "
                 << sourceReads->front().codecId << "\n"
                 << "final-reads: " << finalReads->size() << " "
                 << finalReads->front().codecId << "\n"
                 << "final-seal: accepted\n"
                 << "source-projection:\n";
    sourceProjection->print(llvm::outs());
    llvm::outs() << "\nfinal-projection:\n";
    finalProjection->print(llvm::outs());
    llvm::outs() << "\n";
  }
};

} // namespace

namespace zkc::test {

void registerTestKzgBatchCorePass() {
  PassRegistration<TestKzgBatchCorePass>();
}

} // namespace zkc::test
