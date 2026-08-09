//===- TestSoundnessSite.cpp - sealed soundness site tests -----*- C++ -*-===//

#include "SoundnessAdapterTestUtils.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Soundness/PirSoundnessAdapter.h"
#include "zkc/Soundness/SealedSoundnessView.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include <string>
#include <utility>
#include <vector>

using namespace mlir;

namespace {

template <typename T>
LogicalResult expectRefusal(ModuleOp module, llvm::Expected<T> result,
                            llvm::StringRef expected, llvm::StringRef label) {
  if (result) {
    module.emitError() << label << " unexpectedly resolved";
    return failure();
  }
  std::string detail = llvm::toString(result.takeError());
  if (!llvm::StringRef(detail).contains(expected)) {
    module.emitError() << label << " produced the wrong refusal: " << detail;
    return failure();
  }
  llvm::outs() << label << ": refused\n";
  return success();
}

struct TestSoundnessSitePass
    : public PassWrapper<TestSoundnessSitePass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestSoundnessSitePass)

  TestSoundnessSitePass() = default;
  TestSoundnessSitePass(const TestSoundnessSitePass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override { return "test-soundness-site"; }
  StringRef getDescription() const override {
    return "test canonical sealed-subject construction and site resolution";
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

    auto sealedOps = module.getOps<zkc::pir::SealedOp>();
    if (!llvm::hasSingleElement(sealedOps))
      return fail("soundness-site test expects one sealed artifact");
    zkc::pir::SealedOp sealed = *sealedOps.begin();

    auto artifact = zkc::test::admitSoundnessFixture(
        sealed, protocolVocabularyPath, constructionProfileRegistryPath);
    if (!artifact)
      return fail(llvm::toString(artifact.takeError()));
    auto view = zkc::soundness::buildSealedSoundnessView(*artifact);
    if (!view)
      return fail(llvm::toString(view.takeError()));
    if (view->artifactId != sealed.getId())
      return fail("owned view changed the authenticated artifact id");
    if (view->claimsByIndex.size() != 2 ||
        view->reductionsByTransformerPosition.size() != 1)
      return fail("fixture did not produce the expected canonical site shape");

    const auto &[transformerPosition, reduction] =
        *view->reductionsByTransformerPosition.begin();
    if (reduction.transformerPosition != transformerPosition ||
        reduction.orderedInputs.size() != 1 ||
        reduction.orderedOutputs.size() != 1)
      return fail("owned reduction did not preserve its canonical shape");

    const zkc::soundness::ClaimRef &owner = reduction.orderedOutputs.front();
    const zkc::soundness::ClaimRef &source = reduction.orderedInputs.front();
    if (owner.claimIndex == source.claimIndex)
      return fail("input and output occurrences lost their canonical identity");

    zkc::soundness::ReductionOccurrence reductionSite{view->artifactId, owner,
                                                      transformerPosition, 0};
    auto output = zkc::soundness::resolveReductionOutput(*view, reductionSite);
    if (!output || *output != owner)
      return fail(output ? "canonical output resolved to the wrong claim"
                         : llvm::toString(output.takeError()));

    auto subject = zkc::soundness::subjectOf(
        *view, zkc::soundness::ApplicationSite{reductionSite});
    if (!subject || *subject != zkc::soundness::ProtocolClaimSubject{
                                    view->artifactId, owner})
      return fail(subject ? "reduction subject resolved incorrectly"
                          : llvm::toString(subject.takeError()));

    auto input = zkc::soundness::resolveReductionInput(*view, reductionSite, 0);
    if (!input || *input != zkc::soundness::ProtocolClaimSubject{
                                view->artifactId, source})
      return fail(input ? "reduction input resolved incorrectly"
                        : llvm::toString(input.takeError()));

    auto allInputs =
        zkc::soundness::resolveAllReductionInputs(*view, reductionSite);
    if (!allInputs || *allInputs != zkc::soundness::ConsumedClaimVectorSubject{
                                        view->artifactId, owner, {source}})
      return fail(allInputs ? "ordered input vector resolved incorrectly"
                            : llvm::toString(allInputs.takeError()));
    auto selectedInputs = zkc::soundness::resolveReductionInputs(
        *view, reductionSite, std::vector<uint64_t>{0});
    if (!selectedInputs || *selectedInputs != *allInputs)
      return fail(selectedInputs
                      ? "explicit input selection changed canonical order"
                      : llvm::toString(selectedInputs.takeError()));

    llvm::outs() << "soundness sealed view: PASS\n";
    llvm::outs() << "view: 2 claims, 1 reduction\n";
    llvm::outs()
        << "reduction site: output, subject, and ordered input exact\n";

    zkc::soundness::ReductionOccurrence wrongArtifact = reductionSite;
    wrongArtifact.artifactId += "-other";
    if (failed(expectRefusal(
            module,
            zkc::soundness::resolveReductionOutput(*view, wrongArtifact),
            "application site names a different artifact",
            "artifact mismatch")))
      return signalPassFailure();

    zkc::soundness::ReductionOccurrence wrongOwner = reductionSite;
    wrongOwner.ownerClaim = source;
    if (failed(expectRefusal(
            module, zkc::soundness::resolveReductionOutput(*view, wrongOwner),
            "owner claim does not equal the canonically resolved output",
            "owner mismatch")))
      return signalPassFailure();

    zkc::soundness::PathOccurrence path{view->artifactId, owner};
    auto pathSubject =
        zkc::soundness::subjectOf(*view, zkc::soundness::ApplicationSite{path});
    if (!pathSubject || *pathSubject != *subject)
      return fail(pathSubject ? "path subject resolved incorrectly"
                              : llvm::toString(pathSubject.takeError()));
    llvm::outs() << "path site: exact claim subject\n";

    zkc::soundness::PathOccurrence wrongPathClaim = path;
    wrongPathClaim.claim.descriptorDigest += "0";
    if (failed(expectRefusal(
            module,
            zkc::soundness::subjectOf(
                *view, zkc::soundness::ApplicationSite{wrongPathClaim}),
            "claim descriptor does not match its canonical claim index",
            "path claim mismatch")))
      return signalPassFailure();
  }
};

} // namespace

namespace zkc::test {
void registerTestSoundnessSitePass() {
  PassRegistration<TestSoundnessSitePass>();
}
} // namespace zkc::test
