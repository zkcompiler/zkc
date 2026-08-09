//===- TestArtifactLifecycle.cpp - artifact authority boundary -----------===//

#include "Artifact/ArtifactInternal.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Artifact/Artifact.h"
#include "zkc/Dialect/Pir/Transforms/Projection.h"
#include "zkc/Registry/ProtocolEnvironment.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include <string>
#include <type_traits>

using namespace mlir;

namespace {

namespace art = zkc::artifact;
namespace reg = zkc::registry;

static_assert(std::is_copy_constructible_v<art::DecodedPirArtifact>);
static_assert(std::is_copy_constructible_v<art::AdmittedPirArtifact>);
static_assert(std::is_copy_constructible_v<zkc::pir::ProjectedOirArtifact>);
static_assert(!std::is_default_constructible_v<art::DecodedPirArtifact>);
static_assert(!std::is_default_constructible_v<art::AdmittedPirArtifact>);
static_assert(!std::is_default_constructible_v<zkc::pir::ProjectedOirArtifact>);
static_assert(!std::is_move_assignable_v<art::detail::MutablePirArtifact>);
// The capability types declare copy operations only, which suppresses the
// implicit moves: an rvalue silently copies, so a still-callable moved-from
// capability object cannot exist. No type trait distinguishes that from a
// real move (the copy constructor binds rvalues), so the property is pinned
// here in prose next to the declarations that carry it.

struct TestArtifactLifecyclePass
    : public PassWrapper<TestArtifactLifecyclePass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestArtifactLifecyclePass)

  TestArtifactLifecyclePass() = default;
  TestArtifactLifecyclePass(const TestArtifactLifecyclePass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override { return "test-artifact-lifecycle"; }
  StringRef getDescription() const override {
    return "test decoded and registry-admitted PIR artifact capabilities";
  }

  Option<std::string> artifactPath{*this, "artifact",
                                   llvm::cl::desc("PIR artifact")};
  Option<std::string> protocolVocabularyPath{
      *this, "protocol-vocabulary", llvm::cl::desc("protocol vocabulary")};
  Option<std::string> baseConstructionProfilesPath{
      *this, "base-construction-profiles",
      llvm::cl::desc("construction profiles used when sealing")};
  Option<std::string> citedChangeConstructionProfilesPath{
      *this, "cited-change-construction-profiles",
      llvm::cl::desc("valid profiles with a changed cited entry")};
  Option<std::string> additiveConstructionProfilesPath{
      *this, "additive-construction-profiles",
      llvm::cl::desc("valid profiles with an uncited entry added")};

  void runOnOperation() override {
    ModuleOp module = getOperation();
    auto fail = [&](const llvm::Twine &message) {
      module.emitError() << message;
      signalPassFailure();
    };
    auto loadEnvironment = [&](llvm::StringRef constructionProfiles) {
      return reg::ProtocolEnvironment::loadFromFiles(protocolVocabularyPath,
                                                     constructionProfiles);
    };

    auto decoded = art::loadArtifact(artifactPath);
    if (!decoded) {
      fail("artifact decode failed: " +
           llvm::Twine(llvm::toString(decoded.takeError())));
      return;
    }
    llvm::outs() << "decode: accepted\n";

    auto baseEnvironment = loadEnvironment(baseConstructionProfilesPath);
    if (!baseEnvironment) {
      fail("base environment failed to load: " +
           llvm::Twine(llvm::toString(baseEnvironment.takeError())));
      return;
    }
    auto admitted = art::admitArtifact(*decoded, *baseEnvironment);
    if (!admitted) {
      fail("base admission failed: " +
           llvm::Twine(llvm::toString(admitted.takeError())));
      return;
    }
    llvm::outs() << "base admission: accepted\n";

    auto changedEnvironment =
        loadEnvironment(citedChangeConstructionProfilesPath);
    if (!changedEnvironment) {
      fail("changed environment failed to load: " +
           llvm::Twine(llvm::toString(changedEnvironment.takeError())));
      return;
    }
    const auto *baseProfiles = baseEnvironment->constructionProfiles();
    const auto *changedProfiles = changedEnvironment->constructionProfiles();
    const auto *baseToy =
        baseProfiles ? baseProfiles->lookup("toy_duplex") : nullptr;
    const auto *changedToy =
        changedProfiles ? changedProfiles->lookup("toy_duplex") : nullptr;
    if (!baseToy || !changedToy || baseToy->digest == changedToy->digest) {
      fail("cited-change fixture did not change sponge:toy_duplex");
      return;
    }
    auto changedAdmission = art::admitArtifact(*decoded, *changedEnvironment);
    if (changedAdmission) {
      fail("artifact admitted against changed cited authority");
      return;
    }
    std::string refusal = llvm::toString(changedAdmission.takeError());
    if (!llvm::StringRef(refusal).contains("artifact admission refused")) {
      fail("cited authority failed outside artifact admission: " +
           llvm::Twine(refusal));
      return;
    }
    llvm::outs() << "cited authority mismatch: refused\n";

    auto additiveEnvironment =
        loadEnvironment(additiveConstructionProfilesPath);
    if (!additiveEnvironment) {
      fail("additive environment failed to load: " +
           llvm::Twine(llvm::toString(additiveEnvironment.takeError())));
      return;
    }
    const auto *additiveProfiles = additiveEnvironment->constructionProfiles();
    const auto *additiveToy =
        additiveProfiles ? additiveProfiles->lookup("toy_duplex") : nullptr;
    if (!additiveProfiles || baseProfiles->lookup("zkc_test_unused") ||
        !additiveProfiles->lookup("zkc_test_unused") || !additiveToy ||
        additiveToy->digest != baseToy->digest) {
      fail("uncited-addition fixture changed the cited authority closure");
      return;
    }
    auto additiveAdmission = art::admitArtifact(*decoded, *additiveEnvironment);
    if (!additiveAdmission) {
      fail("uncited additive authority was refused: " +
           llvm::Twine(llvm::toString(additiveAdmission.takeError())));
      return;
    }
    if (additiveAdmission->id() != admitted->id()) {
      fail("admission changed the artifact identity");
      return;
    }
    llvm::outs() << "uncited additive authority: accepted\n";

    std::string original;
    llvm::raw_string_ostream originalStream(original);
    decoded->print(originalStream);
    originalStream.flush();

    art::AdmittedPirArtifact admittedCopy = *admitted;
    auto verifier = zkc::pir::projectArtifact(admittedCopy,
                                              zkc::pir::EndpointKind::Verifier);
    if (!verifier) {
      fail("verifier projection failed: " +
           llvm::Twine(llvm::toString(verifier.takeError())));
      return;
    }
    llvm::outs() << "verifier projection: accepted\n";
    auto prover = zkc::pir::projectArtifact(
        admittedCopy, zkc::pir::EndpointKind::ProverSkeleton);
    if (!prover) {
      fail("prover projection failed: " +
           llvm::Twine(llvm::toString(prover.takeError())));
      return;
    }
    llvm::outs() << "prover projection: accepted\n";

    std::string verifierText, proverText;
    llvm::raw_string_ostream verifierStream(verifierText);
    llvm::raw_string_ostream proverStream(proverText);
    verifier->print(verifierStream);
    prover->print(proverStream);
    verifierStream.flush();
    proverStream.flush();
    const std::string source =
        (llvm::Twine("source \"sha256:") + admittedCopy.id() + "\"").str();
    if (verifier->endpointKind() != zkc::pir::EndpointKind::Verifier ||
        prover->endpointKind() != zkc::pir::EndpointKind::ProverSkeleton ||
        verifier->id().size() != 64 || prover->id().size() != 64 ||
        !llvm::StringRef(verifierText).contains("endpoint \"verifier\"") ||
        !llvm::StringRef(proverText).contains("endpoint \"prover_skeleton\"") ||
        !llvm::StringRef(verifierText).contains(source) ||
        !llvm::StringRef(proverText).contains(source)) {
      fail("projected artifacts lost endpoint or admitted-source identity");
      return;
    }

    auto mutableClone =
        art::detail::ArtifactAccess::cloneForReopen(admittedCopy);
    auto snapshot = art::snapshotArtifact(mutableClone.sealed());
    if (!snapshot || snapshot->id() != admittedCopy.id()) {
      fail(snapshot ? "snapshot changed the artifact identity"
                    : "snapshot failed: " +
                          llvm::Twine(llvm::toString(snapshot.takeError())));
      return;
    }
    mutableClone.sealed().setPolicy("assumption_carrying");
    if (mutableClone.sealed().getPolicy() != "assumption_carrying") {
      fail("mutable clone did not accept an independent mutation");
      return;
    }

    auto freshClone = art::detail::ArtifactAccess::cloneForReopen(admittedCopy);
    std::string after;
    llvm::raw_string_ostream afterStream(after);
    decoded->print(afterStream);
    afterStream.flush();
    std::string snapshotted;
    llvm::raw_string_ostream snapshotStream(snapshotted);
    snapshot->print(snapshotStream);
    snapshotStream.flush();
    if (freshClone.sealed().getPolicy() != "closed_proof" ||
        after != original || snapshotted != original ||
        admittedCopy.id() != decoded->id()) {
      fail("mutable clone changed its admitted source capability");
      return;
    }
    llvm::outs() << "admitted projection isolation: accepted\n";
    llvm::outs() << "serialized snapshot isolation: accepted\n";
    llvm::outs() << "mutable clone isolation: accepted\n";
  }
};

} // namespace

namespace zkc::test {
void registerTestArtifactLifecyclePass() {
  PassRegistration<TestArtifactLifecyclePass>();
}
} // namespace zkc::test
