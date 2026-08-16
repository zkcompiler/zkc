//===- PirBatchOpen.cpp - exact same-point KZG batching --------*- C++ -*-===//
//
// The reusable core discovers, recognizes, realizes, and replay-checks one
// exact same-point KZG application.  The pass is only a convenience wrapper
// that applies every discovered maximal group.  The reduce it produces cites
// only its reduction contract; theorem selection is a separate derivation and
// never appears here.
//
//===----------------------------------------------------------------------===//

#include "zkc/Dialect/Pir/Transforms/KzgBatchOpen.h"
#include "zkc/Dialect/Pir/Transforms/Passes.h"

#include "mlir/IR/Builders.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/OwningOpRef.h"
#include "mlir/IR/Verifier.h"
#include "zkc/ChallengeShape.h"
#include "zkc/Dialect/Pir/Transforms/SpineEditor.h"
#include "zkc/Encoding/CanonicalEncoder.h"
#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Encoding/EncodingDomain.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/MapVector.h"

#include <map>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace zkc {
namespace pir {

#define GEN_PASS_DEF_PIRBATCHOPEN
#include "zkc/Dialect/Pir/Transforms/Passes.h.inc"

} // namespace pir
} // namespace zkc

using namespace mlir;

namespace {

/// One exact batchable source occurrence and the verifier material from which
/// its complete KZG opening descriptor is reconstructed.
struct BatchMember {
  zkc::pir::InstantiateOp source;
  zkc::pir::DischargeOp discharge;
  zkc::pir::CheckOp check;
  Value commitment;
  Value point;
  Value value;
  zkc::pir::SlotOp proof;
  std::string commitmentAnchor;
  std::string pointAnchor;
  std::string valueAnchor;
  std::string descriptorBytes;
  zkc::pir::KzgBatchOpenClaimRef claimRef;
};

struct BatchGroup {
  zkc::pir::KzgBatchOpenApplication application;
  SmallVector<BatchMember> members;
};

/// The claim descriptor preimage, `canonical([profile, anchors])` — parsed
/// back below, so it stays JSON.
static llvm::Expected<std::string>
claimDescriptorBytes(zkc::pir::InstantiateOp source) {
  auto descriptor = zkc::encoding::canonicalClaimDescriptor(
      cast<zkc::pir::ClaimType>(source.getClaim().getType()).getProfile(),
      source.getAnchors());
  if (!descriptor)
    return descriptor.takeError();
  return zkc::encoding::canonicalJsonBytes(*descriptor);
}

/// The order source claims are numbered in, asked of the component that owns
/// it. This file used to answer it by sorting on the descriptor bytes above,
/// which is a *different* order from the encoder's: the separator after the
/// profile is `"` there and NUL in the encoder, so two profiles where one is a
/// prefix of the other and the next byte sorts between them come out reversed.
/// The two numberings are compared for equality downstream, so there is only
/// one right answer and it is not this file's to give.
static llvm::Expected<std::string>
claimOrderKey(zkc::pir::InstantiateOp source) {
  auto anchors = zkc::encoding::attributeToCanonicalJson(source.getAnchors());
  if (!anchors)
    return anchors.takeError();
  return zkc::encoding::canonicalSourceClaimKey(
      cast<zkc::pir::ClaimType>(source.getClaim().getType()).getProfile(),
      *anchors);
}

/// Source claims occupy the first canonical claim positions, in the encoder's
/// own order (see claimOrderKey).  Computing this
/// source-only prefix does not require the resolved vocabulary that seal has
/// not stamped yet, and remains stable when reductions are inserted later.
static llvm::Expected<llvm::DenseMap<Value, zkc::pir::KzgBatchOpenClaimRef>>
canonicalSourceClaimRefs(zkc::pir::ProtocolOp protocol) {
  struct SourceRow {
    Value claim;
    std::string orderKey;
    std::string descriptorBytes;
  };
  SmallVector<SourceRow> rows;
  for (auto source :
       protocol.getBody().front().getOps<zkc::pir::InstantiateOp>()) {
    auto key = claimOrderKey(source);
    if (!key)
      return key.takeError();
    auto bytes = claimDescriptorBytes(source);
    if (!bytes)
      return bytes.takeError();
    rows.push_back({source.getClaim(), std::move(*key), std::move(*bytes)});
  }
  llvm::stable_sort(rows, [](const SourceRow &left, const SourceRow &right) {
    return left.orderKey < right.orderKey;
  });

  llvm::DenseMap<Value, zkc::pir::KzgBatchOpenClaimRef> result;
  for (auto [index, row] : llvm::enumerate(rows)) {
    auto descriptor = zkc::encoding::parseJsonUniqueKeys(row.descriptorBytes);
    if (!descriptor)
      return descriptor.takeError();
    auto digest =
        zkc::encoding::taggedSha256Ref("zkc/claim\n", std::move(*descriptor));
    if (!digest)
      return digest.takeError();
    result.try_emplace(
        row.claim, zkc::pir::KzgBatchOpenClaimRef{static_cast<uint64_t>(index),
                                                  std::move(*digest)});
  }
  return result;
}

/// Evaluate the exact MaterialExpr constructor admitted by the `kzg_batch`
/// contract.  Members are already in canonical complete-descriptor order.
static llvm::Expected<std::string>
batchDescriptorDigest(ArrayRef<BatchMember> sortedMembers) {
  llvm::json::Array descriptors;
  for (const BatchMember &member : sortedMembers) {
    auto descriptor =
        zkc::encoding::parseJsonUniqueKeys(member.descriptorBytes);
    if (!descriptor)
      return descriptor.takeError();
    descriptors.push_back(std::move(*descriptor));
  }
  llvm::json::Array typed;
  typed.push_back("claims");
  typed.push_back(std::move(descriptors));
  llvm::json::Array arguments;
  arguments.push_back(std::move(typed));
  llvm::json::Array preimage;
  preimage.push_back("construct");
  preimage.push_back("zkc.opening-batch.members");
  preimage.push_back(std::move(arguments));
  return zkc::encoding::taggedSha256Ref("zkc/material-expr\n",
                                        llvm::json::Value(std::move(preimage)));
}

static std::optional<std::string> stringAnchor(zkc::pir::InstantiateOp source,
                                               llvm::StringRef name) {
  auto entry = source.getAnchors().getNamed(name);
  auto value = entry ? dyn_cast<StringAttr>(entry->getValue()) : StringAttr();
  if (!value || !zkc::encoding::isSha256Ref(value.getValue()))
    return std::nullopt;
  return value.getValue().str();
}

static bool hasExactMaterialBinding(Block &body, Value value,
                                    llvm::StringRef semanticRef) {
  unsigned matches = 0;
  for (auto binding : body.getOps<zkc::pir::MaterialBindOp>())
    if (binding.getValue() == value) {
      if (binding.getSemanticRef() != semanticRef)
        return false;
      ++matches;
    }
  return matches == 1;
}

static bool hasValueClass(Value value, llvm::StringRef expected) {
  auto type = dyn_cast<zkc::pir::ValType>(value.getType());
  return type && type.getValueClass() == expected;
}

/// A shape outside the exact convention is declined.  Malformed canonical
/// descriptor data is an error because silently dropping it would turn a
/// malformed candidate into a different transform domain.
static llvm::Expected<std::optional<BatchMember>>
candidate(zkc::pir::InstantiateOp source,
          const llvm::DenseMap<Value, zkc::pir::KzgBatchOpenClaimRef>
              &canonicalSourceClaims) {
  auto profile =
      cast<zkc::pir::ClaimType>(source.getClaim().getType()).getProfile();
  if (profile != "single_opening" || !source.getClaim().hasOneUse() ||
      source.getAnchors().size() != 3)
    return std::optional<BatchMember>();

  auto discharge =
      dyn_cast<zkc::pir::DischargeOp>(*source.getClaim().getUsers().begin());
  if (!discharge || discharge.getRule() != "zkc.terminal.kzg-opening" ||
      discharge.getChecks().size() != 1)
    return std::optional<BatchMember>();
  auto selected = discharge.getChecks().getNamed("opening");
  auto selectedLabel =
      selected ? dyn_cast<StringAttr>(selected->getValue()) : StringAttr();
  if (!selectedLabel)
    return std::optional<BatchMember>();

  zkc::pir::CheckOp check;
  for (auto candidateCheck : source->getBlock()->getOps<zkc::pir::CheckOp>())
    if (candidateCheck.getLabel() == selectedLabel.getValue()) {
      if (check)
        return std::optional<BatchMember>();
      check = candidateCheck;
    }
  if (!check || check.getContract() != "zkc.check.kzg-opening" ||
      check.getInputs().size() != 4 || check.getExpr())
    return std::optional<BatchMember>();
  if (!check.getParams() || check.getParams()->size() != 1 ||
      (check.getSemanticArgs() && !check.getSemanticArgs()->empty()))
    return std::optional<BatchMember>();
  auto suite = check.getParams()->getNamed("suite");
  auto suiteName =
      suite ? dyn_cast<StringAttr>(suite->getValue()) : StringAttr();
  if (!suiteName || suiteName.getValue() != "bls12-381")
    return std::optional<BatchMember>();

  Value commitment = check.getInputs()[0];
  Value point = check.getInputs()[1];
  Value value = check.getInputs()[2];
  if (!hasValueClass(commitment, "g1") || !hasValueClass(point, "fr") ||
      !hasValueClass(value, "fr") || !hasValueClass(check.getInputs()[3], "g1"))
    return std::optional<BatchMember>();
  auto proof = check.getInputs()[3].getDefiningOp<zkc::pir::SlotOp>();
  if (!proof || proof.getPayloadClass() != "g1" || !proof.getVal().hasOneUse())
    return std::optional<BatchMember>();

  auto commitmentAnchor = stringAnchor(source, "commitment");
  auto pointAnchor = stringAnchor(source, "point");
  auto valueAnchor = stringAnchor(source, "value");
  if (!commitmentAnchor || !pointAnchor || !valueAnchor)
    return std::optional<BatchMember>();
  Block &body = *source->getBlock();
  if (!hasExactMaterialBinding(body, commitment, *commitmentAnchor) ||
      !hasExactMaterialBinding(body, point, *pointAnchor) ||
      !hasExactMaterialBinding(body, value, *valueAnchor))
    return std::optional<BatchMember>();

  auto claimRef = canonicalSourceClaims.find(source.getClaim());
  if (claimRef == canonicalSourceClaims.end() ||
      !zkc::encoding::isSha256Ref(claimRef->second.descriptorDigest))
    return llvm::createStringError(
        "same-point KZG candidate has no canonical claim reference");
  auto descriptor = claimDescriptorBytes(source);
  if (!descriptor)
    return descriptor.takeError();

  BatchMember member;
  member.source = source;
  member.discharge = discharge;
  member.check = check;
  member.commitment = commitment;
  member.point = point;
  member.value = value;
  member.proof = proof;
  member.commitmentAnchor = std::move(*commitmentAnchor);
  member.pointAnchor = std::move(*pointAnchor);
  member.valueAnchor = std::move(*valueAnchor);
  member.descriptorBytes = std::move(*descriptor);
  member.claimRef = claimRef->second;
  return std::optional<BatchMember>(std::move(member));
}

static llvm::Expected<std::vector<BatchGroup>>
discoverGroups(zkc::pir::ProtocolOp protocol) {
  if (!protocol)
    return llvm::createStringError(
        "same-point KZG discovery expected one pir.protocol");
  if (failed(verify(protocol.getOperation())))
    return llvm::createStringError(
        "same-point KZG discovery requires structurally valid open PIR");
  auto canonicalSourceClaims = canonicalSourceClaimRefs(protocol);
  if (!canonicalSourceClaims)
    return canonicalSourceClaims.takeError();

  std::map<std::string, SmallVector<BatchMember>, std::less<>> byPoint;
  for (auto source :
       protocol.getBody().front().getOps<zkc::pir::InstantiateOp>()) {
    auto found = candidate(source, *canonicalSourceClaims);
    if (!found)
      return found.takeError();
    if (*found)
      byPoint[(*found)->pointAnchor].push_back(std::move(**found));
  }

  std::vector<BatchGroup> result;
  for (auto &[point, members] : byPoint) {
    if (members.size() < 2)
      continue;
    llvm::sort(members, [](const BatchMember &left, const BatchMember &right) {
      return left.descriptorBytes < right.descriptorBytes;
    });
    for (size_t i = 1; i < members.size(); ++i)
      if (members[i - 1].descriptorBytes == members[i].descriptorBytes)
        return llvm::createStringError(
            "same-point KZG group has duplicate complete claim descriptors");

    // The anchor group must also be one exact verifier-side point value.  A
    // shared anchor with multiple local values is ambiguous and therefore not
    // a smaller batch opportunity.
    for (BatchMember &member : members)
      if (member.point != members.front().point ||
          member.proof.getPayloadClass() !=
              members.front().proof.getPayloadClass() ||
          member.check.getParams() != members.front().check.getParams())
        return llvm::createStringError(
            "same-point KZG anchor group has incompatible verifier material");

    auto membersAnchor = batchDescriptorDigest(members);
    if (!membersAnchor)
      return membersAnchor.takeError();
    BatchGroup group;
    group.application.pointAnchor = point;
    group.application.membersAnchor = std::move(*membersAnchor);
    for (const BatchMember &member : members)
      group.application.orderedClaims.push_back(member.claimRef);
    group.members = std::move(members);
    result.push_back(std::move(group));
  }
  return result;
}

static bool memberLabelExists(zkc::pir::ProtocolOp protocol,
                              llvm::StringRef label) {
  for (Operation &operation : protocol.getBody().front())
    if (auto member = dyn_cast<zkc::pir::ProtocolMemberOpInterface>(operation))
      if (member.getMemberLabel() == label)
        return true;
  return false;
}

static llvm::Expected<zkc::pir::ReduceOp>
realizeGroup(zkc::pir::ProtocolOp protocol, BatchGroup &group,
             llvm::StringRef batchSpace) {
  if (!zkc::challenge::isCanonicalPositiveDecimal(batchSpace))
    return llvm::createStringError(
        "batch challenge space must be a canonical positive decimal");

  SmallVector<BatchMember> &members = group.members;
  std::string tag =
      zkc::pir::SpineEditor::contentTag(group.application.membersAnchor, 16);
  std::string prefix = "batch." + tag.substr(0, 8);
  std::string gammaLabel = prefix + ".gamma";
  std::string proofLabel = prefix + ".W";
  std::string checkLabel = prefix + ".open";
  std::string challengeDomain = "batch_open." + tag;

  if (memberLabelExists(protocol, prefix) ||
      memberLabelExists(protocol, gammaLabel) ||
      memberLabelExists(protocol, proofLabel) ||
      memberLabelExists(protocol, checkLabel))
    return llvm::createStringError(
        "content-derived KZG batch label collides with the source protocol");
  for (auto challenge : protocol.getBody().front().getOps<zkc::pir::ChalOp>())
    if (challenge.getDomain() == challengeDomain)
      return llvm::createStringError(
          "content-derived KZG batch domain collides with the source "
          "protocol");

  zkc::pir::EndOp end;
  for (auto candidateEnd :
       protocol.getBody().front().getOps<zkc::pir::EndOp>()) {
    if (end)
      return llvm::createStringError(
          "same-point KZG realization found multiple pir.end operations");
    end = candidateEnd;
  }
  if (!end)
    return llvm::createStringError(
        "same-point KZG realization found no pir.end operation");

  // Every fallible derived value above is complete before this first
  // mutation.  The remaining steps are typed construction and erasure of the
  // exact recognized handles.
  MLIRContext *ctx = protocol.getContext();
  Location loc = protocol.getLoc();
  OpBuilder builder(end);
  SmallVector<Value> deps;
  for (BatchMember &member : members)
    deps.push_back(member.commitment);
  deps.push_back(members.front().point);
  for (BatchMember &member : members)
    deps.push_back(member.value);
  auto gamma =
      zkc::pir::ChalOp::create(builder, loc, end.getThreadIn(), deps,
                               gammaLabel, "fr", challengeDomain, batchSpace);
  auto proof = zkc::pir::SlotOp::create(
      builder, loc, gamma.getOut(), proofLabel,
      members.front().proof.getPayloadClass(), /*count=*/"1",
      /*unabsorbed=*/false,
      /*instance=*/std::nullopt, /*role=*/std::nullopt, /*idx=*/0,
      /*binding=*/StringAttr());
  SmallVector<Value> checkInputs(deps);
  checkInputs.push_back(gamma.getVal());
  checkInputs.push_back(proof.getVal());
  zkc::pir::CheckOp::create(builder, loc, checkInputs, checkLabel,
                            "zkc.check.kzg-batch-opening",
                            *members.front().check.getParams(),
                            /*semantic_args=*/nullptr, /*expr=*/nullptr);
  end->setOperand(0, proof.getOut());

  builder.setInsertionPointAfter(end);
  SmallVector<Value> consumed;
  for (BatchMember &member : members)
    consumed.push_back(member.source.getClaim());
  auto outAnchors = ArrayAttr::get(
      ctx, {DictionaryAttr::get(
               ctx, {{StringAttr::get(ctx, "members"),
                      StringAttr::get(ctx, group.application.membersAnchor)},
                     {StringAttr::get(ctx, "point"),
                      StringAttr::get(ctx, group.application.pointAnchor)}})});
  auto reduce = zkc::pir::ReduceOp::create(
      builder, loc, TypeRange{zkc::pir::ClaimType::get(ctx, "batch_opening")},
      consumed, ValueRange{gamma.getVal()}, prefix, "kzg_batch",
      /*checks=*/
      DictionaryAttr::get(ctx, {{StringAttr::get(ctx, "opening"),
                                 StringAttr::get(ctx, checkLabel)}}),
      /*params=*/nullptr, /*out_anchors=*/outAnchors);

  builder.setInsertionPoint(members.front().discharge);
  auto checks = DictionaryAttr::get(ctx, {{StringAttr::get(ctx, "opening"),
                                           StringAttr::get(ctx, checkLabel)}});
  zkc::pir::DischargeOp::create(builder, loc, reduce.getOuts().front(),
                                "zkc.terminal.kzg-batch-opening", checks);
  zkc::pir::SpineEditor editor(protocol);
  for (BatchMember &member : members) {
    member.discharge->erase();
    member.check->erase();
    editor.eraseEvent(member.proof);
  }

  if (failed(verify(protocol.getOperation())))
    return llvm::createStringError(
        "same-point KZG realization produced structurally invalid PIR");
  return reduce;
}

class PirBatchOpenPass
    : public zkc::pir::impl::PirBatchOpenBase<PirBatchOpenPass> {
public:
  using PirBatchOpenBase::PirBatchOpenBase;

  void runOnOperation() override {
    if (!zkc::challenge::isCanonicalPositiveDecimal(batchSpace)) {
      getOperation().emitError()
          << "pir-batch-open: the batch-challenge space is required "
             "(batch-space=<exact cardinality, minimal decimal>)";
      return signalPassFailure();
    }
    for (auto protocol : getOperation().getOps<zkc::pir::ProtocolOp>()) {
      auto groups = discoverGroups(protocol);
      if (!groups) {
        protocol.emitError()
            << "pir-batch-open: " << llvm::toString(groups.takeError());
        return signalPassFailure();
      }
      llvm::json::Array manifest;
      for (BatchGroup &group : *groups) {
        llvm::json::Array commitments;
        for (const BatchMember &member : group.members)
          commitments.push_back(member.commitmentAnchor);
        auto realized = realizeGroup(protocol, group, batchSpace);
        if (!realized) {
          protocol.emitError()
              << "pir-batch-open: " << llvm::toString(realized.takeError());
          return signalPassFailure();
        }
        manifest.push_back(
            llvm::json::Object{{"batched", std::move(commitments)},
                               {"point", group.application.pointAnchor},
                               {"members", group.application.membersAnchor},
                               {"space", batchSpace}});
      }
      if (!manifest.empty()) {
        // Pass provenance remains discardable and is ignored by the reusable
        // replay judgment.
        std::string bytes;
        llvm::raw_string_ostream stream(bytes);
        if (llvm::Error error = zkc::encoding::writeCanonicalJson(
                llvm::json::Object{{"pass", "pir-batch-open"},
                                   {"groups", std::move(manifest)}},
                stream)) {
          protocol.emitError()
              << "pir-batch-open: " << llvm::toString(std::move(error));
          return signalPassFailure();
        }
        protocol->setDiscardableAttr(
            "pir.pass_manifest", StringAttr::get(protocol.getContext(), bytes));
      }
    }
  }
};

} // namespace

bool zkc::pir::operator==(const KzgBatchOpenClaimRef &left,
                          const KzgBatchOpenClaimRef &right) {
  return left.claimIndex == right.claimIndex &&
         left.descriptorDigest == right.descriptorDigest;
}

bool zkc::pir::operator==(const KzgBatchOpenApplication &left,
                          const KzgBatchOpenApplication &right) {
  return left.pointAnchor == right.pointAnchor &&
         left.membersAnchor == right.membersAnchor &&
         left.orderedClaims == right.orderedClaims;
}

llvm::Expected<std::vector<zkc::pir::KzgBatchOpenApplication>>
zkc::pir::discoverSamePointKzgBatchOpenApplications(ProtocolOp protocol) {
  auto groups = discoverGroups(protocol);
  if (!groups)
    return groups.takeError();
  std::vector<KzgBatchOpenApplication> applications;
  applications.reserve(groups->size());
  for (BatchGroup &group : *groups)
    applications.push_back(std::move(group.application));
  return applications;
}

llvm::Expected<zkc::pir::KzgBatchOpenApplication>
zkc::pir::recognizeSamePointKzgBatchOpenApplication(
    ProtocolOp protocol, llvm::ArrayRef<KzgBatchOpenClaimRef> orderedClaims) {
  auto applications = discoverSamePointKzgBatchOpenApplications(protocol);
  if (!applications)
    return applications.takeError();
  const KzgBatchOpenApplication *match = nullptr;
  for (const KzgBatchOpenApplication &application : *applications)
    if (llvm::ArrayRef(application.orderedClaims) == orderedClaims) {
      if (match)
        return llvm::createStringError(
            "requested KZG claim vector recognizes more than one group");
      match = &application;
    }
  if (!match)
    return llvm::createStringError(
        "requested KZG claim vector is not one canonical eligible group");
  return *match;
}

llvm::Expected<zkc::pir::ReduceOp>
zkc::pir::realizeSamePointKzgBatchOpenApplication(
    ProtocolOp protocol, const KzgBatchOpenApplication &application,
    llvm::StringRef batchChallengeSpace) {
  auto groups = discoverGroups(protocol);
  if (!groups)
    return groups.takeError();
  BatchGroup *match = nullptr;
  for (BatchGroup &group : *groups)
    if (group.application == application) {
      if (match)
        return llvm::createStringError(
            "requested KZG application recognizes more than one group");
      match = &group;
    }
  if (!match)
    return llvm::createStringError(
        "requested KZG application is not exact for this source protocol");
  return realizeGroup(protocol, *match, batchChallengeSpace);
}

llvm::Expected<bool> zkc::pir::checkSamePointKzgBatchOpenApplication(
    ProtocolOp before, ProtocolOp after,
    const KzgBatchOpenApplication &application,
    llvm::StringRef batchChallengeSpace) {
  if (!before || !after)
    return llvm::createStringError(
        "KZG replay check requires before and after pir.protocol values");
  OwningOpRef<ProtocolOp> replay(cast<ProtocolOp>(before->clone()));
  auto realized = realizeSamePointKzgBatchOpenApplication(
      replay.get(), application, batchChallengeSpace);
  if (!realized)
    return realized.takeError();
  auto flags = static_cast<OperationEquivalence::Flags>(
      OperationEquivalence::IgnoreLocations |
      OperationEquivalence::IgnoreDiscardableAttrs);
  return OperationEquivalence::isEquivalentTo(replay.get().getOperation(),
                                              after.getOperation(), flags);
}
