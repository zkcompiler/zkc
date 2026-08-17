//===- TerminalClosure.cpp - static terminal attachment judgment -*- C++
//-*-===//
#include "zkc/Semantics/TerminalClosure.h"

#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Semantics/CheckLayout.h"
#include "zkc/Encoding/CanonicalEncoder.h"
#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Encoding/EncodingDomain.h"
#include "zkc/Registry/ProtocolVocabulary.h"
#include "zkc/Semantics/ClosureLedger.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringMap.h"

#include <algorithm>
#include <map>

using namespace mlir;
using namespace zkc::pir;
using namespace zkc::registry;

namespace {

struct ClaimView {
  std::string profile;
  DictionaryAttr anchors;
  ReduceOp producer;
  uint64_t output = 0;
  std::string descriptorBytes;
};

using zkc::semantics::OperandView;

struct CheckView {
  CheckOp op;
  OperandView operands;
  llvm::json::Value normalizedExpr = nullptr;
};

static std::vector<std::string> sortedNames(DictionaryAttr dictionary) {
  std::vector<std::string> result;
  if (dictionary)
    for (NamedAttribute named : dictionary)
      result.push_back(named.getName().str());
  llvm::sort(result);
  return result;
}

static std::vector<std::string> sortedCopy(ArrayRef<std::string> values) {
  std::vector<std::string> result(values.begin(), values.end());
  llvm::sort(result);
  return result;
}

class Matcher {
public:
  Matcher(Operation *container, const ProtocolVocabulary &vocabulary,
          zkc::semantics::ClosureLedger &ledger)
      : container(container), vocabulary(vocabulary), ledger(ledger),
        body(container->getRegion(0).front()) {}

  LogicalResult run() {
    indexCarrier();
    validateClaims();
    validateChecks();
    validateDischarges();
    if (!ok)
      return failure();
    return success();
  }

private:
  /// The identifier is written as the diagnostic carries it, here and
  /// in every other emitting file, so one search finds every site that
  /// raises a given refusal (docs/spec/versioning.md §3).
  InFlightDiagnostic error(Operation *operation, StringRef id) {
    ok = false;
    return operation->emitOpError() << id << " ";
  }

  void indexCarrier() {
    for (Operation &operation : body) {
      if (auto check = dyn_cast<CheckOp>(operation))
        checksByLabel[check.getLabel()] = check;
      else if (auto binding = dyn_cast<MaterialBindOp>(operation))
        bindingsByValue[binding.getValue()] = binding;
      else if (auto slot = dyn_cast<SlotOp>(operation)) {
        if (auto membership = slot.getMembership())
          messages[membership->instance][membership->role][membership->idx] =
              slot.getVal();
      }
    }
  }

  DictionaryAttr outputAnchors(ReduceOp reduce, uint64_t output) {
    auto all = reduce.getOutAnchors();
    if (!all || output >= all->size())
      return DictionaryAttr::get(container->getContext());
    return dyn_cast<DictionaryAttr>((*all)[output]);
  }

  void addClaim(Value value, DictionaryAttr anchors, ReduceOp producer = {},
                uint64_t output = 0) {
    auto type = cast<ClaimType>(value.getType());
    ClaimView view{type.getProfile().str(), anchors, producer, output, {}};
    const ClaimProfile *profile = vocabulary.lookupProfile(view.profile);
    if (!profile) {
      error(value.getDefiningOp(), "[zkc-E300]")
          << "claim profile '" << view.profile
          << "' is not admitted by the protocol vocabulary";
      return;
    }
    if (!anchors) {
      error(value.getDefiningOp(), "[zkc-E300]")
          << "claim profile '" << view.profile << "' has no anchor dictionary";
      return;
    }
    std::vector<std::string> actual = sortedNames(anchors);
    std::vector<std::string> expected = sortedCopy(profile->anchors);
    if (actual != expected) {
      error(value.getDefiningOp(), "[zkc-E300]")
          << "claim profile '" << view.profile
          << "' requires exactly its admitted anchor set";
      return;
    }
    auto descriptor =
        zkc::encoding::canonicalClaimDescriptor(view.profile, anchors);
    if (!descriptor) {
      error(value.getDefiningOp(), "[zkc-E300]")
          << "claim anchors have no canonical form: "
          << llvm::toString(descriptor.takeError());
      return;
    }
    auto bytes = zkc::encoding::canonicalJsonBytes(*descriptor);
    if (!bytes) {
      error(value.getDefiningOp(), "[zkc-E300]")
          << "claim descriptor has no canonical form: "
          << llvm::toString(bytes.takeError());
      return;
    }
    view.descriptorBytes = std::move(*bytes);
    claims[value] = std::move(view);
  }

  void validateClaims() {
    for (Operation &operation : body) {
      if (auto source = dyn_cast<InstantiateOp>(operation)) {
        addClaim(source.getClaim(), source.getAnchors());
      } else if (auto reduce = dyn_cast<ReduceOp>(operation)) {
        if (auto all = reduce.getOutAnchors();
            all && all->size() != reduce.getOuts().size()) {
          error(reduce, "[zkc-E300]")
              << "out_anchors must contain one dictionary per produced "
                 "claim";
          continue;
        }
        for (auto [index, output] : llvm::enumerate(reduce.getOuts()))
          addClaim(output, outputAnchors(reduce, index), reduce, index);
      }
    }
  }

  llvm::Expected<llvm::json::Value> normalizeExpr(Attribute attribute,
                                                  const OperandView &operands,
                                                  unsigned depth = 0) {
    if (depth > zkc::encoding::kMaxAttrDepth)
      return llvm::createStringError(
          "transparent expression exceeds the canonical depth bound");
    auto node = dyn_cast<ArrayAttr>(attribute);
    if (!node || node.empty())
      return llvm::createStringError(
          "transparent expression node must be a nonempty array");
    auto head = dyn_cast<StringAttr>(node[0]);
    if (!head)
      return llvm::createStringError(
          "transparent expression head must be a string");
    if (head.getValue() == "in") {
      if (node.size() != 2)
        return llvm::createStringError("input leaf must have one index");
      auto index = dyn_cast<IntegerAttr>(node[1]);
      if (!index || index.getInt() < 0 ||
          static_cast<uint64_t>(index.getInt()) >= operands.positions.size())
        return llvm::createStringError(
            "transparent expression input index is out of range");
      auto [role, occurrence] = operands.positions[index.getInt()];
      llvm::json::Array leaf;
      leaf.push_back("role");
      leaf.push_back(role);
      if (operands.roles.at(role).size() != 1)
        leaf.push_back(static_cast<int64_t>(occurrence));
      return llvm::json::Value(std::move(leaf));
    }
    llvm::json::Array normalized;
    normalized.push_back(head.getValue());
    for (Attribute child : llvm::drop_begin(node)) {
      if (auto subtree = dyn_cast<ArrayAttr>(child)) {
        auto value = normalizeExpr(subtree, operands, depth + 1);
        if (!value)
          return value.takeError();
        normalized.push_back(std::move(*value));
      } else {
        auto value = zkc::encoding::attributeToCanonicalJson(child, depth + 1);
        if (!value)
          return value.takeError();
        normalized.push_back(std::move(*value));
      }
    }
    return llvm::json::Value(std::move(normalized));
  }

  void validateChecks() {
    for (Operation &operation : body) {
      auto check = dyn_cast<CheckOp>(operation);
      if (!check)
        continue;
      const CheckContract *contract =
          vocabulary.lookupCheckContract(check.getContract());
      if (!contract) {
        error(check, "[zkc-E301]")
            << "check contract '" << check.getContract() << "' is not admitted";
        continue;
      }
      if (sortedNames(check.getParams().value_or(DictionaryAttr())) !=
          sortedCopy(contract->parameters)) {
        error(check, "[zkc-E301]")
            << "parameter names do not match check contract '"
            << check.getContract() << "'";
        continue;
      }
      if (sortedNames(check.getSemanticArgs().value_or(DictionaryAttr())) !=
          sortedCopy(contract->semanticParameters)) {
        error(check, "[zkc-E301]")
            << "semantic argument names do not match check contract '"
            << check.getContract() << "'";
        continue;
      }
      if (contract->isTransparent() != check.getExpr().has_value()) {
        error(check, "[zkc-E301]")
            << (contract->isTransparent()
                    ? "transparent check contract requires an expression"
                    : "opaque check contract forbids an expression");
        continue;
      }
      SmallVector<OperandView> layouts;
      zkc::semantics::solveCheckLayout(*contract, check.getInputs(), layouts);
      if (layouts.size() != 1) {
        error(check, "[zkc-E302]")
            << "operand sequence has " << layouts.size()
            << " valid layouts under check contract '" << check.getContract()
            << "' (exactly one is required)";
        continue;
      }
      CheckView view{check, std::move(layouts.front()), nullptr};
      if (check.getExpr()) {
        auto normalized = normalizeExpr(*check.getExpr(), view.operands);
        if (!normalized) {
          error(check, "[zkc-E303]") << "transparent expression is malformed: "
                                   << llvm::toString(normalized.takeError());
          continue;
        }
        view.normalizedExpr = std::move(*normalized);
      }
      checkViews[check.getOperation()] = std::move(view);
    }
  }

  ClaimView *claim(Value value) {
    auto found = claims.find(value);
    return found == claims.end() ? nullptr : &found->second;
  }

  StringRef anchor(ClaimView &view, StringRef name) {
    auto value = view.anchors.getAs<StringAttr>(name);
    return value ? value.getValue() : StringRef();
  }

  SmallVector<ClaimView *> orderedProducerInputs(ClaimView &view,
                                                 Operation *at) {
    SmallVector<ClaimView *> inputs;
    if (!view.producer) {
      error(at, "[zkc-E304]") << "terminal rule requires a reduction producer";
      return inputs;
    }
    for (Value value : view.producer.getClaims()) {
      ClaimView *input = claim(value);
      if (!input) {
        error(at, "[zkc-E304]")
            << "producer input has no admitted claim descriptor";
        return {};
      }
      inputs.push_back(input);
    }
    llvm::sort(inputs, [](const ClaimView *left, const ClaimView *right) {
      return left->descriptorBytes < right->descriptorBytes;
    });
    for (auto pair : llvm::zip(inputs, llvm::drop_begin(inputs)))
      if (std::get<0>(pair)->descriptorBytes ==
          std::get<1>(pair)->descriptorBytes) {
        error(at, "[zkc-E304]") << "producer input descriptors are not unique";
        return {};
      }
    return inputs;
  }

  Value producerDependency(ClaimView &view, StringRef role, Operation *at) {
    const ReductionContract *contract =
        view.producer
            ? vocabulary.lookupReductionContract(view.producer.getContract())
            : nullptr;
    if (!contract) {
      error(at, "[zkc-E304]")
          << "attachment requires an admitted reduction producer";
      return {};
    }
    for (auto [index, slot] : llvm::enumerate(contract->depSlots))
      if (slot.role == role) {
        if (index >= view.producer.getDeps().size())
          break;
        return view.producer.getDeps()[index];
      }
    error(at, "[zkc-E304]") << "producer has no dependency role '" << role << "'";
    return {};
  }

  Value producerMessage(ClaimView &view, StringRef role, uint64_t index,
                        Operation *at) {
    if (!view.producer) {
      error(at, "[zkc-E304]") << "attachment requires a reduction producer";
      return {};
    }
    auto instance = messages.find(view.producer.getLabel());
    if (instance != messages.end()) {
      auto roleIt = instance->second.find(role);
      if (roleIt != instance->second.end()) {
        auto value = roleIt->second.find(index);
        if (value != roleIt->second.end())
          return value->second;
      }
    }
    error(at, "[zkc-E304]") << "producer has no message role '" << role
                          << "' at index " << index;
    return {};
  }

  StringRef binding(Value value, Operation *at) {
    auto found = bindingsByValue.find(value);
    if (found == bindingsByValue.end()) {
      error(at, "[zkc-E305]") << "selected check operand has no material binding";
      return {};
    }
    ledger.usedMaterialBindings.insert(found->second.getOperation());
    return found->second.getSemanticRef();
  }

  SmallVector<Value> checkOperands(CheckView &check, StringRef role,
                                   Operation *at) {
    auto found = check.operands.roles.find(role);
    if (found == check.operands.roles.end()) {
      error(at, "[zkc-E306]")
          << "selected check has no operand role '" << role << "'";
      return {};
    }
    return found->second;
  }

  StringRef sourceAnchor(const AttachmentSource &source, ClaimView &view,
                         Operation *at) {
    if (source.kind == AttachmentSourceKind::ClaimAnchor)
      return anchor(view, source.anchor);
    if (source.kind == AttachmentSourceKind::ProducerInputAnchor) {
      if (!view.producer || source.index >= view.producer.getClaims().size()) {
        error(at, "[zkc-E306]") << "producer input anchor index is out of range";
        return {};
      }
      ClaimView *input = claim(view.producer.getClaims()[source.index]);
      return input ? anchor(*input, source.anchor) : StringRef();
    }
    error(at, "[zkc-E306]") << "attachment source is not a scalar claim anchor";
    return {};
  }

  SmallVector<StringRef> sourceAnchorVector(const AttachmentSource &source,
                                            ClaimView &view, Operation *at) {
    if (source.kind != AttachmentSourceKind::ProducerInputsAnchor) {
      error(at, "[zkc-E306]")
          << "attachment source is not a producer-input anchor vector";
      return {};
    }
    SmallVector<StringRef> result;
    for (ClaimView *input : orderedProducerInputs(view, at))
      result.push_back(anchor(*input, source.anchor));
    return result;
  }

  Value sourceValue(const AttachmentSource &source, ClaimView &view,
                    Operation *at) {
    if (source.kind == AttachmentSourceKind::ProducerDependency)
      return producerDependency(view, source.role, at);
    if (source.kind == AttachmentSourceKind::ProducerMessage)
      return producerMessage(view, source.role, source.index, at);
    error(at, "[zkc-E306]") << "attachment source is not an SSA value";
    return {};
  }

  StringRef semanticArgument(CheckOp check, StringRef role) {
    auto arguments = check.getSemanticArgs();
    auto value = arguments ? arguments->getAs<StringAttr>(role) : StringAttr();
    return value ? value.getValue() : StringRef();
  }

  void
  matchAttachment(const TerminalAttachment &attachment, ClaimView &claimView,
                  std::map<std::string, CheckView *, std::less<>> &selected,
                  Operation *at) {
    CheckView *check = nullptr;
    if (!attachment.checkRole.empty()) {
      auto found = selected.find(attachment.checkRole);
      if (found == selected.end()) {
        error(at, "[zkc-E306]") << "attachment names unknown terminal role '"
                              << attachment.checkRole << "'";
        return;
      }
      check = found->second;
    }

    switch (attachment.kind) {
    case TerminalAttachmentKind::SemanticParameter: {
      StringRef expected = sourceAnchor(attachment.source, claimView, at);
      if (!check || expected.empty() ||
          semanticArgument(check->op, attachment.targetRole) != expected)
        error(at, "[zkc-E306]")
            << "semantic parameter attachment does not match role '"
            << attachment.targetRole << "'";
      return;
    }
    case TerminalAttachmentKind::MaterialRefEquality: {
      StringRef expected = sourceAnchor(attachment.source, claimView, at);
      SmallVector<Value> operands =
          check ? checkOperands(*check, attachment.targetRole, at)
                : SmallVector<Value>();
      if (expected.empty() || operands.size() != 1 ||
          binding(operands.front(), at) != expected)
        error(at, "[zkc-E306]")
            << "material reference attachment does not match role '"
            << attachment.targetRole << "'";
      return;
    }
    case TerminalAttachmentKind::ValueIdentity: {
      Value expected = sourceValue(attachment.source, claimView, at);
      SmallVector<Value> operands =
          check ? checkOperands(*check, attachment.targetRole, at)
                : SmallVector<Value>();
      if (!expected || operands.size() != 1 || operands.front() != expected)
        error(at, "[zkc-E306]") << "SSA attachment does not match role '"
                              << attachment.targetRole << "'";
      return;
    }
    case TerminalAttachmentKind::MaterialRefVectorEquality: {
      SmallVector<StringRef> expected =
          sourceAnchorVector(attachment.source, claimView, at);
      SmallVector<Value> operands =
          check ? checkOperands(*check, attachment.targetRole, at)
                : SmallVector<Value>();
      bool matches = !expected.empty() && expected.size() == operands.size();
      for (size_t index = 0; matches && index < operands.size(); ++index)
        matches &= binding(operands[index], at) == expected[index];
      if (!matches)
        error(at, "[zkc-E306]")
            << "material reference vector does not match role '"
            << attachment.targetRole << "'";
      return;
    }
    case TerminalAttachmentKind::CommonMaterialRefEquality: {
      SmallVector<StringRef> references =
          sourceAnchorVector(attachment.source, claimView, at);
      StringRef common = references.empty() ? StringRef() : references.front();
      bool matches = !common.empty() &&
                     llvm::all_of(references,
                                  [&](StringRef reference) {
                                    return reference == common;
                                  }) &&
                     anchor(claimView, attachment.claimAnchor) == common;
      SmallVector<Value> operands =
          check ? checkOperands(*check, attachment.targetRole, at)
                : SmallVector<Value>();
      matches &= operands.size() == 1;
      if (operands.size() == 1)
        matches &= binding(operands.front(), at) == common;
      if (!matches)
        error(at, "[zkc-E306]")
            << "common material reference attachment does not match";
      return;
    }
    case TerminalAttachmentKind::DescriptorDigest: {
      if (attachment.source.kind !=
          AttachmentSourceKind::ProducerInputDescriptors) {
        error(at, "[zkc-E306]")
            << "descriptor digest requires producer_input_descriptors";
        return;
      }
      llvm::json::Array descriptors;
      for (ClaimView *input : orderedProducerInputs(claimView, at)) {
        auto parsed =
            zkc::encoding::parseJsonUniqueKeys(input->descriptorBytes);
        if (!parsed) {
          error(at, "[zkc-E306]") << "internal claim descriptor parse failed";
          return;
        }
        descriptors.push_back(std::move(*parsed));
      }
      auto digest = zkc::encoding::taggedSha256Ref(
          "zkc/claim-vector\n", llvm::json::Value(std::move(descriptors)));
      if (!digest || anchor(claimView, attachment.claimAnchor) != *digest) {
        if (!digest)
          llvm::consumeError(digest.takeError());
        error(at, "[zkc-E306]")
            << "producer descriptor-vector digest does not match claim "
               "anchor '"
            << attachment.claimAnchor << "'";
      }
      return;
    }
    }
  }

  bool sameJson(const llvm::json::Value &left, const llvm::json::Value &right) {
    auto leftBytes = zkc::encoding::canonicalJsonBytes(left);
    auto rightBytes = zkc::encoding::canonicalJsonBytes(right);
    if (!leftBytes || !rightBytes) {
      if (!leftBytes)
        llvm::consumeError(leftBytes.takeError());
      if (!rightBytes)
        llvm::consumeError(rightBytes.takeError());
      return false;
    }
    return *leftBytes == *rightBytes;
  }

  void validateDischarges() {
    llvm::SmallPtrSet<Operation *, 16> selectedGlobally;
    for (Operation &operation : body) {
      auto discharge = dyn_cast<DischargeOp>(operation);
      if (!discharge)
        continue;
      const TerminalRule *rule = vocabulary.lookupRule(discharge.getRule());
      if (!rule) {
        error(discharge, "[zkc-E307]")
            << "terminal rule '" << discharge.getRule() << "' is not admitted";
        continue;
      }
      ClaimView *claimView = claim(discharge.getClaim());
      if (!claimView || claimView->profile != rule->claimProfile) {
        error(discharge, "[zkc-E307]")
            << "terminal rule does not match the consumed claim profile";
        continue;
      }
      if (rule->producer) {
        if (!claimView->producer ||
            claimView->producer.getContract() != rule->producer->contract ||
            claimView->output != rule->producer->output) {
          error(discharge, "[zkc-E307]")
              << "terminal rule producer pin does not match the consumed "
                 "claim";
          continue;
        }
      }

      std::map<std::string, CheckView *, std::less<>> selected;
      std::vector<std::string> actualRoles = sortedNames(discharge.getChecks());
      std::vector<std::string> expectedRoles;
      for (const auto &[role, contract] : rule->checks)
        expectedRoles.push_back(role);
      if (actualRoles != expectedRoles) {
        error(discharge, "[zkc-E307]")
            << "discharge check roles do not exactly match terminal rule '"
            << discharge.getRule() << "'";
        continue;
      }
      bool selectionOk = true;
      for (const auto &[role, expectedContract] : rule->checks) {
        StringRef label =
            discharge.getChecks().getAs<StringAttr>(role).getValue();
        CheckOp check = checksByLabel.lookup(label);
        auto view =
            check ? checkViews.find(check.getOperation()) : checkViews.end();
        if (!check || view == checkViews.end() ||
            check.getContract() != expectedContract) {
          error(discharge, "[zkc-E307]")
              << "terminal role '" << role
              << "' does not select a conforming check of contract '"
              << expectedContract << "'";
          selectionOk = false;
          continue;
        }
        auto reductionOwner =
            ledger.reductionCheckOwners.find(check.getOperation());
        if (reductionOwner != ledger.reductionCheckOwners.end()) {
          bool exactPinnedOutput =
              rule->producer && claimView->producer &&
              claimView->producer.getOperation() == reductionOwner->second &&
              claimView->producer.getContract() == rule->producer->contract &&
              claimView->output == rule->producer->output;
          if (!exactPinnedOutput) {
            error(discharge, "[zkc-E307]")
                << "check '" << label
                << "' is owned by a reduction and may be reused only to "
                   "discharge that reduction's exact producer-pinned output";
            selectionOk = false;
            continue;
          }
        }
        if (!selectedGlobally.insert(check.getOperation()).second) {
          error(discharge, "[zkc-E307]")
              << "check '" << label
              << "' is selected by more than one discharge";
          selectionOk = false;
          continue;
        }
        selected[role] = &view->second;
      }
      if (!selectionOk)
        continue;

      for (const auto &[role, predicate] : rule->transparentPredicates) {
        auto selectedCheck = selected.find(role);
        if (selectedCheck == selected.end() ||
            !sameJson(selectedCheck->second->normalizedExpr, predicate)) {
          error(discharge, "[zkc-E308]")
              << "transparent predicate for terminal role '" << role
              << "' does not match the admitted rule";
          selectionOk = false;
        }
      }
      if (!selectionOk)
        continue;

      for (const TerminalAttachment &attachment : rule->attachments)
        matchAttachment(attachment, *claimView, selected, discharge);
    }
  }

  Operation *container;
  const ProtocolVocabulary &vocabulary;
  zkc::semantics::ClosureLedger &ledger;
  Block &body;
  bool ok = true;

  llvm::StringMap<CheckOp> checksByLabel;
  llvm::DenseMap<Value, MaterialBindOp> bindingsByValue;
  llvm::StringMap<llvm::StringMap<llvm::DenseMap<int64_t, Value>>> messages;
  llvm::DenseMap<Value, ClaimView> claims;
  llvm::DenseMap<Operation *, CheckView> checkViews;
};

} // namespace

LogicalResult
zkc::semantics::verifyTerminalClosure(Operation *container,
                                      const ProtocolVocabulary &vocabulary,
                                      ClosureLedger &ledger) {
  return Matcher(container, vocabulary, ledger).run();
}
