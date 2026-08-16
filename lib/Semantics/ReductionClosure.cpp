//===- ReductionClosure.cpp - exact local reduction judgment -------------===//
#include "zkc/Semantics/ReductionClosure.h"

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
#include <optional>
#include <string>
#include <utility>
#include <vector>

using namespace mlir;
using namespace zkc::pir;
using namespace zkc::registry;

namespace {

struct ClaimView {
  std::string profile;
  DictionaryAttr anchors;
  llvm::json::Value descriptor = nullptr;
  std::string descriptorBytes;
};

struct MessageView {
  Value value;
  Operation *operation = nullptr;
};

using zkc::semantics::OperandView;

struct CheckView {
  CheckOp op;
  OperandView operands;
  llvm::json::Value normalizedExpr = nullptr;
};

struct EvaluatedMaterial {
  MaterialExprSort sort = MaterialExprSort::Atom;
  llvm::json::Value value = nullptr;
};

static std::vector<std::string> sortedNames(DictionaryAttr dictionary) {
  std::vector<std::string> result;
  if (dictionary)
    for (NamedAttribute named : dictionary)
      result.push_back(named.getName().str());
  llvm::sort(result);
  return result;
}

template <typename Range>
static std::vector<std::string> sortedKeys(const Range &range) {
  std::vector<std::string> result;
  for (const auto &entry : range)
    result.push_back(std::string(entry.first));
  llvm::sort(result);
  return result;
}

static std::vector<std::string> sortedCopy(ArrayRef<std::string> values) {
  std::vector<std::string> result(values.begin(), values.end());
  llvm::sort(result);
  return result;
}

static StringRef materialSortName(MaterialExprSort sort) {
  switch (sort) {
  case MaterialExprSort::Ref:
    return "ref";
  case MaterialExprSort::Refs:
    return "refs";
  case MaterialExprSort::Claim:
    return "claim";
  case MaterialExprSort::Claims:
    return "claims";
  case MaterialExprSort::Atom:
    return "atom";
  }
  llvm_unreachable("closed material sort");
}

class Matcher {
public:
  Matcher(Operation *container, const ProtocolVocabulary &vocabulary,
          zkc::semantics::ClosureLedger &ledger)
      : container(container), vocabulary(vocabulary), ledger(ledger),
        body(container->getRegion(0).front()) {}

  LogicalResult run() {
    indexCarrier();
    for (Operation &operation : body)
      if (auto reduce = dyn_cast<ReduceOp>(operation))
        validateReduction(reduce);
    return success(ok);
  }

private:
  InFlightDiagnostic error(Operation *operation, StringRef code) {
    ok = false;
    return operation->emitOpError() << "[" << code << "] ";
  }

  void indexCarrier() {
    int64_t position = 0;
    for (Operation &operation : body) {
      positions[&operation] = position++;
      if (auto check = dyn_cast<CheckOp>(operation)) {
        checksByLabel[check.getLabel()] = check;
      } else if (auto binding = dyn_cast<MaterialBindOp>(operation)) {
        bindingsByValue[binding.getValue()] = binding;
      } else if (auto slot = dyn_cast<SlotOp>(operation)) {
        if (auto membership = slot.getMembership())
          messages[membership->instance][membership->role][membership->idx] = {
              slot.getVal(), slot.getOperation()};
      }
    }

    for (Operation &operation : body) {
      if (auto source = dyn_cast<InstantiateOp>(operation)) {
        addClaim(source.getClaim(), source.getAnchors(), source);
      } else if (auto reduce = dyn_cast<ReduceOp>(operation)) {
        ArrayAttr authored = reduce.getOutAnchors().value_or(ArrayAttr());
        for (auto [index, output] : llvm::enumerate(reduce.getOuts())) {
          DictionaryAttr anchors;
          if (authored && index < authored.size())
            anchors = dyn_cast<DictionaryAttr>(authored[index]);
          addClaim(output, anchors, reduce);
        }
      }
    }
  }

  void addClaim(Value value, DictionaryAttr anchors, Operation *at) {
    auto type = dyn_cast<ClaimType>(value.getType());
    if (!type || !anchors)
      return;
    // A claim whose descriptor will not canonicalize is a refusal, not a
    // claim that quietly does not exist. Dropping it here left the consumers
    // below reporting "unknown claim" instead of the reason, and made this
    // judgment engine fail open the moment the encoding-domain check that
    // currently runs first moved after it.
    auto descriptor =
        zkc::encoding::canonicalClaimDescriptor(type.getProfile(), anchors);
    if (!descriptor) {
      error(at, "zkc-E320") << llvm::toString(descriptor.takeError());
      return;
    }
    auto bytes = zkc::encoding::canonicalJsonBytes(*descriptor);
    if (!bytes) {
      error(at, "zkc-E320") << llvm::toString(bytes.takeError());
      return;
    }
    claims[value] = ClaimView{type.getProfile().str(), anchors,
                              std::move(*descriptor), std::move(*bytes)};
  }

  static bool classMatches(Value value, StringRef expected) {
    auto type = dyn_cast<ValType>(value.getType());
    return type && (expected == "*" || type.getValueClass() == expected);
  }

  static bool sourceMatches(Value value, VocabularyDepSource expected) {
    Operation *producer = value.getDefiningOp();
    switch (expected) {
    case VocabularyDepSource::Any:
      return true;
    case VocabularyDepSource::PublicBind:
      return producer && isa<BindOp>(producer);
    case VocabularyDepSource::ProverSlot:
      return producer && isa<SlotOp>(producer);
    case VocabularyDepSource::ChallengeCapability:
      if (!producer)
        return false;
      if (auto capability = dyn_cast<ChallengeCapabilityOpInterface>(producer))
        return capability.getChallengeValue() == value;
      return false;
    }
    llvm_unreachable("closed dependency-source constraint");
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

  std::optional<CheckView> buildCheckView(CheckOp check, Operation *at) {
    const CheckContract *contract =
        vocabulary.lookupCheckContract(check.getContract());
    if (!contract) {
      error(at, "zkc-E321") << "selected check contract '"
                            << check.getContract() << "' is not admitted";
      return std::nullopt;
    }
    if (sortedNames(check.getParams().value_or(DictionaryAttr())) !=
            sortedCopy(contract->parameters) ||
        sortedNames(check.getSemanticArgs().value_or(DictionaryAttr())) !=
            sortedCopy(contract->semanticParameters)) {
      error(at, "zkc-E321")
          << "selected check does not have the admitted parameter surface";
      return std::nullopt;
    }
    if (contract->isTransparent() != check.getExpr().has_value()) {
      error(at, "zkc-E321")
          << "selected check has the wrong opaque/transparent mode";
      return std::nullopt;
    }
    SmallVector<OperandView> layouts;
    zkc::semantics::solveCheckLayout(*contract, check.getInputs(), layouts);
    if (layouts.size() != 1) {
      error(at, "zkc-E321")
          << "selected check has " << layouts.size()
          << " valid operand layouts (exactly one is required)";
      return std::nullopt;
    }
    CheckView view{check, std::move(layouts.front()), nullptr};
    if (check.getExpr()) {
      auto normalized = normalizeExpr(*check.getExpr(), view.operands);
      if (!normalized) {
        error(at, "zkc-E322")
            << "selected transparent check expression is malformed: "
            << llvm::toString(normalized.takeError());
        return std::nullopt;
      }
      view.normalizedExpr = std::move(*normalized);
    }
    return view;
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

  std::optional<llvm::json::Value>
  canonicalAttribute(Attribute attribute, Operation *at, StringRef what) {
    auto result = zkc::encoding::attributeToCanonicalJson(attribute);
    if (!result) {
      error(at, "zkc-E320") << what << " is outside the canonical domain: "
                            << llvm::toString(result.takeError());
      return std::nullopt;
    }
    return std::move(*result);
  }

  bool validateInstanceShape(ReduceOp reduce,
                             const ReductionContract &contract) {
    bool valid = true;
    auto instanceError = [&](StringRef code) -> InFlightDiagnostic {
      valid = false;
      return error(reduce, code);
    };
    auto shapeError = [&]() -> InFlightDiagnostic {
      return instanceError("zkc-E320");
    };
    auto dependencyError = [&]() -> InFlightDiagnostic {
      return instanceError("zkc-E243");
    };
    auto membershipError = [&]() -> InFlightDiagnostic {
      return instanceError("zkc-E244");
    };
    auto sharingError = [&]() -> InFlightDiagnostic {
      return instanceError("zkc-E245");
    };
    auto prefixError = [&]() -> InFlightDiagnostic {
      return instanceError("zkc-E213");
    };

    if (contract.consumes.size() == 1 &&
        contract.consumes.front().isVariadic()) {
      const VocabularyConsumePattern &pattern = contract.consumes.front();
      if (reduce.getClaims().size() < pattern.min)
        shapeError() << "contract requires at least " << pattern.min
                     << " input claims, got " << reduce.getClaims().size();
      for (auto [index, value] : llvm::enumerate(reduce.getClaims()))
        if (cast<ClaimType>(value.getType()).getProfile() != pattern.profile)
          shapeError() << "input claim " << index << " must have profile '"
                       << pattern.profile << "'";
    } else {
      if (reduce.getClaims().size() != contract.consumes.size()) {
        shapeError() << "contract consumes " << contract.consumes.size()
                     << " claim(s), got " << reduce.getClaims().size();
      } else {
        for (auto [index, pattern] : llvm::enumerate(contract.consumes))
          if (cast<ClaimType>(reduce.getClaims()[index].getType())
                  .getProfile() != pattern.profile)
            shapeError() << "input claim " << index << " must have profile '"
                         << pattern.profile << "'";
      }
    }

    if (reduce.getOuts().size() != contract.outputs.size()) {
      shapeError() << "contract produces " << contract.outputs.size()
                   << " claim(s), got " << reduce.getOuts().size();
    } else {
      for (auto [index, output] : llvm::enumerate(contract.outputs))
        if (cast<ClaimType>(reduce.getOuts()[index].getType()).getProfile() !=
            output.profile)
          shapeError() << "output claim " << index << " must have profile '"
                       << output.profile << "'";
    }

    if (reduce.getDeps().size() != contract.depSlots.size()) {
      dependencyError() << "contract declares " << contract.depSlots.size()
                        << " dependency slot(s), got "
                        << reduce.getDeps().size();
    } else {
      for (auto [index, slot] : llvm::enumerate(contract.depSlots)) {
        Value dependency = reduce.getDeps()[index];
        auto type = dyn_cast<ValType>(dependency.getType());
        if (!type || type.getValueClass() != slot.payloadClass ||
            !sourceMatches(dependency, slot.source)) {
          dependencyError() << "dependency " << index
                            << " does not match role '" << slot.role << "'";
        }
      }
    }

    llvm::StringMap<uint64_t> expectedMessages;
    for (const VocabularyRound &round : contract.rounds)
      for (const VocabularyMessageRole &message : round.messages)
        expectedMessages[message.role] =
            message.multiplicity.resolve(reduce.getClaims().size());
    auto instance = messages.find(reduce.getLabel());
    if (instance != messages.end())
      for (const auto &role : instance->second)
        if (!expectedMessages.count(role.getKey())) {
          membershipError()
              << "contract has no message role '" << role.getKey() << "'";
        }
    for (const auto &expected : expectedMessages) {
      const llvm::DenseMap<int64_t, MessageView> *occurrences = nullptr;
      if (instance != messages.end()) {
        auto found = instance->second.find(expected.getKey());
        if (found != instance->second.end())
          occurrences = &found->second;
      }
      uint64_t count = occurrences ? occurrences->size() : 0;
      if (count != expected.getValue()) {
        membershipError() << "message role '" << expected.getKey() << "' needs "
                          << expected.getValue() << " occurrence(s), got "
                          << count;
        continue;
      }
      for (uint64_t index = 0; index < expected.getValue(); ++index)
        if (!occurrences->count(index))
          membershipError() << "message role '" << expected.getKey()
                            << "' has a non-canonical occurrence set";
    }

    if (reduce.getDeps().size() == contract.depSlots.size()) {
      llvm::StringMap<size_t> dependencyPositions;
      for (auto [index, slot] : llvm::enumerate(contract.depSlots))
        dependencyPositions[slot.role] = index;
      llvm::SmallPtrSet<Value, 8> challengesHere;
      SmallVector<Operation *> priorChallenges;
      for (auto [roundIndex, round] : llvm::enumerate(contract.rounds)) {
        auto dep = dependencyPositions.find(round.challengeUse.role);
        if (dep == dependencyPositions.end())
          continue;
        Value challengeValue = reduce.getDeps()[dep->second];
        auto challenge = dyn_cast_or_null<ChallengeCapabilityOpInterface>(
            challengeValue.getDefiningOp());
        if (!challenge || challenge.getChallengeValue() != challengeValue) {
          dependencyError()
              << "dependency role '" << round.challengeUse.role
              << "' is a priced challenge use but is not produced "
                 "by a challenge capability";
          continue;
        }
        std::string expectedCount =
            round.challengeUse.count ? std::to_string(round.challengeUse.count)
                                     : "1";
        if (challenge.getChallengeCount() != expectedCount) {
          dependencyError()
              << "dependency role '" << round.challengeUse.role
              << "' realizes challenge count " << challenge.getChallengeCount()
              << ", contract requires " << expectedCount;
        }
        if (!challengesHere.insert(challengeValue).second) {
          sharingError()
              << "one challenge capability fills two priced round uses";
        } else {
          auto [owner, fresh] =
              challengeOwners.try_emplace(challengeValue, reduce);
          if (!fresh)
            sharingError()
                << "priced challenge capability is already consumed by reduce '"
                << owner->second.getLabel() << "'";
        }
        Operation *challengeOp = challenge.getOperation();
        int64_t challengePosition = positions.lookup(challengeOp);
        for (Operation *prior : priorChallenges)
          if (positions.lookup(prior) > challengePosition)
            prefixError() << "round challenges do not follow contract order";
        if (instance != messages.end())
          for (size_t covered = 0; covered <= roundIndex; ++covered)
            for (const VocabularyMessageRole &message :
                 contract.rounds[covered].messages) {
              auto role = instance->second.find(message.role);
              if (role == instance->second.end())
                continue;
              for (const auto &occurrence : role->second) {
                Operation *messageOp = occurrence.second.operation;
                auto slot = cast<SlotOp>(messageOp);
                if (positions.lookup(messageOp) > challengePosition)
                  prefixError() << "message role '" << message.role
                                << "' is committed after its challenge";
                else if (slot.getUnabsorbed())
                  prefixError() << "message role '" << message.role
                                << "' is not absorbed before its challenge";
              }
            }
        priorChallenges.push_back(challengeOp);
      }
    }
    return valid;
  }

  std::optional<std::map<std::string, EvaluatedMaterial, std::less<>>>
  validateParameters(ReduceOp reduce, const ReductionContract &contract) {
    DictionaryAttr params = reduce.getParams().value_or(DictionaryAttr());
    if (sortedNames(params) != sortedKeys(contract.parameters)) {
      error(reduce, "zkc-E320")
          << "reduction parameter names do not exactly match contract '"
          << reduce.getContract() << "'";
      return std::nullopt;
    }

    std::map<std::string, EvaluatedMaterial, std::less<>> result;
    for (const auto &[name, sort] : contract.parameters) {
      Attribute attribute = params.get(name);
      auto canonical =
          canonicalAttribute(attribute, reduce, "reduction parameter");
      if (!canonical)
        return std::nullopt;
      switch (sort) {
      case ReductionParameterSort::Atom:
        result.emplace(name,
                       EvaluatedMaterial{MaterialExprSort::Atom, *canonical});
        break;
      case ReductionParameterSort::MaterialRef: {
        auto string = dyn_cast<StringAttr>(attribute);
        if (!string || !zkc::encoding::isSha256Ref(string.getValue())) {
          error(reduce, "zkc-E320")
              << "parameter '" << name << "' must be one MaterialRef";
          return std::nullopt;
        }
        result.emplace(name,
                       EvaluatedMaterial{MaterialExprSort::Ref, *canonical});
        break;
      }
      case ReductionParameterSort::MaterialRefVector: {
        auto array = dyn_cast<ArrayAttr>(attribute);
        if (!array || !llvm::all_of(array, [](Attribute member) {
              auto string = dyn_cast<StringAttr>(member);
              return string && zkc::encoding::isSha256Ref(string.getValue());
            })) {
          error(reduce, "zkc-E320")
              << "parameter '" << name << "' must be a MaterialRef vector";
          return std::nullopt;
        }
        result.emplace(name,
                       EvaluatedMaterial{MaterialExprSort::Refs, *canonical});
        break;
      }
      }
    }
    return result;
  }

  ClaimView *claim(Value value, Operation *at) {
    auto found = claims.find(value);
    if (found == claims.end()) {
      error(at, "zkc-E324")
          << "consumed claim has no canonical anchored descriptor";
      return nullptr;
    }
    return &found->second;
  }

  SmallVector<ClaimView *> inputClaims(ReduceOp reduce, MaterialOrder order,
                                       Operation *at) {
    SmallVector<ClaimView *> result;
    for (Value value : reduce.getClaims()) {
      ClaimView *view = claim(value, at);
      if (!view)
        return {};
      result.push_back(view);
    }
    if (order == MaterialOrder::Operand)
      return result;
    llvm::sort(result, [](const ClaimView *left, const ClaimView *right) {
      return left->descriptorBytes < right->descriptorBytes;
    });
    for (auto pair : llvm::zip(result, llvm::drop_begin(result)))
      if (std::get<0>(pair)->descriptorBytes ==
          std::get<1>(pair)->descriptorBytes) {
        error(at, "zkc-E324")
            << "canonical_unique inputs contain duplicate descriptors";
        return {};
      }
    return result;
  }

  Value dependency(ReduceOp reduce, const ReductionContract &contract,
                   StringRef role, Operation *at) {
    for (auto [index, slot] : llvm::enumerate(contract.depSlots))
      if (slot.role == role && index < reduce.getDeps().size())
        return reduce.getDeps()[index];
    error(at, "zkc-E324") << "material expression cannot resolve dependency '"
                          << role << "'";
    return {};
  }

  Value message(ReduceOp reduce, StringRef role, uint64_t occurrence,
                Operation *at) {
    auto instance = messages.find(reduce.getLabel());
    if (instance != messages.end()) {
      auto roleIt = instance->second.find(role);
      if (roleIt != instance->second.end()) {
        auto found = roleIt->second.find(occurrence);
        if (found != roleIt->second.end())
          return found->second.value;
      }
    }
    error(at, "zkc-E324") << "material expression cannot resolve message '"
                          << role << "' occurrence " << occurrence;
    return {};
  }

  std::optional<std::string> binding(Value value, Operation *at) {
    auto found = bindingsByValue.find(value);
    if (found == bindingsByValue.end()) {
      error(at, "zkc-E324")
          << "material expression value has no MaterialBinding";
      return std::nullopt;
    }
    ledger.usedMaterialBindings.insert(found->second.getOperation());
    return found->second.getSemanticRef().str();
  }

  std::optional<Value> localValue(const MaterialExpr &expr, ReduceOp reduce,
                                  const ReductionContract &contract,
                                  Operation *at) {
    if (expr.kind == MaterialExprKind::Dependency) {
      Value value = dependency(reduce, contract, expr.name, at);
      return value ? std::optional<Value>(value) : std::nullopt;
    }
    if (expr.kind == MaterialExprKind::Message) {
      Value value = message(reduce, expr.name, expr.index, at);
      return value ? std::optional<Value>(value) : std::nullopt;
    }
    error(at, "zkc-E323")
        << "value-identity attachment source is not a local-value selector";
    return std::nullopt;
  }

  std::optional<EvaluatedMaterial>
  evaluate(const MaterialExpr &expr, ReduceOp reduce,
           const ReductionContract &contract,
           const std::map<std::string, EvaluatedMaterial, std::less<>> &params,
           Operation *at) {
    auto ref = [&](StringRef value) -> std::optional<EvaluatedMaterial> {
      if (!zkc::encoding::isSha256Ref(value)) {
        error(at, "zkc-E324")
            << "material expression resolved a non-MaterialRef value";
        return std::nullopt;
      }
      return EvaluatedMaterial{MaterialExprSort::Ref, value.str()};
    };

    switch (expr.kind) {
    case MaterialExprKind::LiteralRef:
      return ref(expr.name);
    case MaterialExprKind::InputAnchor: {
      if (expr.index >= reduce.getClaims().size()) {
        error(at, "zkc-E324") << "input-anchor index is out of range";
        return std::nullopt;
      }
      ClaimView *view = claim(reduce.getClaims()[expr.index], at);
      auto anchor =
          view ? view->anchors.getAs<StringAttr>(expr.name) : StringAttr();
      if (!anchor) {
        error(at, "zkc-E324")
            << "input anchor '" << expr.name << "' does not resolve";
        return std::nullopt;
      }
      return ref(anchor.getValue());
    }
    case MaterialExprKind::Dependency:
    case MaterialExprKind::Message: {
      auto value = localValue(expr, reduce, contract, at);
      if (!value)
        return std::nullopt;
      auto semanticRef = binding(*value, at);
      return semanticRef ? ref(*semanticRef) : std::nullopt;
    }
    case MaterialExprKind::ParameterRef:
    case MaterialExprKind::ParameterRefs:
    case MaterialExprKind::ParameterAtom: {
      auto found = params.find(expr.name);
      if (found == params.end() || found->second.sort != expr.sort) {
        error(at, "zkc-E324") << "material expression parameter '" << expr.name
                              << "' has the wrong runtime sort";
        return std::nullopt;
      }
      return found->second;
    }
    case MaterialExprKind::Construct: {
      llvm::json::Array typedArguments;
      for (const MaterialExpr &argument : expr.arguments) {
        auto evaluated = evaluate(argument, reduce, contract, params, at);
        if (!evaluated)
          return std::nullopt;
        llvm::json::Array typed;
        typed.push_back(materialSortName(evaluated->sort));
        typed.push_back(evaluated->value);
        typedArguments.push_back(std::move(typed));
      }
      llvm::json::Array preimage;
      preimage.push_back("construct");
      preimage.push_back(expr.name);
      preimage.push_back(std::move(typedArguments));
      auto digest = zkc::encoding::taggedSha256Ref(
          "zkc/material-expr\n", llvm::json::Value(std::move(preimage)));
      if (!digest) {
        error(at, "zkc-E324") << "material constructor is not canonical: "
                              << llvm::toString(digest.takeError());
        return std::nullopt;
      }
      return EvaluatedMaterial{MaterialExprSort::Ref, std::move(*digest)};
    }
    case MaterialExprKind::InputAnchors: {
      llvm::json::Array values;
      SmallVector<ClaimView *> inputs = inputClaims(reduce, expr.order, at);
      if (inputs.size() != reduce.getClaims().size())
        return std::nullopt;
      for (ClaimView *view : inputs) {
        auto anchor = view->anchors.getAs<StringAttr>(expr.name);
        if (!anchor || !zkc::encoding::isSha256Ref(anchor.getValue())) {
          error(at, "zkc-E324") << "input anchor vector does not resolve";
          return std::nullopt;
        }
        values.push_back(anchor.getValue());
      }
      return EvaluatedMaterial{MaterialExprSort::Refs, std::move(values)};
    }
    case MaterialExprKind::Messages: {
      llvm::json::Array values;
      uint64_t count = 0;
      for (const VocabularyRound &round : contract.rounds)
        for (const VocabularyMessageRole &role : round.messages)
          if (role.role == expr.name)
            count = role.multiplicity.resolve(reduce.getClaims().size());
      for (uint64_t index = 0; index < count; ++index) {
        Value value = message(reduce, expr.name, index, at);
        if (!value)
          return std::nullopt;
        auto semanticRef = binding(value, at);
        if (!semanticRef)
          return std::nullopt;
        values.push_back(*semanticRef);
      }
      return EvaluatedMaterial{MaterialExprSort::Refs, std::move(values)};
    }
    case MaterialExprKind::List: {
      llvm::json::Array values;
      for (const MaterialExpr &item : expr.arguments) {
        auto evaluated = evaluate(item, reduce, contract, params, at);
        if (!evaluated || evaluated->sort != MaterialExprSort::Ref)
          return std::nullopt;
        values.push_back(evaluated->value);
      }
      return EvaluatedMaterial{MaterialExprSort::Refs, std::move(values)};
    }
    case MaterialExprKind::InputDescriptor: {
      if (expr.index >= reduce.getClaims().size()) {
        error(at, "zkc-E324") << "input-descriptor index is out of range";
        return std::nullopt;
      }
      ClaimView *view = claim(reduce.getClaims()[expr.index], at);
      if (!view)
        return std::nullopt;
      return EvaluatedMaterial{MaterialExprSort::Claim, view->descriptor};
    }
    case MaterialExprKind::InputDescriptors: {
      llvm::json::Array descriptors;
      SmallVector<ClaimView *> inputs = inputClaims(reduce, expr.order, at);
      if (inputs.size() != reduce.getClaims().size())
        return std::nullopt;
      for (ClaimView *view : inputs)
        descriptors.push_back(view->descriptor);
      return EvaluatedMaterial{MaterialExprSort::Claims,
                               std::move(descriptors)};
    }
    case MaterialExprKind::Literal:
      return EvaluatedMaterial{MaterialExprSort::Atom, expr.literal};
    }
    llvm_unreachable("closed material-expression kind");
  }

  SmallVector<Value> operands(CheckView &check, StringRef role, Operation *at) {
    auto found = check.operands.roles.find(role);
    if (found == check.operands.roles.end()) {
      error(at, "zkc-E323")
          << "selected check has no operand role '" << role << "'";
      return {};
    }
    return found->second;
  }

  StringRef semanticArgument(CheckOp check, StringRef role) {
    auto arguments = check.getSemanticArgs();
    auto value = arguments ? arguments->getAs<StringAttr>(role) : StringAttr();
    return value ? value.getValue() : StringRef();
  }

  bool matchAttachment(
      const ReductionCheckAttachment &attachment, CheckView &check,
      ReduceOp reduce, const ReductionContract &contract,
      const std::map<std::string, EvaluatedMaterial, std::less<>> &params) {
    // ValueIdentity is deliberately a local SSA judgment. Its source is
    // admitted as exactly dependency/message, so resolving it must not demand
    // a MaterialBinding or manufacture a global semantic reference.
    if (attachment.kind == ReductionCheckAttachmentKind::ValueIdentity) {
      auto local = localValue(attachment.source, reduce, contract, reduce);
      SmallVector<Value> selected =
          operands(check, attachment.targetRole, reduce);
      if (!local || selected.size() != 1 || selected.front() != *local) {
        error(reduce, "zkc-E323")
            << "local SSA attachment does not match role '"
            << attachment.targetRole << "'";
        return false;
      }
      return true;
    }

    auto expected =
        evaluate(attachment.source, reduce, contract, params, reduce);
    if (!expected)
      return false;
    switch (attachment.kind) {
    case ReductionCheckAttachmentKind::SemanticParameter: {
      auto value = expected->value.getAsString();
      if (expected->sort != MaterialExprSort::Ref || !value ||
          semanticArgument(check.op, attachment.targetRole) != *value) {
        error(reduce, "zkc-E323")
            << "semantic parameter attachment does not match role '"
            << attachment.targetRole << "'";
        return false;
      }
      return true;
    }
    case ReductionCheckAttachmentKind::ValueIdentity:
      llvm_unreachable("handled before material evaluation");
    case ReductionCheckAttachmentKind::MaterialRefEquality: {
      auto value = expected->value.getAsString();
      SmallVector<Value> selected =
          operands(check, attachment.targetRole, reduce);
      auto actual = selected.size() == 1 ? binding(selected.front(), reduce)
                                         : std::nullopt;
      if (expected->sort != MaterialExprSort::Ref || !value || !actual ||
          *actual != *value) {
        error(reduce, "zkc-E323")
            << "material-reference attachment does not match role '"
            << attachment.targetRole << "'";
        return false;
      }
      return true;
    }
    case ReductionCheckAttachmentKind::MaterialRefVectorEquality: {
      const llvm::json::Array *expectedValues = expected->value.getAsArray();
      SmallVector<Value> selected =
          operands(check, attachment.targetRole, reduce);
      bool matches = expected->sort == MaterialExprSort::Refs &&
                     expectedValues &&
                     expectedValues->size() == selected.size();
      for (size_t index = 0; matches && index < selected.size(); ++index) {
        auto expectedRef = (*expectedValues)[index].getAsString();
        auto actual = binding(selected[index], reduce);
        matches &= expectedRef && actual && *expectedRef == *actual;
      }
      if (!matches) {
        error(reduce, "zkc-E323")
            << "material-reference vector does not match role '"
            << attachment.targetRole << "'";
        return false;
      }
      return true;
    }
    case ReductionCheckAttachmentKind::CommonMaterialRefEquality: {
      const llvm::json::Array *expectedValues = expected->value.getAsArray();
      std::optional<StringRef> common;
      bool matches = expected->sort == MaterialExprSort::Refs &&
                     expectedValues && !expectedValues->empty();
      if (matches)
        common = (*expectedValues)[0].getAsString();
      matches &= common.has_value();
      for (size_t index = 1; matches && index < expectedValues->size(); ++index)
        matches &= (*expectedValues)[index].getAsString() == common;
      SmallVector<Value> selected =
          operands(check, attachment.targetRole, reduce);
      matches &= selected.size() == 1;
      if (selected.size() == 1) {
        auto actual = binding(selected.front(), reduce);
        matches &= actual && common && *actual == *common;
      }
      if (!matches) {
        error(reduce, "zkc-E323")
            << "common-material attachment does not match role '"
            << attachment.targetRole << "'";
        return false;
      }
      return true;
    }
    }
    llvm_unreachable("closed reduction attachment kind");
  }

  void validateChecks(
      ReduceOp reduce, const ReductionContract &contract,
      const std::map<std::string, EvaluatedMaterial, std::less<>> &params) {
    DictionaryAttr selections = reduce.getChecks();
    if (sortedNames(selections) != sortedKeys(contract.checks)) {
      error(reduce, "zkc-E321")
          << "body-check roles do not exactly match reduction contract '"
          << reduce.getContract() << "'";
      return;
    }

    llvm::SmallPtrSet<Operation *, 8> selectedHere;
    for (const auto &[role, slot] : contract.checks) {
      auto selectedLabel = selections.getAs<StringAttr>(role);
      CheckOp selected = selectedLabel
                             ? checksByLabel.lookup(selectedLabel.getValue())
                             : CheckOp();
      if (!selected || selected.getContract() != slot.contract) {
        error(reduce, "zkc-E321") << "body role '" << role
                                  << "' does not select a check of contract '"
                                  << slot.contract << "'";
        continue;
      }
      if (!selectedHere.insert(selected.getOperation()).second) {
        error(reduce, "zkc-E327")
            << "one check is selected for two roles in the same reduction";
        continue;
      }
      auto [owner, fresh] = ledger.reductionCheckOwners.try_emplace(
          selected.getOperation(), reduce.getOperation());
      if (!fresh && owner->second != reduce.getOperation()) {
        error(reduce, "zkc-E327") << "check '" << selectedLabel.getValue()
                                  << "' already justifies another reduction";
        continue;
      }

      auto view = buildCheckView(selected, reduce);
      if (!view)
        continue;

      llvm::json::Object expectedParameters;
      for (const auto &[name, value] : slot.parameters)
        expectedParameters.try_emplace(name, value);
      auto actualParameters =
          canonicalAttribute(selected.getParams().value_or(
                                 DictionaryAttr::get(container->getContext())),
                             reduce, "selected check parameters");
      if (!actualParameters ||
          !sameJson(*actualParameters,
                    llvm::json::Value(std::move(expectedParameters)))) {
        error(reduce, "zkc-E322")
            << "body role '" << role << "' has the wrong fixed parameters";
        continue;
      }
      llvm::json::Value expectedPredicate = slot.transparentPredicate
                                                ? *slot.transparentPredicate
                                                : llvm::json::Value(nullptr);
      if (!sameJson(view->normalizedExpr, expectedPredicate)) {
        error(reduce, "zkc-E322")
            << "body role '" << role << "' has the wrong transparent predicate";
        continue;
      }

      for (const ReductionCheckAttachment &attachment : slot.attachments)
        matchAttachment(attachment, *view, reduce, contract, params);
    }
  }

  void validateConstraints(
      ReduceOp reduce, const ReductionContract &contract,
      const std::map<std::string, EvaluatedMaterial, std::less<>> &params) {
    for (const MaterialConstraint &constraint : contract.constraints) {
      auto left = evaluate(constraint.left, reduce, contract, params, reduce);
      auto right = evaluate(constraint.right, reduce, contract, params, reduce);
      if (!left || !right)
        continue;
      if (left->sort != right->sort || !sameJson(left->value, right->value))
        error(reduce, "zkc-E325")
            << "an admitted material-identity constraint does not hold: left "
            << llvm::formatv("{0}", left->value) << ", right "
            << llvm::formatv("{0}", right->value);
    }
  }

  void validateOutputs(
      ReduceOp reduce, const ReductionContract &contract,
      const std::map<std::string, EvaluatedMaterial, std::less<>> &params) {
    ArrayAttr authored = reduce.getOutAnchors().value_or(ArrayAttr());
    if (!authored || authored.size() != contract.outputs.size()) {
      error(reduce, "zkc-E326") << "out_anchors must contain one exact "
                                   "dictionary per contract output";
      return;
    }
    if (reduce.getOuts().size() != contract.outputs.size())
      return;

    for (auto [index, output] : llvm::enumerate(contract.outputs)) {
      auto authoredDictionary = dyn_cast<DictionaryAttr>(authored[index]);
      if (!authoredDictionary) {
        error(reduce, "zkc-E326")
            << "output " << index << " anchor assertion is not a dictionary";
        continue;
      }
      llvm::json::Object expected;
      bool evaluable = true;
      for (const auto &[name, expression] : output.anchors) {
        auto value = evaluate(expression, reduce, contract, params, reduce);
        auto reference = value ? value->value.getAsString() : std::nullopt;
        if (!value || value->sort != MaterialExprSort::Ref || !reference) {
          evaluable = false;
          break;
        }
        // `getAsString()` is a view into the temporary EvaluatedMaterial.
        // Materialize an owned string before the value leaves this iteration;
        // otherwise llvm::json may retain a dangling StringRef and make an
        // otherwise exact output descriptor non-canonical.
        expected.try_emplace(name, reference->str());
      }
      auto actual = canonicalAttribute(authoredDictionary, reduce,
                                       "authored output anchors");
      if (evaluable) {
        llvm::json::Value expectedValue(std::move(expected));
        if (!actual || !sameJson(*actual, expectedValue)) {
          auto expectedBytes = zkc::encoding::canonicalJsonBytes(expectedValue);
          auto actualBytes =
              actual ? zkc::encoding::canonicalJsonBytes(*actual)
                     : llvm::Expected<std::string>(llvm::createStringError(
                           "anchor dictionary is not canonical"));
          auto diagnostic = error(reduce, "zkc-E326")
                            << "output " << index
                            << " descriptor does not equal the contract "
                               "constructor";
          if (expectedBytes)
            diagnostic << "; expected " << *expectedBytes;
          else
            diagnostic << "; expected descriptor is not canonical: "
                       << llvm::toString(expectedBytes.takeError());
          if (actualBytes)
            diagnostic << ", got " << *actualBytes;
          else
            diagnostic << ", actual descriptor is not canonical: "
                       << llvm::toString(actualBytes.takeError());
        }
      }
    }
  }

  void validateReduction(ReduceOp reduce) {
    const ReductionContract *contract =
        vocabulary.lookupReductionContract(reduce.getContract());
    if (!contract) {
      error(reduce, "zkc-E320")
          << "unknown reduction contract '" << reduce.getContract() << "'";
      return;
    }
    bool shapeValid = validateInstanceShape(reduce, *contract);
    auto params = validateParameters(reduce, *contract);
    if (!shapeValid || !params)
      return;
    validateChecks(reduce, *contract, *params);
    validateConstraints(reduce, *contract, *params);
    validateOutputs(reduce, *contract, *params);
  }

  Operation *container;
  const ProtocolVocabulary &vocabulary;
  zkc::semantics::ClosureLedger &ledger;
  Block &body;
  bool ok = true;

  llvm::DenseMap<Operation *, int64_t> positions;
  llvm::StringMap<CheckOp> checksByLabel;
  llvm::DenseMap<Value, MaterialBindOp> bindingsByValue;
  llvm::StringMap<llvm::StringMap<llvm::DenseMap<int64_t, MessageView>>>
      messages;
  llvm::DenseMap<Value, ClaimView> claims;
  llvm::DenseMap<Value, ReduceOp> challengeOwners;
};

} // namespace

LogicalResult
zkc::semantics::verifyReductionClosure(Operation *container,
                                       const ProtocolVocabulary &vocabulary,
                                       zkc::semantics::ClosureLedger &ledger) {
  return Matcher(container, vocabulary, ledger).run();
}
