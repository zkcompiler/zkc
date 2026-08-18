//===- TestSoundnessKernel.cpp - declaration kernel test pass ---*- C++ -*-===//
//
// The shipped signature read through the real loader, then held to the
// kernel's declaration judgments: every rule and binding well-formed, every
// declaration carrying its own content digest, and the loader refusing each
// way a signature can be damaged.
//
//===----------------------------------------------------------------------===//
#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Soundness/SignatureEncoding.h"
#include "zkc/Soundness/SignatureFile.h"
#include "zkc/Soundness/SoundnessKernel.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

#include <functional>
#include <set>
#include <string>

using namespace mlir;

namespace {

using SignatureMutation = std::function<llvm::Error(llvm::json::Object &root)>;

/// Read the signature, damage it in one exact way, and hand the result to the
/// real loader.  The loader is the fail-closed boundary between a file an
/// author edits and the declarations the kernel evaluates, so every one of
/// these must refuse rather than repair.
llvm::Error loadMutatedSignature(llvm::StringRef path, llvm::StringRef label,
                                 const SignatureMutation &mutate) {
  auto buffer = llvm::MemoryBuffer::getFile(path);
  if (!buffer)
    return llvm::createStringError(buffer.getError(), "cannot read signature");
  auto document = llvm::json::parse((*buffer)->getBuffer());
  if (!document)
    return document.takeError();
  llvm::json::Object *root = document->getAsObject();
  if (!root)
    return llvm::createStringError("the signature document is not an object");
  if (llvm::Error error = mutate(*root))
    return std::move(error);
  std::string bytes;
  llvm::raw_string_ostream stream(bytes);
  if (llvm::Error error = zkc::encoding::writeCanonicalJson(*document, stream))
    return std::move(error);
  stream.flush();
  auto signature = zkc::soundness::parseSignature(bytes, label);
  if (signature)
    return llvm::createStringError("the loader admitted a damaged signature");
  return signature.takeError();
}

llvm::json::Object *section(llvm::json::Object &root, llvm::StringRef name,
                            llvm::StringRef id) {
  llvm::json::Object *entries = root.getObject(name);
  return entries ? entries->getObject(id) : nullptr;
}

const zkc::soundness::RuleBinding *
findBindingForRule(const zkc::soundness::SoundnessCatalog &catalog,
                   llvm::StringRef ruleId) {
  auto it = llvm::find_if(catalog.bindings, [&](const auto &entry) {
    return entry.second.ruleRef.id == ruleId;
  });
  return it == catalog.bindings.end() ? nullptr : &it->second;
}

bool hasHypothesis(const zkc::soundness::SoundnessRule &rule,
                   llvm::StringRef propositionRef) {
  return llvm::any_of(
      rule.externalHypotheses,
      [&](const zkc::soundness::ExternalHypothesisTemplate &hypothesis) {
        return hypothesis.propositionRef == propositionRef;
      });
}

const zkc::soundness::ExternalHypothesisTemplate *
findHypothesis(const zkc::soundness::SoundnessRule &rule,
               llvm::StringRef propositionRef) {
  auto hypothesis = llvm::find_if(
      rule.externalHypotheses,
      [&](const zkc::soundness::ExternalHypothesisTemplate &candidate) {
        return candidate.propositionRef == propositionRef;
      });
  return hypothesis == rule.externalHypotheses.end() ? nullptr : &*hypothesis;
}

bool hasParameter(const zkc::soundness::SoundnessRule &rule,
                  llvm::StringRef name, zkc::soundness::ValueSort sort) {
  return llvm::any_of(rule.parameters,
                      [&](const zkc::soundness::TypedDeclaration &parameter) {
                        return parameter.name == name && parameter.sort == sort;
                      });
}

bool sameProjection(const zkc::soundness::ArtifactProjection &lhs,
                    const zkc::soundness::ArtifactProjection &rhs) {
  return lhs.kind == rhs.kind && lhs.resultSort == rhs.resultSort &&
         lhs.field == rhs.field && lhs.inputIndex == rhs.inputIndex &&
         lhs.roundSelector.kind == rhs.roundSelector.kind &&
         lhs.roundSelector.roundKind == rhs.roundSelector.roundKind &&
         lhs.roundSelector.position == rhs.roundSelector.position &&
         lhs.aggregate == rhs.aggregate;
}

bool sameLiteral(
    const std::variant<zkc::registry::Rational, std::string, bool,
                       zkc::soundness::AlgebraInstanceValue> &lhs,
    const std::variant<zkc::registry::Rational, std::string, bool,
                       zkc::soundness::AlgebraInstanceValue> &rhs) {
  if (lhs.index() != rhs.index())
    return false;
  if (const auto *value = std::get_if<zkc::registry::Rational>(&lhs))
    return value->compare(std::get<zkc::registry::Rational>(rhs)) == 0;
  if (const auto *value = std::get_if<std::string>(&lhs))
    return *value == std::get<std::string>(rhs);
  if (const auto *value = std::get_if<bool>(&lhs))
    return *value == std::get<bool>(rhs);
  return std::get<zkc::soundness::AlgebraInstanceValue>(lhs) ==
         std::get<zkc::soundness::AlgebraInstanceValue>(rhs);
}

bool sameBindingValue(const zkc::soundness::BindingValue &lhs,
                      const zkc::soundness::BindingValue &rhs) {
  return lhs.kind == rhs.kind && lhs.sort == rhs.sort &&
         sameLiteral(lhs.literal, rhs.literal) &&
         lhs.reference == rhs.reference && lhs.premisePort == rhs.premisePort &&
         sameProjection(lhs.artifactProjection, rhs.artifactProjection);
}

bool isIntegerLiteral(const zkc::soundness::BindingValue &value,
                      int64_t expected) {
  const auto *number = std::get_if<zkc::registry::Rational>(&value.literal);
  return value.kind == zkc::soundness::BindingValueKind::Literal &&
         value.sort == zkc::soundness::ValueSort::Integer && number &&
         number->compare(zkc::registry::Rational::fromInteger(expected)) == 0;
}

const std::vector<zkc::soundness::BindingValue> *
conditionArguments(const zkc::soundness::RuleBinding &binding,
                   llvm::StringRef slot) {
  auto arguments = binding.conditionArgumentBindings.find(slot);
  return arguments == binding.conditionArgumentBindings.end()
             ? nullptr
             : &arguments->second;
}

const std::vector<zkc::soundness::BindingValue> *
hypothesisArguments(const zkc::soundness::RuleBinding &binding,
                    llvm::StringRef slot) {
  auto arguments = binding.hypothesisArgumentBindings.find(slot);
  return arguments == binding.hypothesisArgumentBindings.end()
             ? nullptr
             : &arguments->second;
}

bool isRationalLiteral(const zkc::soundness::QuantityTemplate &quantity,
                       int64_t value) {
  return quantity.kind == zkc::soundness::QuantityKind::RationalLiteral &&
         quantity.literal.compare(
             zkc::registry::Rational::fromInteger(value)) == 0;
}

bool boundReadsPremise(const zkc::soundness::RuleBound &bound) {
  if (bound.kind == zkc::soundness::RuleBoundKind::ScalarBound)
    return true;
  return llvm::any_of(bound.operands, boundReadsPremise);
}

struct TestSoundnessKernelPass
    : public PassWrapper<TestSoundnessKernelPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestSoundnessKernelPass)

  TestSoundnessKernelPass() = default;
  TestSoundnessKernelPass(const TestSoundnessKernelPass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override { return "test-soundness-kernel"; }
  StringRef getDescription() const override {
    return "test the owned Soundness Kernel declaration model and legacy "
           "adapter";
  }

  Option<std::string> signaturePath{*this, "signature",
                                    llvm::cl::desc("the shipped signature")};

  void runOnOperation() override {
    auto fail = [&](const llvm::Twine &message) {
      getOperation().emitError() << message;
      signalPassFailure();
    };

    auto signature = zkc::soundness::loadSignatureFromFile(signaturePath);
    if (!signature)
      return fail(llvm::toString(signature.takeError()));
    const zkc::soundness::SoundnessCatalog *catalog = &signature->catalog;

    size_t declaredRules = catalog->rules.size();
    size_t admittedRules = 0;
    size_t reductionBindings = 0;
    size_t pathBindings = 0;
    for (const auto &[id, rule] : catalog->rules) {
      (void)id;
      admittedRules += rule.status == zkc::soundness::RuleStatus::Admitted;
    }
    for (const auto &[id, binding] : catalog->bindings) {
      (void)id;
      reductionBindings +=
          binding.anchor.kind ==
          zkc::soundness::ProtocolAnchorKind::ReductionContract;
      pathBindings += binding.anchor.kind ==
                      zkc::soundness::ProtocolAnchorKind::PathTransition;
    }

    size_t zeroBindingRules =
        llvm::count_if(catalog->rules, [&](const auto &ruleEntry) {
          return llvm::none_of(
              catalog->bindings, [&](const auto &bindingEntry) {
                return bindingEntry.second.ruleRef == ruleEntry.second.ref;
              });
        });

    const std::set<std::string> preservationRuleIds = {
        "zkc.pcs.kzg_batch",
        "zkc.pcs.kzg_batch_arsdh",
    };
    for (const std::string &ruleId : preservationRuleIds) {
      std::string bindingId = ruleId + "@reduction:kzg_batch";
      auto rule = catalog->rules.find(ruleId);
      auto binding = catalog->bindings.find(bindingId);
      if (rule == catalog->rules.end() || binding == catalog->bindings.end())
        return fail("a KZG preservation rule has no executable declaration and "
                    "exact reduction binding");
      const auto *body =
          std::get_if<zkc::soundness::SpecialSoundnessPreservation>(
              &rule->second.body);
      const auto *source = rule->second.premises.size() == 1
                               ? &rule->second.premises.front()
                               : nullptr;
      auto relation = binding->second.premiseRelations.find("source_ss");
      if (!body || body->sourcePort != "source_ss" || !source ||
          source->expectedSubjectSchema !=
              "zkc.subject.consumed_claim_vector" ||
          source->expectedIndex.index.notion !=
              zkc::soundness::SecurityNotion::SpecialSoundness ||
          source->expectedIndex.index.track !=
              zkc::soundness::SecurityTrack::Knowledge ||
          relation == binding->second.premiseRelations.end() ||
          relation->second.kind !=
              zkc::soundness::SubjectRelationKind::ConsumedClaimVector ||
          relation->second.selector !=
              zkc::soundness::ConsumedClaimSelectorKind::AllReductionInputs ||
          body->appendedCoordinates.kind !=
              zkc::soundness::CoordinateSequence::Kind::Contract ||
          body->appendedCoordinates.cases.size() != 1 ||
          body->appendedCoordinates.cases.front().caseName != "batch" ||
          body->appendedCoordinates.cases.front().labelProjection !=
              zkc::soundness::ContractLabelProjection::CaseName ||
          body->appendedCoordinates.cases.front().arity.kind !=
              zkc::soundness::QuantityKind::Parameter ||
          body->appendedCoordinates.cases.front().arity.name != "s" ||
          !body->appendedCoordinates.cases.front().challengeSpace ||
          body->appendedCoordinates.cases.front().challengeSpace->kind !=
              zkc::soundness::QuantityKind::ContractRoundFact ||
          boundReadsPremise(body->conclusionFailureBound) ||
          !hasParameter(rule->second, "s",
                        zkc::soundness::ValueSort::Integer) ||
          !hasParameter(rule->second, "srs_max_degree",
                        zkc::soundness::ValueSort::Integer) ||
          !hasParameter(rule->second, "algebra",
                        zkc::soundness::ValueSort::AlgebraInstance) ||
          !hasParameter(rule->second, "srs",
                        zkc::soundness::ValueSort::SrsInstance))
        return fail("a KZG preservation rule does not carry its exact source, "
                    "coordinate, or theorem inputs");
    }

    // A declaration's revision is its own content digest, so recomputing it
    // must reproduce what the loader stored; a binding pins the exact revision
    // of the rule it names.
    for (const auto &[id, rule] : catalog->rules) {
      auto digest = zkc::soundness::ruleDigest(rule);
      if (!digest)
        return fail(llvm::toString(digest.takeError()));
      if (rule.ref.id != id || rule.ref.sourceRevision != *digest)
        return fail("rule '" + id + "' does not carry its own content digest");
    }
    for (const auto &[id, binding] : catalog->bindings) {
      auto digest = zkc::soundness::bindingDigest(binding);
      if (!digest)
        return fail(llvm::toString(digest.takeError()));
      auto rule = catalog->rules.find(binding.ruleRef.id);
      if (binding.ref.id != id || binding.ref.sourceRevision != *digest ||
          rule == catalog->rules.end() || binding.ruleRef != rule->second.ref)
        return fail("binding '" + id +
                    "' does not carry its own digest and pin the exact "
                    "revision of the rule it names");
      zkc::soundness::RuleWfResult bindingWf =
          zkc::soundness::checkRuleBindingWellFormed(catalog->schemas,
                                                     rule->second, binding);
      if (!bindingWf.accepted())
        return fail(
            "binding '" + id + "' does not pass binding WF: " +
            zkc::soundness::ruleWfRefusalCodeName(bindingWf.refusal->code));
    }
    for (const auto &[id, definition] : catalog->schemas.primitiveGames)
      if (definition.ref.id != id || definition.ref.sourceRevision.empty())
        return fail("a primitive-game definition is not versioned");
    for (const auto &[id, proposition] : catalog->schemas.propositions)
      if (proposition.ref.id != id || proposition.ref.sourceRevision.empty())
        return fail("a proposition schema is not versioned");
    for (const auto &[id, decider] : catalog->schemas.machineDeciders)
      if (decider.ref.id != id || decider.ref.sourceRevision.empty())
        return fail("a machine decider is not versioned");

    using DeciderKind = zkc::soundness::MachineDeciderKind;
    using Sort = zkc::soundness::ValueSort;
    const std::map<std::string, std::pair<DeciderKind, std::vector<Sort>>,
                   std::less<>>
        expectedDeciders = {
            {"zkc.side.one_message_role",
             {DeciderKind::OneMessageRole, {Sort::ReductionContract}}},
            {"zkc.side.space_embeds",
             {DeciderKind::SpaceEmbeds,
              {Sort::ReductionContract, Sort::Integer}}},
            {"zkc.side.bound_bites",
             {DeciderKind::BoundBites, {Sort::ReductionContract}}},
            {"zkc.side.field_class",
             {DeciderKind::FieldClass,
              {Sort::ReductionContract, Sort::String}}},
            {"zkc.side.space_covers_arity",
             {DeciderKind::SpaceCoversArity,
              {Sort::ReductionContract, Sort::Integer}}},
            {"zkc.side.batch_arity",
             {DeciderKind::BatchArity, {Sort::Integer}}},
            {"zkc.side.space_covers_batch",
             {DeciderKind::SpaceCoversBatch, {Sort::Integer, Sort::Integer}}},
            {"zkc.side.same_point",
             {DeciderKind::SamePoint, {Sort::ReductionContract}}},
            {"zkc.side.batch_after_material",
             {DeciderKind::BatchAfterMaterial, {Sort::ReductionContract}}},
            {"zkc.side.fri_shape",
             {DeciderKind::FriShape,
              {Sort::Integer, Sort::Integer, Sort::Integer, Sort::Integer}}},
            {"zkc.side.johnson_fold_param",
             {DeciderKind::JohnsonFoldParam, {Sort::Integer}}},
            {"zkc.side.johnson_slack",
             {DeciderKind::JohnsonSlack,
              {Sort::Rational, Sort::Integer, Sort::Integer}}},
            {"zkc.side.johnson_multiplicity",
             {DeciderKind::JohnsonMultiplicity,
              {Sort::Integer, Sort::Rational, Sort::Integer}}},
            {"zkc.side.johnson_delta",
             {DeciderKind::JohnsonDelta,
              {Sort::Rational, Sort::Rational, Sort::Integer}}},
            {"zkc.side.udr_domain_floor",
             {DeciderKind::UdrDomainFloor,
              {Sort::Integer, Sort::Integer, Sort::Integer}}},
            {"zkc.side.udr_theta_window",
             {DeciderKind::UdrThetaWindow,
              {Sort::Rational, Sort::Integer, Sort::Integer}}},
            {"zkc.side.random_words_eta_floor",
             {DeciderKind::RandomWordsEtaFloor,
              {Sort::Rational, Sort::Integer, Sort::Integer}}},
            {"zkc.side.threshold_delta_window",
             {DeciderKind::ThresholdDeltaWindow,
              {Sort::Rational, Sort::Integer}}},
            {"zkc.side.pow_pinned",
             {DeciderKind::PowPinned, {Sort::RoundAdjacency}}},
            {"zkc.side.pow_adjacent",
             {DeciderKind::PowAdjacent, {Sort::RoundAdjacency}}},
            {"zkc.side.duplex_spine",
             {DeciderKind::DuplexSpine, {Sort::PathTransition}}},
            {"zkc.side.codec_bias_declared",
             {DeciderKind::CodecBiasDeclared, {Sort::PathTransition}}},
        };
    if (catalog->schemas.machineDeciders.size() != expectedDeciders.size())
      return fail("the closed machine-decider set changed");
    for (const auto &[id, expected] : expectedDeciders) {
      auto actual = catalog->schemas.machineDeciders.find(id);
      if (actual == catalog->schemas.machineDeciders.end() ||
          actual->second.kind != expected.first ||
          actual->second.argumentTypes != expected.second)
        return fail("machine decider '" + id +
                    "' has the wrong kind or signature");
    }
    if (catalog->schemas.machineDeciders.count("zkc.side.degrees_within_srs") ||
        catalog->schemas.machineDeciders.count("zkc.side.algebra_match"))
      return fail("externally supplied algebra/SRS facts became machine "
                  "deciders");
    auto degreesProposition =
        catalog->schemas.propositions.find("zkc.side.degrees_within_srs");
    auto algebraProposition =
        catalog->schemas.propositions.find("zkc.side.algebra_match");
    if (degreesProposition == catalog->schemas.propositions.end() ||
        degreesProposition->second.argumentTypes !=
            std::vector<Sort>{Sort::Subject, Sort::SrsInstance,
                              Sort::Integer} ||
        algebraProposition == catalog->schemas.propositions.end() ||
        algebraProposition->second.argumentTypes !=
            std::vector<Sort>{Sort::Subject, Sort::AlgebraInstance})
      return fail("external algebra/SRS proposition signatures changed");

    for (const auto &[id, rule] : catalog->rules) {
      zkc::soundness::RuleWfResult result =
          zkc::soundness::checkRuleWellFormed(catalog->schemas, rule);
      if (!result.accepted())
        return fail(
            "adapted rule '" + id + "' no longer passes RULE_WF: " +
            zkc::soundness::ruleWfRefusalCodeName(result.refusal->code));
    }

    // The refuted capacity rule stays in the signature as a record and is
    // offered to nobody: it is well-formed, inspectable, and unreachable.
    auto fri = catalog->rules.find("zkc.rbr.fri.capacity");
    if (fri == catalog->rules.end())
      return fail("the refuted FRI rule is not recorded");
    if (fri->second.status != zkc::soundness::RuleStatus::Declared ||
        findBindingForRule(*catalog, "zkc.rbr.fri.capacity"))
      return fail("the refuted FRI rule is reachable");
    const auto *friBody =
        std::get_if<zkc::soundness::NativeRoundByRoundEntry>(&fri->second.body);
    if (!friBody ||
        friBody->rounds.kind != zkc::soundness::RoundSequence::Kind::Contract ||
        friBody->rounds.cases.size() != 2 ||
        friBody->rounds.cases[0].caseName != "fold" ||
        friBody->rounds.cases[1].caseName != "query")
      return fail("heterogeneous FRI round cases were not preserved");
    const zkc::soundness::QuantityTemplate &friFoldSpace =
        friBody->rounds.cases[0].challengeSpace;
    const zkc::soundness::QuantityTemplate &friQuerySpace =
        friBody->rounds.cases[1].challengeSpace;
    if (friFoldSpace.kind != zkc::soundness::QuantityKind::Parameter ||
        friFoldSpace.name != "field_order" ||
        friQuerySpace.kind != zkc::soundness::QuantityKind::Pow2 ||
        friQuerySpace.operands.size() != 1 ||
        friQuerySpace.operands[0].kind !=
            zkc::soundness::QuantityKind::Parameter ||
        friQuerySpace.operands[0].name != "n")
      return fail("FRI challenge-space expressions were reconstructed "
                  "instead of translated from the source trees");

    const std::map<std::string,
                   std::map<std::string, std::vector<std::string>, std::less<>>,
                   std::less<>>
        expectedFriConditionParameters = {
            {"zkc.rbr.fri.johnson",
             {{"S1", {"n", "k", "log_blowup", "log_final_poly_len"}},
              {"S2", {"m"}},
              {"S3", {"eta", "m", "log_blowup"}},
              {"S4", {"delta", "eta", "log_blowup"}}}},
            {"zkc.rbr.fri.udr",
             {{"S1", {"n", "k", "log_blowup", "log_final_poly_len"}},
              {"S2", {"n", "k", "log_final_poly_len"}},
              {"S3", {"theta", "n", "k"}}}},
            {"zkc.rbr.fri.johnson_linear",
             {{"S1", {"n", "k", "log_blowup", "log_final_poly_len"}},
              {"S2", {"m"}},
              {"S3", {"m", "eta", "log_blowup"}},
              {"S4", {"delta", "eta", "log_blowup"}}}},
        };
    const std::map<std::string, std::string, std::less<>> friHypothesisSlots = {
        {"zkc.rbr.fri.johnson", "S5"},
        {"zkc.rbr.fri.udr", "S4"},
        {"zkc.rbr.fri.johnson_linear", "S5"},
    };
    // The capacity rule is absent from these tables on purpose: it is
    // declared rather than admitted, so it has no binding whose argument
    // reuse could be checked.
    for (const auto &[id, expectedConditions] :
         expectedFriConditionParameters) {
      auto rule = catalog->rules.find(id);
      const zkc::soundness::RuleBinding *binding =
          findBindingForRule(*catalog, id);
      if (rule == catalog->rules.end() || !binding ||
          !hasParameter(rule->second, "fri_domain", Sort::FriDomainInstance))
        return fail("FRI rule '" + id + "' has no exact FRI-domain parameter");
      for (const auto &[slot, parameterNames] : expectedConditions) {
        const auto *arguments = conditionArguments(*binding, slot);
        if (!arguments || arguments->size() != parameterNames.size())
          return fail("FRI condition '" + id + ":" + slot +
                      "' has the wrong binding arity");
        for (size_t index = 0; index < parameterNames.size(); ++index) {
          auto parameter =
              binding->parameterBindings.find(parameterNames[index]);
          if (parameter == binding->parameterBindings.end() ||
              !sameBindingValue((*arguments)[index], parameter->second))
            return fail("FRI condition '" + id + ":" + slot +
                        "' does not reuse its exact typed parameter");
        }
      }
      auto hypothesisSlot = friHypothesisSlots.find(id);
      auto domain = binding->parameterBindings.find("fri_domain");
      const auto *hypothesis =
          hypothesisSlot == friHypothesisSlots.end()
              ? nullptr
              : hypothesisArguments(*binding, hypothesisSlot->second);
      if (domain == binding->parameterBindings.end() || !hypothesis ||
          hypothesis->size() != 2 ||
          hypothesis->front().kind !=
              zkc::soundness::BindingValueKind::ConclusionSubject ||
          !sameBindingValue((*hypothesis)[1], domain->second))
        return fail("FRI theorem hypothesis does not bind the exact subject "
                    "and FRI-domain instance");
    }

    auto sigma = catalog->rules.find("zkc.ss.sigma");
    if (sigma == catalog->rules.end())
      return fail("the sigma special-soundness entry is absent");
    const auto *sigmaBody =
        std::get_if<zkc::soundness::SpecialSoundnessEntry>(&sigma->second.body);
    if (!sigmaBody ||
        sigmaBody->coordinates.kind !=
            zkc::soundness::CoordinateSequence::Kind::Contract ||
        sigmaBody->coordinates.cases.size() != 1 ||
        !sigmaBody->coordinates.cases[0].challengeSpace ||
        sigmaBody->coordinates.cases[0].challengeSpace->kind !=
            zkc::soundness::QuantityKind::ContractRoundFact ||
        sigmaBody->coordinates.cases[0].challengeSpace->caseName !=
            "sigma_round" ||
        sigmaBody->coordinates.cases[0].challengeSpace->contractRoundField !=
            zkc::soundness::ContractRoundField::ChallengeSpace)
      return fail("the sealed sigma challenge-space source was not retained");
    const zkc::soundness::RuleBinding *sigmaBinding =
        findBindingForRule(*catalog, "zkc.ss.sigma");
    const auto *sigmaArityArguments =
        sigmaBinding ? conditionArguments(*sigmaBinding, "S1") : nullptr;
    const auto *sigmaTranscriptArguments =
        sigmaBinding ? hypothesisArguments(*sigmaBinding, "S2") : nullptr;
    auto sigmaContract =
        sigmaBinding ? sigmaBinding->factBindings.find("contract")
                     : std::map<std::string, zkc::soundness::BindingValue,
                                std::less<>>::const_iterator();
    auto sigmaAlgebra =
        sigmaBinding ? sigmaBinding->parameterBindings.find("algebra")
                     : std::map<std::string, zkc::soundness::BindingValue,
                                std::less<>>::const_iterator();
    if (!hasParameter(sigma->second, "algebra", Sort::AlgebraInstance) ||
        !sigmaBinding || sigmaContract == sigmaBinding->factBindings.end() ||
        sigmaAlgebra == sigmaBinding->parameterBindings.end() ||
        sigmaAlgebra->second.kind !=
            zkc::soundness::BindingValueKind::ResolvedParameter ||
        sigmaAlgebra->second.reference != "algebra" || !sigmaArityArguments ||
        sigmaArityArguments->size() != 2 ||
        !sameBindingValue((*sigmaArityArguments)[0], sigmaContract->second) ||
        !isIntegerLiteral((*sigmaArityArguments)[1], 2) ||
        !sigmaTranscriptArguments || sigmaTranscriptArguments->size() != 2 ||
        !sameBindingValue((*sigmaTranscriptArguments)[0],
                          sigmaContract->second) ||
        !sameBindingValue((*sigmaTranscriptArguments)[1], sigmaAlgebra->second))
      return fail("sigma did not bind its contract, arity, and algebra "
                  "instance exactly");

    auto grinding = catalog->rules.find("zkc.rbr.grinding");
    if (grinding == catalog->rules.end())
      return fail("the grinding scaling rule is absent");
    const auto *grindingBody =
        std::get_if<zkc::soundness::RoundScaling>(&grinding->second.body);
    bool hasAdjacencyFact = false;
    for (const zkc::soundness::TypedDeclaration &fact :
         grinding->second.artifactFacts) {
      hasAdjacencyFact |=
          fact.name == "pow_adjacency" &&
          fact.sort == zkc::soundness::ValueSort::RoundAdjacency;
    }
    // Exactly one fact port, because a rule declares only what its body
    // reads: the adjacency the scaled round is selected through.
    if (!grindingBody || grinding->second.artifactFacts.size() != 1 ||
        !hasAdjacencyFact ||
        grindingBody->selectedRound.kind !=
            zkc::soundness::RoundSelectorKind::AdjacentPredecessorRound ||
        grindingBody->selectedRound.adjacencyFactPort != "pow_adjacency" ||
        !grindingBody->selectedRound.exactRoundIndex.empty())
      return fail("grinding does not select its scaled round through a "
                  "typed adjacency fact");
    const zkc::soundness::QuantityTemplate &grindingScale = grindingBody->scale;
    if (grindingScale.kind != zkc::soundness::QuantityKind::Pow2 ||
        grindingScale.operands.size() != 1 ||
        grindingScale.operands[0].kind != zkc::soundness::QuantityKind::Mul ||
        grindingScale.operands[0].operands.size() != 2 ||
        !isRationalLiteral(grindingScale.operands[0].operands[0], -1) ||
        grindingScale.operands[0].operands[1].kind !=
            zkc::soundness::QuantityKind::Parameter ||
        grindingScale.operands[0].operands[1].name != "z")
      return fail("grinding did not retain its exact source scale tree");
    size_t grindingBindingCount =
        llvm::count_if(catalog->bindings, [](const auto &entry) {
          return entry.second.ruleRef.id == "zkc.rbr.grinding";
        });
    const zkc::soundness::RuleBinding *grindingBinding =
        findBindingForRule(*catalog, "zkc.rbr.grinding");
    auto grindingAdjacency =
        grindingBinding ? grindingBinding->factBindings.find("pow_adjacency")
                        : std::map<std::string, zkc::soundness::BindingValue,
                                   std::less<>>::const_iterator();
    if (grindingBindingCount != 1 || !grindingBinding ||
        grindingAdjacency == grindingBinding->factBindings.end() ||
        grindingAdjacency->second.kind !=
            zkc::soundness::BindingValueKind::SealedArtifactProjection ||
        grindingAdjacency->second.artifactProjection.kind !=
            zkc::soundness::ArtifactProjectionKind::ContractRoundAdjacency ||
        grindingAdjacency->second.sort !=
            zkc::soundness::ValueSort::RoundAdjacency)
      return fail("the grinding adjacency fact has no exact typed binding");
    const auto *grindingPinnedArguments =
        conditionArguments(*grindingBinding, "S1");
    const auto *grindingAdjacentArguments =
        conditionArguments(*grindingBinding, "S2");
    if (!grindingPinnedArguments || grindingPinnedArguments->size() != 1 ||
        !sameBindingValue(grindingPinnedArguments->front(),
                          grindingAdjacency->second) ||
        !grindingAdjacentArguments || grindingAdjacentArguments->size() != 1 ||
        !sameBindingValue(grindingAdjacentArguments->front(),
                          grindingAdjacency->second))
      return fail("grinding conditions do not consume the authenticated "
                  "adjacency fact");
    zkc::soundness::RuleBinding malformedRelation = *grindingBinding;
    malformedRelation.premiseRelations.at("source_rbr").inputIndices.clear();
    zkc::soundness::RuleWfResult malformedRelationResult =
        zkc::soundness::checkRuleBindingWellFormed(
            catalog->schemas, grinding->second, malformedRelation);
    if (malformedRelationResult.accepted() ||
        malformedRelationResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidSubjectRelation)
      return fail("binding WF accepted a malformed consumed-claim relation");

    zkc::soundness::RuleBinding unknownAnchor = *grindingBinding;
    unknownAnchor.anchor.kind =
        static_cast<zkc::soundness::ProtocolAnchorKind>(255);
    zkc::soundness::RuleWfResult unknownAnchorResult =
        zkc::soundness::checkRuleBindingWellFormed(
            catalog->schemas, grinding->second, unknownAnchor);
    if (unknownAnchorResult.accepted() ||
        unknownAnchorResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidBinding)
      return fail("binding WF accepted an unknown protocol-anchor kind");

    zkc::soundness::RuleBinding unknownRelation = *grindingBinding;
    unknownRelation.premiseRelations.at("source_rbr").kind =
        static_cast<zkc::soundness::SubjectRelationKind>(255);
    zkc::soundness::RuleWfResult unknownRelationResult =
        zkc::soundness::checkRuleBindingWellFormed(
            catalog->schemas, grinding->second, unknownRelation);
    if (unknownRelationResult.accepted() ||
        unknownRelationResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidSubjectRelation)
      return fail("binding WF accepted an unknown subject-relation kind");

    zkc::soundness::RuleBinding nonClaimConclusion = *grindingBinding;
    nonClaimConclusion.subjectSchema = "zkc.subject.consumed_claim_vector";
    zkc::soundness::RuleWfResult nonClaimConclusionResult =
        zkc::soundness::checkRuleBindingWellFormed(
            catalog->schemas, grinding->second, nonClaimConclusion);
    if (nonClaimConclusionResult.accepted() ||
        nonClaimConclusionResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidBinding)
      return fail("binding WF accepted a non-claim direct conclusion");

    zkc::soundness::SchemaContext externalSchemas = catalog->schemas;
    externalSchemas.subjectSchemas.emplace(
        "test.external.path",
        zkc::soundness::SubjectSchema{
            "test.external.path",
            {zkc::soundness::ValueSort::PathTransition},
            zkc::soundness::SubjectSchemaKind::ExternalInstance});
    zkc::soundness::SoundnessRule externalRule = grinding->second;
    externalRule.premises.front().expectedSubjectSchema = "test.external.path";
    zkc::soundness::RuleBinding crossAnchorArgument = *grindingBinding;
    zkc::soundness::BindingValue pathArgument;
    pathArgument.sort = zkc::soundness::ValueSort::PathTransition;
    pathArgument.kind =
        zkc::soundness::BindingValueKind::ApplicationPathTransition;
    crossAnchorArgument.premiseRelations.at("source_rbr") =
        zkc::soundness::SubjectRelation{
            zkc::soundness::SubjectRelationKind::ExactExternalSubject,
            zkc::soundness::ConsumedClaimSelectorKind::ReductionInput,
            {},
            "test.external.path",
            {pathArgument}};
    zkc::soundness::RuleWfResult crossAnchorArgumentResult =
        zkc::soundness::checkRuleBindingWellFormed(
            externalSchemas, externalRule, crossAnchorArgument);
    if (crossAnchorArgumentResult.accepted() ||
        crossAnchorArgumentResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidBinding)
      return fail("binding WF accepted a path value through a reduction "
                  "external-subject relation");

    auto ssToRbr = catalog->rules.find("zkc.rbr.from_ss");
    if (ssToRbr == catalog->rules.end())
      return fail("the SS-to-RBR rule is absent");
    const auto *ssToRbrBody =
        std::get_if<zkc::soundness::SpecialSoundnessToRoundByRound>(
            &ssToRbr->second.body);
    const zkc::soundness::QuantityTemplate *ssPrice =
        ssToRbrBody && ssToRbrBody->perCoordinateBound.kind ==
                           zkc::soundness::RuleBoundKind::Quantity
            ? &ssToRbrBody->perCoordinateBound.quantity
            : nullptr;
    if (!ssPrice || ssPrice->kind != zkc::soundness::QuantityKind::Div ||
        ssPrice->operands.size() != 2 ||
        ssPrice->operands[0].kind != zkc::soundness::QuantityKind::Sub ||
        ssPrice->operands[0].operands.size() != 2 ||
        ssPrice->operands[0].operands[0].kind !=
            zkc::soundness::QuantityKind::PremiseCoordinate ||
        ssPrice->operands[0].operands[0].port != "source_ss" ||
        ssPrice->operands[0].operands[0].premiseCoordinateField !=
            zkc::soundness::PremiseCoordinateField::Arity ||
        ssPrice->operands[0].operands[0].premiseCoordinateSelector.kind !=
            zkc::soundness::PremiseCoordinateSelectorKind::BoundCoordinate ||
        !isRationalLiteral(ssPrice->operands[0].operands[1], 1) ||
        ssPrice->operands[1].kind !=
            zkc::soundness::QuantityKind::PremiseCoordinate ||
        ssPrice->operands[1].port != "source_ss" ||
        ssPrice->operands[1].premiseCoordinateField !=
            zkc::soundness::PremiseCoordinateField::ChallengeSpace ||
        ssPrice->operands[1].premiseCoordinateSelector.kind !=
            zkc::soundness::PremiseCoordinateSelectorKind::BoundCoordinate)
      return fail("SS-to-RBR did not retain its exact source loss tree");

    for (llvm::StringRef id :
         {"zkc.sr.from_rbr", "zkc.sr.from_rbr_knowledge"}) {
      auto rule = catalog->rules.find(id);
      const auto *body =
          rule == catalog->rules.end()
              ? nullptr
              : std::get_if<zkc::soundness::RoundByRoundToStateRestoration>(
                    &rule->second.body);
      if (!body ||
          body->moveBudget.kind !=
              zkc::soundness::QuantityKind::ResourceVariable ||
          body->moveBudget.name != "t")
        return fail("RBR-to-SR did not retain the exact source move budget");
      const zkc::soundness::RuleBinding *binding =
          findBindingForRule(*catalog, id);
      const auto *s1 = binding ? hypothesisArguments(*binding, "S1") : nullptr;
      const auto *s2 = binding && id == "zkc.sr.from_rbr_knowledge"
                           ? hypothesisArguments(*binding, "S2")
                           : nullptr;
      if (!binding || !s1 || !s1->empty() ||
          (id == "zkc.sr.from_rbr_knowledge" && (!s2 || !s2->empty())))
        return fail("RBR-to-SR attested hypotheses are not zero-argument "
                    "propositions");
    }

    for (llvm::StringRef id : {"zkc.fs.duplex", "zkc.fs.duplex_knowledge"}) {
      auto rule = catalog->rules.find(id);
      const auto *body =
          rule == catalog->rules.end()
              ? nullptr
              : std::get_if<zkc::soundness::StateRestorationToFiatShamirDuplex>(
                    &rule->second.body);
      // Three sponge terms from the theorem, plus the collision addend
      // pricing the 216-bit anchor projection: a named game advantage
      // scaled by the artifact's bound-relation-anchor count, so it is
      // exactly zero where no relation identity enters the transcript.
      if (!body ||
          body->localDuplexBound.kind != zkc::soundness::RuleBoundKind::Add ||
          body->localDuplexBound.operands.size() != 4 ||
          boundReadsPremise(body->localDuplexBound))
        return fail("SR-to-FS did not isolate exactly the three local "
                    "duplex terms and the collision addend from its premise");
      const zkc::soundness::RuleBound &collision =
          body->localDuplexBound.operands.back();
      if (collision.kind != zkc::soundness::RuleBoundKind::Scale ||
          collision.quantity.kind != zkc::soundness::QuantityKind::Parameter ||
          collision.quantity.name != "bound_relation_anchors" ||
          collision.operands.size() != 1 ||
          collision.operands.front().kind !=
              zkc::soundness::RuleBoundKind::PrimitiveAdvantage ||
          collision.operands.front().game.gameRef !=
              "zkc.assume.sha256_216_collision")
        return fail("SR-to-FS collision addend is not the anchor-count-scaled "
                    "sha256-216 advantage");
      const zkc::soundness::RuleBinding *binding =
          findBindingForRule(*catalog, id);
      const auto *spine =
          binding ? conditionArguments(*binding, "S1") : nullptr;
      const auto *codec =
          binding ? conditionArguments(*binding, "S2") : nullptr;
      const auto *profile =
          binding ? hypothesisArguments(*binding, "S3") : nullptr;
      const auto *mapping =
          binding ? hypothesisArguments(*binding, "S4") : nullptr;
      const auto *ideal =
          binding ? hypothesisArguments(
                        *binding, "assumption:zkc.assume.ideal_permutation")
                  : nullptr;
      auto isSubject = [](const auto *arguments) {
        return arguments && arguments->size() == 1 &&
               arguments->front().kind ==
                   zkc::soundness::BindingValueKind::ConclusionSubject &&
               arguments->front().sort == Sort::Subject;
      };
      // The two decidable conditions read the sealed path transition the
      // application sits at; the three hypotheses a person must assert read
      // the subject. Nothing routes the path through a fact port, because
      // nothing in the body reads one.
      auto isPath = [](const auto *arguments) {
        return arguments && arguments->size() == 1 &&
               arguments->front().kind == zkc::soundness::BindingValueKind::
                                              ApplicationPathTransition &&
               arguments->front().sort == Sort::PathTransition;
      };
      if (!binding || !binding->factBindings.empty() || !isPath(spine) ||
          !isPath(codec) || !isSubject(profile) || !isSubject(mapping) ||
          !isSubject(ideal))
        return fail("duplex rule inputs are not split between the sealed path "
                    "and explicit subject hypotheses");
    }

    auto css = catalog->rules.find("zkc.pcs.kzg_css");
    if (css == catalog->rules.end())
      return fail("the independent KZG PCS-CSS provider did not adapt");
    bool cssHasBinding = llvm::any_of(catalog->bindings, [](const auto &entry) {
      return entry.second.ruleRef.id == "zkc.pcs.kzg_css";
    });
    if (cssHasBinding)
      return fail("the independent KZG PCS-CSS provider gained a direct "
                  "artifact binding");
    if (hasHypothesis(css->second, "zkc.assume.arsdh") ||
        !hasHypothesis(css->second, "zkc.assume.srs_ceremony"))
      return fail("quantitative and qualitative CSS assumptions were not "
                  "separated by actual Adv use");
    const auto *cssBody =
        std::get_if<zkc::soundness::ComputationalEntry>(&css->second.body);
    const auto *degrees =
        findHypothesis(css->second, "zkc.side.degrees_within_srs");
    const auto *algebra = findHypothesis(css->second, "zkc.side.algebra_match");
    const auto *ceremony =
        findHypothesis(css->second, "zkc.assume.srs_ceremony");
    const zkc::soundness::ExactParameterPin *algebraPin =
        css->second.exactParameterPins.size() == 1
            ? &css->second.exactParameterPins.front()
            : nullptr;
    const auto *exactAlgebra =
        algebraPin ? std::get_if<zkc::soundness::AlgebraInstanceValue>(
                         &algebraPin->expected.literal)
                   : nullptr;
    if (!hasParameter(css->second, "algebra", Sort::AlgebraInstance) ||
        !hasParameter(css->second, "srs", Sort::SrsInstance) || !cssBody ||
        !algebraPin || algebraPin->parameter != "algebra" ||
        algebraPin->expected.kind !=
            zkc::soundness::BindingValueKind::Literal ||
        !exactAlgebra || exactAlgebra->group != "algebra:bls12_381:g1" ||
        exactAlgebra->fieldClass != "fr" ||
        exactAlgebra->fieldOrder.str() !=
            "524358751751261904794477405081859658376905525005276378226036586999"
            "38581184513" ||
        cssBody->failureBound.kind !=
            zkc::soundness::RuleBoundKind::PrimitiveAdvantage ||
        cssBody->failureBound.game.instanceArguments.size() != 2 ||
        cssBody->failureBound.game.instanceArguments[0].sort !=
            Sort::AlgebraInstance ||
        cssBody->failureBound.game.instanceArguments[0].kind !=
            zkc::soundness::BindingValueKind::ResolvedParameter ||
        cssBody->failureBound.game.instanceArguments[0].reference !=
            "algebra" ||
        cssBody->failureBound.game.instanceArguments[1].sort != Sort::Integer ||
        cssBody->failureBound.game.instanceArguments[1].kind !=
            zkc::soundness::BindingValueKind::ResolvedParameter ||
        cssBody->failureBound.game.instanceArguments[1].reference !=
            "srs_max_degree" ||
        !degrees ||
        degrees->argumentTypes != std::vector<Sort>{Sort::Subject,
                                                    Sort::SrsInstance,
                                                    Sort::Integer} ||
        !algebra ||
        algebra->argumentTypes !=
            std::vector<Sort>{Sort::Subject, Sort::AlgebraInstance} ||
        !ceremony ||
        ceremony->argumentTypes != std::vector<Sort>{Sort::SrsInstance})
      return fail("KZG CSS does not expose exact algebra, SRS, degree, and "
                  "primitive-game inputs");

    auto fs = catalog->rules.find("zkc.fs.duplex");
    if (fs == catalog->rules.end() ||
        !hasHypothesis(fs->second, "zkc.assume.ideal_permutation"))
      return fail("the non-Adv ideal-permutation assumption was dropped");

    const zkc::soundness::RuleBinding *sumcheckBinding =
        findBindingForRule(*catalog, "zkc.rbr.sumcheck");
    if (!sumcheckBinding)
      return fail("the sumcheck rule has no reduction binding");
    // The field's order is not an artifact fact: the sealed protocol
    // authenticates the payload class and each round's declared challenge
    // space, and nothing in it records the order. The parameter is therefore
    // supplied by the caller and its correspondence to the artifact is a
    // stated hypothesis, exactly as the KZG rules treat their algebra and SRS.
    auto fieldOrder = sumcheckBinding->parameterBindings.find("field_order");
    auto fieldClass = sumcheckBinding->parameterBindings.find("field_class");
    using Kind = zkc::soundness::BindingValueKind;
    if (fieldOrder == sumcheckBinding->parameterBindings.end() ||
        fieldOrder->second.kind != Kind::ResolvedParameter ||
        fieldOrder->second.sort != zkc::soundness::ValueSort::Integer ||
        fieldOrder->second.reference != "field_order" ||
        fieldClass == sumcheckBinding->parameterBindings.end() ||
        fieldClass->second.kind != Kind::ResolvedParameter ||
        fieldClass->second.sort != zkc::soundness::ValueSort::String ||
        fieldClass->second.reference != "field_class")
      return fail("field parameters are not caller-supplied");
    const auto *orderCondition = conditionArguments(*sumcheckBinding, "S2");
    if (!orderCondition || orderCondition->size() != 2 ||
        !((*orderCondition)[1] == fieldOrder->second))
      return fail("the embedding condition does not read the declared field "
                  "order");
    auto sumcheck = catalog->rules.find("zkc.rbr.sumcheck");
    if (sumcheck == catalog->rules.end() ||
        !hasHypothesis(sumcheck->second, "zkc.side.field_order_match"))
      return fail("the field order is supplied without a stated "
                  "correspondence to the artifact");
    auto sumcheckContract = sumcheckBinding->factBindings.find("contract");
    const auto *sumcheckS1 = conditionArguments(*sumcheckBinding, "S1");
    const auto *sumcheckS2 = conditionArguments(*sumcheckBinding, "S2");
    const auto *sumcheckS3 = conditionArguments(*sumcheckBinding, "S3");
    const auto *sumcheckS4 = conditionArguments(*sumcheckBinding, "S4");
    if (sumcheckContract == sumcheckBinding->factBindings.end() ||
        !sumcheckS1 || sumcheckS1->size() != 1 ||
        !sameBindingValue(sumcheckS1->front(), sumcheckContract->second) ||
        !sumcheckS2 || sumcheckS2->size() != 2 ||
        !sameBindingValue((*sumcheckS2)[0], sumcheckContract->second) ||
        !sameBindingValue((*sumcheckS2)[1], fieldOrder->second) ||
        !sumcheckS3 || sumcheckS3->size() != 1 ||
        !sameBindingValue(sumcheckS3->front(), sumcheckContract->second) ||
        !sumcheckS4 || sumcheckS4->size() != 2 ||
        !sameBindingValue((*sumcheckS4)[0], sumcheckContract->second) ||
        !sameBindingValue((*sumcheckS4)[1], fieldClass->second))
      return fail("sumcheck conditions do not consume the exact contract and "
                  "typed parameters");

    size_t preservationRules =
        llvm::count_if(preservationRuleIds, [&](const std::string &id) {
          return catalog->rules.count(id) == 1;
        });
    if (preservationRules != 2)
      return fail("the two KZG preservation rules are not both declared");

    // A literal that is not an exact value of its declared sort must refuse at
    // the exact slot it appears in, not be coerced.
    llvm::Error invalidConstant = loadMutatedSignature(
        signaturePath, "invalid-constant-signature",
        [](llvm::json::Object &root) -> llvm::Error {
          llvm::json::Object *binding =
              section(root, "bindings", "zkc.ss.sigma@reduction:sigma");
          llvm::json::Object *conditions =
              binding ? binding->getObject("condition_argument_bindings")
                      : nullptr;
          llvm::json::Array *arity =
              conditions ? conditions->getArray("S1") : nullptr;
          llvm::json::Object *value =
              arity && arity->size() == 2 ? (*arity)[1].getAsObject() : nullptr;
          if (!value)
            return llvm::createStringError(
                "the sigma arity argument is absent in the mutation fixture");
          (*value)["literal"] = "not-an-integer";
          return llvm::Error::success();
        });
    std::string invalidConstantRefusal =
        llvm::toString(std::move(invalidConstant));
    if (invalidConstantRefusal.find("exact decimal rational") ==
        std::string::npos)
      return fail("an invalid typed constant did not refuse at its condition "
                  "argument: " +
                  invalidConstantRefusal);

    // The signature may only name machine deciders this build implements.
    // Reading a decider kind the binary does not have would widen the trusted
    // computing base by editing a file.
    llvm::Error unknownDecider = loadMutatedSignature(
        signaturePath, "unknown-decider-signature",
        [](llvm::json::Object &root) -> llvm::Error {
          llvm::json::Object *schemas = root.getObject("schemas");
          llvm::json::Object *decider =
              schemas ? section(*schemas, "machine_deciders",
                                "zkc.side.pow_adjacent")
                      : nullptr;
          if (!decider)
            return llvm::createStringError(
                "the adjacency decider is absent in the mutation fixture");
          (*decider)["kind"] = "pow_adjacent_but_weaker";
          return llvm::Error::success();
        });
    std::string unknownDeciderRefusal =
        llvm::toString(std::move(unknownDecider));
    if (unknownDeciderRefusal.find("unknown value") == std::string::npos)
      return fail("a machine decider this build does not implement was "
                  "admitted: " +
                  unknownDeciderRefusal);

    // Every declaration is read against a closed field set at every depth: a
    // reader that skipped what it did not understand would silently accept a
    // signature written against a different language.
    llvm::Error unknownField = loadMutatedSignature(
        signaturePath, "unknown-field-signature",
        [](llvm::json::Object &root) -> llvm::Error {
          llvm::json::Object *rule = section(root, "rules", "zkc.pcs.kzg_css");
          if (!rule)
            return llvm::createStringError(
                "the CSS rule is absent in the mutation fixture");
          (*rule)["regime"] = "comp";
          return llvm::Error::success();
        });
    std::string unknownFieldRefusal = llvm::toString(std::move(unknownField));
    if (unknownFieldRefusal.find("unknown field 'regime'") == std::string::npos)
      return fail("an unknown declaration field was admitted: " +
                  unknownFieldRefusal);

    // A receipt's axiom profile and its recorded state are two spellings of
    // the same fact, so they may not disagree.
    llvm::Error overclaimedReceipt = loadMutatedSignature(
        signaturePath, "overclaimed-receipt-signature",
        [](llvm::json::Object &root) -> llvm::Error {
          llvm::json::Object *annotation =
              section(root, "annotations", "zkc.rbr.sumcheck");
          llvm::json::Array *receipts =
              annotation ? annotation->getArray("formalization") : nullptr;
          llvm::json::Object *receipt = receipts && !receipts->empty()
                                            ? receipts->front().getAsObject()
                                            : nullptr;
          if (!receipt)
            return llvm::createStringError(
                "the sumcheck receipt is absent in the mutation fixture");
          (*receipt)["state"] = "mechanized";
          return llvm::Error::success();
        });
    std::string overclaimedRefusal =
        llvm::toString(std::move(overclaimedReceipt));
    if (overclaimedRefusal.find("axiom profile says the opposite") ==
        std::string::npos)
      return fail("a receipt claiming more than its axiom profile allows was "
                  "admitted: " +
                  overclaimedRefusal);

    // The unmatched list is about a specific rule, so a slot that rule does not
    // declare is a claim about coverage that has fallen out of step with it.
    llvm::Error strayObligation = loadMutatedSignature(
        signaturePath, "stray-obligation-signature",
        [](llvm::json::Object &root) -> llvm::Error {
          llvm::json::Object *annotation =
              section(root, "annotations", "zkc.rbr.sumcheck");
          llvm::json::Array *receipts =
              annotation ? annotation->getArray("formalization") : nullptr;
          llvm::json::Object *receipt = receipts && !receipts->empty()
                                            ? receipts->front().getAsObject()
                                            : nullptr;
          llvm::json::Array *unmatched =
              receipt ? receipt->getArray("unmatched_obligations") : nullptr;
          if (!unmatched)
            return llvm::createStringError(
                "the sumcheck receipt has no unmatched-obligation list");
          unmatched->push_back("S9");
          return llvm::Error::success();
        });
    std::string strayRefusal = llvm::toString(std::move(strayObligation));
    if (strayRefusal.find("which the rule does not declare") ==
        std::string::npos)
      return fail("a receipt named an obligation its rule does not declare: " +
                  strayRefusal);

    // No binding may reach a declared rule. The refuted capacity rule is the
    // live instance, so pointing a binding at it must refuse.
    llvm::Error bindsDeclared = loadMutatedSignature(
        signaturePath, "binds-declared-rule-signature",
        [](llvm::json::Object &root) -> llvm::Error {
          llvm::json::Object *binding =
              section(root, "bindings", "zkc.rbr.fri.johnson@reduction:fri");
          if (!binding)
            return llvm::createStringError(
                "the Johnson FRI binding is absent in the mutation fixture");
          (*binding)["rule"] = "zkc.rbr.fri.capacity";
          return llvm::Error::success();
        });
    std::string bindsDeclaredRefusal = llvm::toString(std::move(bindsDeclared));
    if (bindsDeclaredRefusal.find("declared, so no binding may reach it") ==
        std::string::npos)
      return fail("a binding reached a declared rule: " + bindsDeclaredRefusal);

    zkc::soundness::SoundnessRule malformed = fri->second;
    malformed.conclusionIndex.index.notion =
        zkc::soundness::SecurityNotion::FiatShamir;
    malformed.conclusionIndex.index.model = "duplex";
    zkc::soundness::RuleWfResult malformedResult =
        zkc::soundness::checkRuleWellFormed(catalog->schemas, malformed);
    if (malformedResult.accepted() ||
        malformedResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidBodySignature)
      return fail("RULE_WF accepted an exact body/index mismatch");

    zkc::soundness::SchemaContext unknownTrackSchemas = catalog->schemas;
    zkc::soundness::SoundnessRule unknownTrack = fri->second;
    unknownTrack.conclusionIndex.index.track =
        static_cast<zkc::soundness::SecurityTrack>(255);
    unknownTrackSchemas.securityIndices.push_back(
        unknownTrack.conclusionIndex.index);
    zkc::soundness::RuleWfResult unknownTrackResult =
        zkc::soundness::checkRuleWellFormed(unknownTrackSchemas, unknownTrack);
    if (unknownTrackResult.accepted() ||
        unknownTrackResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidIndex)
      return fail("RULE_WF admitted an unknown security track");

    zkc::soundness::SoundnessRule unknownBound = css->second;
    auto &unknownBoundBody =
        std::get<zkc::soundness::ComputationalEntry>(unknownBound.body);
    unknownBoundBody.failureBound.kind =
        static_cast<zkc::soundness::RuleBoundKind>(255);
    zkc::soundness::RuleWfResult unknownBoundResult =
        zkc::soundness::checkRuleWellFormed(catalog->schemas, unknownBound);
    if (unknownBoundResult.accepted() ||
        unknownBoundResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidBound)
      return fail("RULE_WF admitted an unknown rule-bound kind");

    zkc::soundness::SoundnessRule nonLiteralPin = css->second;
    nonLiteralPin.exactParameterPins.front().expected.kind =
        zkc::soundness::BindingValueKind::ResolvedParameter;
    nonLiteralPin.exactParameterPins.front().expected.reference = "algebra";
    zkc::soundness::RuleWfResult nonLiteralPinResult =
        zkc::soundness::checkRuleWellFormed(catalog->schemas, nonLiteralPin);
    if (nonLiteralPinResult.accepted() ||
        nonLiteralPinResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidReference)
      return fail("RULE_WF admitted a nonliteral exact parameter pin");

    zkc::soundness::SoundnessRule duplicatePin = css->second;
    duplicatePin.exactParameterPins.push_back(
        duplicatePin.exactParameterPins.front());
    zkc::soundness::RuleWfResult duplicatePinResult =
        zkc::soundness::checkRuleWellFormed(catalog->schemas, duplicatePin);
    if (duplicatePinResult.accepted() ||
        duplicatePinResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::DuplicateDeclaration)
      return fail("RULE_WF admitted duplicate exact parameter pins");

    zkc::soundness::SoundnessRule unknownRoundSequence = fri->second;
    auto &unknownRoundBody = std::get<zkc::soundness::NativeRoundByRoundEntry>(
        unknownRoundSequence.body);
    unknownRoundBody.rounds.kind =
        static_cast<zkc::soundness::RoundSequence::Kind>(255);
    zkc::soundness::RuleWfResult unknownRoundSequenceResult =
        zkc::soundness::checkRuleWellFormed(catalog->schemas,
                                            unknownRoundSequence);
    if (unknownRoundSequenceResult.accepted() ||
        unknownRoundSequenceResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidSequence)
      return fail("RULE_WF admitted an unknown round-sequence kind");

    zkc::soundness::SoundnessRule unknownCoordinateSequence = sigma->second;
    auto &unknownCoordinateBody =
        std::get<zkc::soundness::SpecialSoundnessEntry>(
            unknownCoordinateSequence.body);
    unknownCoordinateBody.coordinates.kind =
        static_cast<zkc::soundness::CoordinateSequence::Kind>(255);
    zkc::soundness::RuleWfResult unknownCoordinateSequenceResult =
        zkc::soundness::checkRuleWellFormed(catalog->schemas,
                                            unknownCoordinateSequence);
    if (unknownCoordinateSequenceResult.accepted() ||
        unknownCoordinateSequenceResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidSequence)
      return fail("RULE_WF admitted an unknown coordinate-sequence kind");

    zkc::soundness::SoundnessRule nonNumericRuleResource = fri->second;
    nonNumericRuleResource.resources.push_back({"label", Sort::String});
    zkc::soundness::RuleWfResult nonNumericRuleResourceResult =
        zkc::soundness::checkRuleWellFormed(catalog->schemas,
                                            nonNumericRuleResource);
    if (nonNumericRuleResourceResult.accepted() ||
        nonNumericRuleResourceResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidReference)
      return fail("RULE_WF admitted a non-numeric rule resource");

    zkc::soundness::SoundnessRule nonNumericPremiseResource = grinding->second;
    nonNumericPremiseResource.premises.front().expectedResources.push_back(
        {"label", Sort::String});
    nonNumericPremiseResource.premises.front().resourceSubstitution.emplace(
        "label", zkc::soundness::QuantityTemplate::rational(
                     zkc::registry::Rational::fromInteger(0)));
    zkc::soundness::RuleWfResult nonNumericPremiseResourceResult =
        zkc::soundness::checkRuleWellFormed(catalog->schemas,
                                            nonNumericPremiseResource);
    if (nonNumericPremiseResourceResult.accepted() ||
        nonNumericPremiseResourceResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidReference)
      return fail("RULE_WF admitted a non-numeric premise resource");

    const std::string cssGameRef = cssBody->failureBound.game.gameRef;
    if (cssGameRef.empty())
      return fail("the CSS rule has no primitive-game reference");
    zkc::soundness::SchemaContext emptyGameResourceSchemas = catalog->schemas;
    emptyGameResourceSchemas.primitiveGames.at(cssGameRef).resources.clear();
    zkc::soundness::SoundnessRule emptyGameResourceRule = css->second;
    std::get<zkc::soundness::ComputationalEntry>(emptyGameResourceRule.body)
        .failureBound.gameResourceSubstitution.clear();
    zkc::soundness::RuleWfResult emptyGameResourceResult =
        zkc::soundness::checkRuleWellFormed(emptyGameResourceSchemas,
                                            emptyGameResourceRule);
    if (!emptyGameResourceResult.accepted())
      return fail("RULE_WF refused a valid resource-free primitive game");

    zkc::soundness::SchemaContext duplicateGameResourceSchemas =
        catalog->schemas;
    duplicateGameResourceSchemas.primitiveGames.at(cssGameRef)
        .resources.push_back({"tau", Sort::Integer});
    zkc::soundness::RuleWfResult duplicateGameResourceResult =
        zkc::soundness::checkRuleWellFormed(duplicateGameResourceSchemas,
                                            css->second);
    if (duplicateGameResourceResult.accepted() ||
        duplicateGameResourceResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidPrimitiveGame)
      return fail("RULE_WF admitted duplicate primitive-game resources");

    zkc::soundness::SchemaContext nonNumericGameResourceSchemas =
        catalog->schemas;
    nonNumericGameResourceSchemas.primitiveGames.at(cssGameRef)
        .resources.front()
        .sort = Sort::String;
    zkc::soundness::RuleWfResult nonNumericGameResourceResult =
        zkc::soundness::checkRuleWellFormed(nonNumericGameResourceSchemas,
                                            css->second);
    if (nonNumericGameResourceResult.accepted() ||
        nonNumericGameResourceResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidPrimitiveGame)
      return fail("RULE_WF admitted a non-numeric primitive-game resource");

    auto resolvedSemanticValue = [](Sort sort, llvm::StringRef parameter) {
      zkc::soundness::BindingValue value;
      value.kind = zkc::soundness::BindingValueKind::ResolvedParameter;
      value.sort = sort;
      value.reference = parameter.str();
      return value;
    };

    auto sumcheckRule = catalog->rules.find("zkc.rbr.sumcheck");
    if (sumcheckRule == catalog->rules.end())
      return fail("the sumcheck rule disappeared before provenance tests");
    zkc::soundness::SoundnessRule forgedContractRule = sumcheckRule->second;
    forgedContractRule.parameters.push_back(
        {"forged_contract", Sort::ReductionContract});
    zkc::soundness::RuleBinding forgedContractBinding = *sumcheckBinding;
    forgedContractBinding.parameterBindings.emplace("forged_contract",
                                                    sumcheckContract->second);
    forgedContractBinding.factBindings.at("contract") =
        resolvedSemanticValue(Sort::ReductionContract, "forged_contract");
    zkc::soundness::RuleWfResult forgedContractResult =
        zkc::soundness::checkRuleBindingWellFormed(
            catalog->schemas, forgedContractRule, forgedContractBinding);
    if (forgedContractResult.accepted() ||
        forgedContractResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidReference)
      return fail("binding WF admitted a parameter-derived reduction contract");

    zkc::soundness::SoundnessRule forgedAdjacencyRule = grinding->second;
    forgedAdjacencyRule.parameters.push_back(
        {"forged_adjacency", Sort::RoundAdjacency});
    zkc::soundness::RuleBinding forgedAdjacencyBinding = *grindingBinding;
    forgedAdjacencyBinding.parameterBindings.emplace("forged_adjacency",
                                                     grindingAdjacency->second);
    forgedAdjacencyBinding.factBindings.at("pow_adjacency") =
        resolvedSemanticValue(Sort::RoundAdjacency, "forged_adjacency");
    zkc::soundness::RuleWfResult forgedAdjacencyResult =
        zkc::soundness::checkRuleBindingWellFormed(
            catalog->schemas, forgedAdjacencyRule, forgedAdjacencyBinding);
    if (forgedAdjacencyResult.accepted() ||
        forgedAdjacencyResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidReference)
      return fail("binding WF admitted parameter-derived round adjacency");

    auto fsRule = catalog->rules.find("zkc.fs.duplex");
    const zkc::soundness::RuleBinding *fsBinding =
        findBindingForRule(*catalog, "zkc.fs.duplex");
    if (fsRule == catalog->rules.end() || !fsBinding)
      return fail("the duplex rule or binding disappeared");
    // A path transition is the occurrence the application sits at, so it may
    // only ever be the selected one. Substituting a caller-supplied parameter
    // of the same sort must refuse wherever a path transition is read.
    auto fsSpine = fsBinding->conditionArgumentBindings.find("S1");
    if (fsSpine == fsBinding->conditionArgumentBindings.end() ||
        fsSpine->second.size() != 1)
      return fail("the duplex binding does not read the sealed path");
    zkc::soundness::SoundnessRule forgedPathRule = fsRule->second;
    forgedPathRule.parameters.push_back({"forged_path", Sort::PathTransition});
    zkc::soundness::RuleBinding forgedPathBinding = *fsBinding;
    forgedPathBinding.parameterBindings.emplace("forged_path",
                                                fsSpine->second.front());
    forgedPathBinding.conditionArgumentBindings.at("S1").front() =
        resolvedSemanticValue(Sort::PathTransition, "forged_path");
    zkc::soundness::RuleWfResult forgedPathResult =
        zkc::soundness::checkRuleBindingWellFormed(
            catalog->schemas, forgedPathRule, forgedPathBinding);
    if (forgedPathResult.accepted() ||
        forgedPathResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidReference)
      return fail("binding WF admitted a parameter-derived path transition");

    zkc::soundness::RuleBinding unknownPathField = *fsBinding;
    unknownPathField.parameterBindings.at("alphabet_order")
        .artifactProjection.field = "sponge.width";
    zkc::soundness::RuleWfResult unknownPathFieldResult =
        zkc::soundness::checkRuleBindingWellFormed(
            catalog->schemas, fsRule->second, unknownPathField);
    if (unknownPathFieldResult.accepted() ||
        unknownPathFieldResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidReference)
      return fail("binding WF admitted an unknown path-binding field");

    zkc::soundness::RuleBinding illTypedPathField = *fsBinding;
    illTypedPathField.parameterBindings.at("codec_bias_max")
        .artifactProjection.field = "sponge.rate";
    zkc::soundness::RuleWfResult illTypedPathFieldResult =
        zkc::soundness::checkRuleBindingWellFormed(
            catalog->schemas, fsRule->second, illTypedPathField);
    if (illTypedPathFieldResult.accepted() ||
        illTypedPathFieldResult.refusal->code !=
            zkc::soundness::RuleWfRefusalCode::InvalidReference)
      return fail("binding WF admitted an ill-typed path-binding field");

    // The index variable, both halves. Matching shares one binding
    // across a rule's premises — the second occurrence is a constraint,
    // not a rebinding — and instantiation substitutes the bound value
    // into a conclusion that restates the variable.
    {
      zkc::soundness::SecurityIndexPattern pattern;
      pattern.index.notion = zkc::soundness::SecurityNotion::RoundByRound;
      pattern.index.variant = "standard";
      pattern.quantificationVariable = "$q";
      zkc::soundness::SecurityIndex staticIndex = pattern.index;
      zkc::soundness::SecurityIndex adaptiveIndex = pattern.index;
      adaptiveIndex.quantification =
          zkc::soundness::SecurityQuantification::AdaptiveInstance;
      std::optional<zkc::soundness::SecurityQuantification> binding;
      if (!zkc::soundness::matchSecurityIndex(pattern, adaptiveIndex, binding))
        return fail("a variable pattern refused the index it should bind");
      if (zkc::soundness::matchSecurityIndex(pattern, staticIndex, binding))
        return fail("a second premise rebound the variable instead of "
                    "constraining it");
      if (zkc::soundness::instantiateSecurityIndex(pattern, *binding) !=
          adaptiveIndex)
        return fail("instantiation did not substitute the bound value");
      zkc::soundness::SecurityIndexPattern literal;
      literal.index = staticIndex;
      if (zkc::soundness::instantiateSecurityIndex(literal, *binding) !=
          staticIndex)
        return fail("instantiation rewrote a literal pattern");
    }

    // A conclusion's variable restates what a premise bound; a rule
    // whose premises never name it concludes nothing at all.
    {
      auto sigma = catalog->rules.find("zkc.ss.sigma");
      if (sigma == catalog->rules.end())
        return fail("the sigma entry rule is missing");
      zkc::soundness::SoundnessRule unbound = sigma->second;
      unbound.conclusionIndex.quantificationVariable = "$q";
      zkc::soundness::RuleWfResult unboundResult =
          zkc::soundness::checkRuleWellFormed(catalog->schemas, unbound);
      if (unboundResult.accepted() ||
          unboundResult.refusal->code !=
              zkc::soundness::RuleWfRefusalCode::InvalidIndex)
        return fail("rule WF admitted a conclusion variable no premise binds");
    }

    llvm::outs() << "soundness kernel declaration slice: PASS\n";
    llvm::outs() << "rules: " << declaredRules << " declared, " << admittedRules
                 << " admitted\n";
    llvm::outs() << "reduction bindings: " << reductionBindings << "\n";
    llvm::outs() << "path bindings: " << pathBindings << "\n";
    llvm::outs() << "zero-binding rules: " << zeroBindingRules << "\n";
    llvm::outs() << "heterogeneous FRI cases: fold, query\n";
    llvm::outs() << "refuted theorem remains declared: yes\n";
    llvm::outs() << "executable KZG preservation rules: " << preservationRules
                 << "\n";
    llvm::outs() << "body/index mutation refused: "
                 << zkc::soundness::ruleWfRefusalCodeName(
                        malformedResult.refusal->code)
                 << "\n";
    llvm::outs() << "loss trees: exact\n";
    llvm::outs() << "invalid typed constant refused: yes\n";
    llvm::outs() << "unimplemented machine decider refused: yes\n";
    llvm::outs() << "unknown declaration field refused: yes\n";
    llvm::outs() << "binding to a declared rule refused: yes\n";
    llvm::outs() << "subject-relation mutation refused: "
                 << zkc::soundness::ruleWfRefusalCodeName(
                        malformedRelationResult.refusal->code)
                 << "\n";
    llvm::outs() << "declarations carry their own content digests\n";
    llvm::outs() << "receipt overclaim refused: yes\n";
    llvm::outs() << "stray unmatched obligation refused: yes\n";
    llvm::outs() << "index variable binds once and instantiates: yes\n";
    llvm::outs() << "unbound conclusion variable refused: yes\n";
    auto digest = zkc::soundness::signatureDigest(*catalog);
    if (!digest)
      return fail(llvm::toString(digest.takeError()));
    llvm::outs() << "signature digest: " << *digest << "\n";
  }
};

} // namespace

namespace zkc::test {
void registerTestSoundnessKernelPass() {
  PassRegistration<TestSoundnessKernelPass>();
}
} // namespace zkc::test
