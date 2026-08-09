//===- SoundnessEvaluator.cpp - Executable soundness judgments ----------===//
#include "zkc/Soundness/SoundnessEvaluator.h"

#include "zkc/Soundness/SoundnessProjection.h"
#include "llvm/Support/Error.h"

#include <algorithm>
#include <cstdint>
#include <limits>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

namespace zkc::soundness {

SoundnessContext::SoundnessContext(
    const SoundnessCatalog &catalog, std::vector<ExactRef> selectedBindingRefs,
    ResolvedParameterEnvironments resolvedParameters)
    : catalog_(catalog), selectedBindingRefs_(std::move(selectedBindingRefs)),
      resolvedParameters_(std::move(resolvedParameters)) {}

const SoundnessRule *SoundnessContext::findRule(const ExactRef &ref) const {
  auto rule = catalog_.rules.find(ref.id);
  if (rule == catalog_.rules.end() || rule->second.ref != ref)
    return nullptr;
  for (const ExactRef &bindingRef : selectedBindingRefs_) {
    const RuleBinding *binding = findBinding(bindingRef);
    if (binding && binding->ruleRef == ref)
      return &rule->second;
  }
  return nullptr;
}

const RuleBinding *SoundnessContext::findBinding(const ExactRef &ref) const {
  auto selected =
      std::find(selectedBindingRefs_.begin(), selectedBindingRefs_.end(), ref);
  if (selected == selectedBindingRefs_.end())
    return nullptr;
  auto binding = catalog_.bindings.find(ref.id);
  if (binding == catalog_.bindings.end() || binding->second.ref != ref)
    return nullptr;
  return &binding->second;
}

const ResolvedParameterEnvironment *
SoundnessContext::findResolvedParameters(const ExactRef &bindingRef) const {
  if (!findBinding(bindingRef))
    return nullptr;
  auto environment = resolvedParameters_.find(bindingRef.id);
  if (environment == resolvedParameters_.end() ||
      environment->second.bindingRef != bindingRef)
    return nullptr;
  return &environment->second;
}

namespace {

constexpr int64_t kMaxExactExponent = 4096;
constexpr const char *kProtocolClaimSchema = "zkc.subject.protocol_claim";
constexpr const char *kConsumedClaimVectorSchema =
    "zkc.subject.consumed_claim_vector";

bool isInteger(const registry::Rational &value) {
  return value.denStr() == "1";
}

bool isPositive(const registry::Rational &value) {
  return value.compare(registry::Rational::fromInteger(0)) > 0;
}

bool isNonnegative(const registry::Rational &value) {
  return !value.isNegative();
}

bool validRef(const ExactRef &ref) {
  return !ref.id.empty() && !ref.sourceRevision.empty();
}

SoundnessRefusal makeRefusal(RuntimePhase phase, RuntimeRefusalCode code,
                             std::string location, std::string detail) {
  return {phase, code, std::move(location), std::move(detail)};
}

RuntimeCheckResult refuseCheck(RuntimePhase phase, RuntimeRefusalCode code,
                               std::string location, std::string detail) {
  return {makeRefusal(phase, code, std::move(location), std::move(detail))};
}

template <typename T> struct Step {
  std::optional<T> value;
  std::optional<SoundnessRefusal> refusal;

  bool accepted() const { return value.has_value() && !refusal.has_value(); }
};

template <typename T>
Step<T> refuse(RuntimePhase phase, RuntimeRefusalCode code,
               std::string location, std::string detail) {
  return {std::nullopt,
          makeRefusal(phase, code, std::move(location), std::move(detail))};
}

template <typename T> Step<T> accept(T value) {
  return {std::move(value), std::nullopt};
}

template <typename T>
Step<T> projectionFailure(llvm::Error error, RuntimePhase phase,
                          RuntimeRefusalCode code, std::string location) {
  return refuse<T>(phase, code, std::move(location),
                   llvm::toString(std::move(error)));
}

bool declarationsEqual(const std::vector<TypedDeclaration> &lhs,
                       const std::vector<TypedDeclaration> &rhs) {
  if (lhs.size() != rhs.size())
    return false;
  for (size_t index = 0; index < lhs.size(); ++index)
    if (lhs[index].name != rhs[index].name ||
        lhs[index].sort != rhs[index].sort)
      return false;
  return true;
}

std::string subjectSchemaOf(const SecuritySubject &subject) {
  if (std::holds_alternative<ProtocolClaimSubject>(subject.payload))
    return kProtocolClaimSchema;
  if (std::holds_alternative<ConsumedClaimVectorSubject>(subject.payload))
    return kConsumedClaimVectorSchema;
  return std::get<ExternalInstanceSubject>(subject.payload).schemaRef;
}

struct SemanticValue {
  ValueSort sort = ValueSort::String;
  std::variant<RuntimeValue, ClosedQuantity> payload = RuntimeValue::text("");
};

SemanticValue runtimeSemantic(RuntimeValue value) {
  return {value.sort, std::move(value)};
}

SemanticValue quantitySemantic(ValueSort sort, ClosedQuantity value) {
  return {sort, std::move(value)};
}

ClosedQuantity groundQuantity(registry::Rational value) {
  ClosedQuantity result;
  result.constant = std::move(value);
  return result;
}

std::optional<ClosedQuantity> numericQuantity(const SemanticValue &value) {
  if (value.sort != ValueSort::Integer && value.sort != ValueSort::Rational)
    return std::nullopt;
  if (const auto *quantity = std::get_if<ClosedQuantity>(&value.payload))
    return *quantity;
  const RuntimeValue &runtime = std::get<RuntimeValue>(value.payload);
  const auto *number = std::get_if<registry::Rational>(&runtime.payload);
  if (!number)
    return std::nullopt;
  return groundQuantity(*number);
}

bool semanticEqual(const SemanticValue &lhs, const SemanticValue &rhs) {
  if (lhs.sort != rhs.sort)
    return false;
  if (lhs.sort == ValueSort::Integer || lhs.sort == ValueSort::Rational) {
    std::optional<ClosedQuantity> left = numericQuantity(lhs);
    std::optional<ClosedQuantity> right = numericQuantity(rhs);
    return left && right && *left == *right;
  }
  const auto *left = std::get_if<RuntimeValue>(&lhs.payload);
  const auto *right = std::get_if<RuntimeValue>(&rhs.payload);
  return left && right && *left == *right;
}

Step<RuntimeValue> requireRuntimeValue(const SemanticValue &value,
                                       const std::string &location) {
  if (const auto *runtime = std::get_if<RuntimeValue>(&value.payload))
    return accept(*runtime);
  std::optional<ClosedQuantity> quantity = numericQuantity(value);
  if (!quantity || !quantity->resourceTerms.empty())
    return refuse<RuntimeValue>(
        RuntimePhase::BindingResolution,
        RuntimeRefusalCode::UnsupportedNormalForm, location,
        "a symbolic conclusion resource cannot close a typed runtime value");
  if (value.sort == ValueSort::Integer && !isInteger(quantity->constant))
    return refuse<RuntimeValue>(
        RuntimePhase::BindingResolution, RuntimeRefusalCode::SortMismatch,
        location, "integer runtime value resolved to a fractional quantity");
  return accept(value.sort == ValueSort::Integer
                    ? RuntimeValue::integer(quantity->constant)
                    : RuntimeValue::rational(quantity->constant));
}

struct EvaluationEnvironment {
  std::map<std::string, SemanticValue, std::less<>> parameters;
  std::map<std::string, SemanticValue, std::less<>> facts;
  std::map<std::string, const SecurityJudgment *, std::less<>> premises;
  std::map<std::string, ValueSort, std::less<>> resources;
  const ReductionContractRoundValue *currentRound = nullptr;
  std::string currentRoundCase;
  const ExtractionCoordinate *currentCoordinate = nullptr;
};

struct ApplicationEnvironment {
  const SoundnessContext &context;
  const SealedSoundnessView &sealed;
  const ApplicationSite &site;
  const SoundnessRule &rule;
  const RuleBinding &binding;
  SecuritySubject conclusionSubject;
  EvaluationEnvironment evaluation;
};

Step<SemanticValue> literalValue(const BindingValue &bindingValue,
                                 const std::string &location) {
  switch (bindingValue.sort) {
  case ValueSort::Integer:
  case ValueSort::Rational: {
    const auto *number = std::get_if<registry::Rational>(&bindingValue.literal);
    if (!number ||
        (bindingValue.sort == ValueSort::Integer && !isInteger(*number)))
      return refuse<SemanticValue>(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::SortMismatch,
          location, "numeric literal has the wrong exact carrier");
    return accept(runtimeSemantic(bindingValue.sort == ValueSort::Integer
                                      ? RuntimeValue::integer(*number)
                                      : RuntimeValue::rational(*number)));
  }
  case ValueSort::String: {
    const auto *text = std::get_if<std::string>(&bindingValue.literal);
    if (!text)
      return refuse<SemanticValue>(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::SortMismatch,
          location, "string literal has the wrong exact carrier");
    return accept(runtimeSemantic(RuntimeValue::text(*text)));
  }
  case ValueSort::Boolean: {
    const auto *boolean = std::get_if<bool>(&bindingValue.literal);
    if (!boolean)
      return refuse<SemanticValue>(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::SortMismatch,
          location, "Boolean literal has the wrong exact carrier");
    return accept(runtimeSemantic(RuntimeValue::boolean(*boolean)));
  }
  case ValueSort::AlgebraInstance: {
    const auto *algebra =
        std::get_if<AlgebraInstanceValue>(&bindingValue.literal);
    if (!algebra)
      return refuse<SemanticValue>(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::SortMismatch,
          location, "algebra literal has the wrong exact carrier");
    return accept(runtimeSemantic(RuntimeValue::algebra(*algebra)));
  }
  case ValueSort::Subject:
  case ValueSort::ReductionContract:
  case ValueSort::PathTransition:
  case ValueSort::RoundAdjacency:
  case ValueSort::SrsInstance:
  case ValueSort::FriDomainInstance:
    return refuse<SemanticValue>(
        RuntimePhase::BindingResolution, RuntimeRefusalCode::SortMismatch,
        location, "this value sort has no admitted literal carrier");
  }
  return refuse<SemanticValue>(RuntimePhase::BindingResolution,
                               RuntimeRefusalCode::SortMismatch, location,
                               "unknown literal sort");
}

Step<SemanticValue>
resolveBindingValue(const BindingValue &value,
                    const ApplicationEnvironment &environment,
                    const std::string &location) {
  switch (value.kind) {
  case BindingValueKind::Literal:
    return literalValue(value, location);
  case BindingValueKind::SealedArtifactProjection: {
    auto projected = projectArtifactFact(environment.sealed, environment.site,
                                         value.artifactProjection);
    if (!projected)
      return projectionFailure<SemanticValue>(
          projected.takeError(), RuntimePhase::BindingResolution,
          RuntimeRefusalCode::InvalidPayload, location);
    if (projected->sort != value.sort)
      return refuse<SemanticValue>(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::SortMismatch,
          location, "artifact projection returned the wrong exact sort");
    return accept(runtimeSemantic(std::move(*projected)));
  }
  case BindingValueKind::ConclusionSubject:
    if (value.sort != ValueSort::Subject)
      return refuse<SemanticValue>(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::SortMismatch,
          location, "conclusion-subject binding has a non-subject sort");
    return accept(
        runtimeSemantic(RuntimeValue::subject(environment.conclusionSubject)));
  case BindingValueKind::ApplicationPathTransition: {
    auto transition = resolveApplicationPathTransition(
        environment.sealed, environment.site, environment.binding);
    if (!transition)
      return projectionFailure<SemanticValue>(
          transition.takeError(), RuntimePhase::BindingResolution,
          RuntimeRefusalCode::BindingMismatch, location);
    if (transition->sort != value.sort)
      return refuse<SemanticValue>(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::SortMismatch,
          location, "path-transition resolver returned the wrong exact sort");
    return accept(runtimeSemantic(std::move(*transition)));
  }
  case BindingValueKind::ConclusionResource: {
    auto resource = environment.evaluation.resources.find(value.reference);
    if (resource == environment.evaluation.resources.end() ||
        resource->second != value.sort)
      return refuse<SemanticValue>(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::InvalidResource,
          location,
          "conclusion-resource binding names no resource of its exact sort");
    ClosedQuantity quantity;
    quantity.resourceTerms.push_back(
        {registry::Rational::fromInteger(1), value.reference, 1});
    return accept(quantitySemantic(value.sort, std::move(quantity)));
  }
  case BindingValueKind::ResolvedParameter: {
    const ResolvedParameterEnvironment *selected =
        environment.context.findResolvedParameters(environment.binding.ref);
    if (!selected)
      return refuse<SemanticValue>(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::InvalidReference,
          location,
          "resolved-parameter binding has no exact parameter environment");
    auto parameter = selected->values.find(value.reference);
    if (parameter == selected->values.end())
      return refuse<SemanticValue>(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::InvalidReference,
          location,
          "resolved-parameter binding names no supplied external value");
    if (parameter->second.sort != value.sort)
      return refuse<SemanticValue>(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::SortMismatch,
          location, "resolved external parameter has the wrong exact sort");
    return accept(runtimeSemantic(parameter->second));
  }
  }
  return refuse<SemanticValue>(RuntimePhase::BindingResolution,
                               RuntimeRefusalCode::InvalidPayload, location,
                               "unknown binding-value constructor");
}

Step<bool> resolveNamedBindings(
    const std::map<std::string, BindingValue, std::less<>> &bindings,
    const std::vector<TypedDeclaration> &declarations,
    ApplicationEnvironment &environment,
    std::map<std::string, SemanticValue, std::less<>> &output,
    const std::string &location) {
  for (const TypedDeclaration &declaration : declarations) {
    auto binding = bindings.find(declaration.name);
    if (binding == bindings.end())
      return refuse<bool>(RuntimePhase::BindingResolution,
                          RuntimeRefusalCode::InvalidReference,
                          location + "." + declaration.name,
                          "complete binding lacks a declared value");
    auto resolved = resolveBindingValue(binding->second, environment,
                                        location + "." + declaration.name);
    if (!resolved.accepted())
      return {std::nullopt, resolved.refusal};
    if (resolved.value->sort != declaration.sort)
      return refuse<bool>(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::SortMismatch,
          location + "." + declaration.name,
          "resolved named binding has the wrong declaration sort");
    output.emplace(declaration.name, std::move(*resolved.value));
  }
  return accept(true);
}

Step<bool> matchBindingValue(const BindingValue &expected,
                             const SemanticValue &actual,
                             const ApplicationEnvironment &environment,
                             const std::string &location) {
  if (expected.sort != actual.sort)
    return refuse<bool>(RuntimePhase::EqualitySolving,
                        RuntimeRefusalCode::SortMismatch, location,
                        "direct value and actual value have different sorts");
  auto resolved =
      resolveBindingValue(expected, environment, location + ".expected");
  if (!resolved.accepted())
    return {std::nullopt, resolved.refusal};
  if (!semanticEqual(*resolved.value, actual))
    return refuse<bool>(RuntimePhase::EqualitySolving,
                        RuntimeRefusalCode::EqualityMismatch, location,
                        "direct value does not equal the actual value");
  return accept(true);
}

Step<bool> checkExactParameterPins(const SoundnessRule &rule,
                                   const ApplicationEnvironment &environment) {
  for (size_t index = 0; index < rule.exactParameterPins.size(); ++index) {
    const ExactParameterPin &pin = rule.exactParameterPins[index];
    std::string location =
        "apply.exact_parameter_pins[" + std::to_string(index) + "]";
    auto actual = environment.evaluation.parameters.find(pin.parameter);
    if (actual == environment.evaluation.parameters.end())
      return refuse<bool>(RuntimePhase::EqualitySolving,
                          RuntimeRefusalCode::InvalidReference, location,
                          "exact parameter pin names no resolved parameter");
    auto expected =
        resolveBindingValue(pin.expected, environment, location + ".expected");
    if (!expected.accepted())
      return {std::nullopt, expected.refusal};
    if (!semanticEqual(actual->second, *expected.value))
      return refuse<bool>(
          RuntimePhase::EqualitySolving, RuntimeRefusalCode::EqualityMismatch,
          location, "resolved parameter differs from its exact literal pin");
  }
  return accept(true);
}

struct Polynomial {
  registry::Rational constant;
  std::map<std::pair<std::string, uint64_t>, registry::Rational> terms;
};

Polynomial polynomialOf(const ClosedQuantity &quantity) {
  Polynomial result;
  result.constant = quantity.constant;
  for (const ResourceMonomial &term : quantity.resourceTerms)
    result.terms[{term.resource, term.exponent}] = term.coefficient;
  return result;
}

void addCoefficient(
    std::map<std::pair<std::string, uint64_t>, registry::Rational> &terms,
    const std::pair<std::string, uint64_t> &key,
    const registry::Rational &coefficient) {
  auto found = terms.find(key);
  if (found == terms.end()) {
    if (!coefficient.isZero())
      terms.emplace(key, coefficient);
    return;
  }
  found->second = found->second.add(coefficient);
  if (found->second.isZero())
    terms.erase(found);
}

Polynomial addPolynomial(const Polynomial &lhs, const Polynomial &rhs) {
  Polynomial result = lhs;
  result.constant = result.constant.add(rhs.constant);
  for (const auto &[key, coefficient] : rhs.terms)
    addCoefficient(result.terms, key, coefficient);
  return result;
}

Polynomial subtractPolynomial(const Polynomial &lhs, const Polynomial &rhs) {
  Polynomial result = lhs;
  result.constant = result.constant.sub(rhs.constant);
  for (const auto &[key, coefficient] : rhs.terms)
    addCoefficient(result.terms, key, registry::Rational().sub(coefficient));
  return result;
}

Polynomial scalePolynomial(const Polynomial &value,
                           const registry::Rational &scale) {
  Polynomial result;
  result.constant = value.constant.mul(scale);
  for (const auto &[key, coefficient] : value.terms) {
    registry::Rational scaled = coefficient.mul(scale);
    if (!scaled.isZero())
      result.terms.emplace(key, std::move(scaled));
  }
  return result;
}

bool isGround(const Polynomial &value) { return value.terms.empty(); }

Step<Polynomial> multiplyPolynomial(const Polynomial &lhs,
                                    const Polynomial &rhs,
                                    const std::string &location) {
  if (isGround(lhs))
    return accept(scalePolynomial(rhs, lhs.constant));
  if (isGround(rhs))
    return accept(scalePolynomial(lhs, rhs.constant));
  return refuse<Polynomial>(
      RuntimePhase::QuantityValidation,
      RuntimeRefusalCode::UnsupportedNormalForm, location,
      "a product contains more than one symbolic-valued factor");
}

Step<Polynomial> powPolynomial(const Polynomial &base, int64_t exponent,
                               const std::string &location) {
  if (exponent < -kMaxExactExponent || exponent > kMaxExactExponent)
    return refuse<Polynomial>(RuntimePhase::QuantityValidation,
                              RuntimeRefusalCode::ArithmeticDomain, location,
                              "power exponent exceeds the v0 exact range");
  if (exponent == 0) {
    Polynomial one;
    one.constant = registry::Rational::fromInteger(1);
    return accept(std::move(one));
  }
  if (exponent == 1)
    return accept(base);
  if (exponent < 0 && !isGround(base))
    return refuse<Polynomial>(
        RuntimePhase::QuantityValidation,
        RuntimeRefusalCode::UnsupportedNormalForm, location,
        "a symbolic quantity cannot have a negative exponent");
  if (isGround(base)) {
    auto powered = base.constant.pow(exponent);
    if (!powered)
      return projectionFailure<Polynomial>(
          powered.takeError(), RuntimePhase::QuantityValidation,
          RuntimeRefusalCode::ArithmeticDomain, location);
    Polynomial result;
    result.constant = std::move(*powered);
    return accept(std::move(result));
  }

  if (!base.constant.isZero() || base.terms.size() != 1 || exponent < 0)
    return refuse<Polynomial>(
        RuntimePhase::QuantityValidation,
        RuntimeRefusalCode::UnsupportedNormalForm, location,
        "only a ground value or one pure resource monomial has an exact "
        "symbolic power in the v0 normal form");
  const auto &[key, coefficient] = *base.terms.begin();
  uint64_t unsignedExponent = static_cast<uint64_t>(exponent);
  if (unsignedExponent != 0 &&
      (key.second > std::numeric_limits<uint64_t>::max() / unsignedExponent ||
       key.second * unsignedExponent >
           static_cast<uint64_t>(kMaxExactExponent)))
    return refuse<Polynomial>(
        RuntimePhase::QuantityValidation, RuntimeRefusalCode::ArithmeticDomain,
        location, "resource exponent exceeds the v0 closed normal form");
  auto poweredCoefficient = coefficient.pow(exponent);
  if (!poweredCoefficient)
    return projectionFailure<Polynomial>(
        poweredCoefficient.takeError(), RuntimePhase::QuantityValidation,
        RuntimeRefusalCode::ArithmeticDomain, location);
  Polynomial result;
  result.terms.emplace(std::pair{key.first, key.second * unsignedExponent},
                       std::move(*poweredCoefficient));
  return accept(std::move(result));
}

Step<ClosedQuantity> closePolynomial(const Polynomial &value,
                                     const std::string &location) {
  if (!isNonnegative(value.constant))
    return refuse<ClosedQuantity>(
        RuntimePhase::QuantityValidation,
        RuntimeRefusalCode::UnsupportedNormalForm, location,
        "closed quantity has a negative constant coefficient");
  ClosedQuantity result;
  result.constant = value.constant;
  for (const auto &[key, coefficient] : value.terms) {
    if (coefficient.isZero())
      continue;
    if (key.second == 0 ||
        key.second > static_cast<uint64_t>(kMaxExactExponent))
      return refuse<ClosedQuantity>(
          RuntimePhase::QuantityValidation,
          RuntimeRefusalCode::ArithmeticDomain, location,
          "resource exponent exceeds the v0 closed normal form");
    if (!isPositive(coefficient))
      return refuse<ClosedQuantity>(
          RuntimePhase::QuantityValidation,
          RuntimeRefusalCode::UnsupportedNormalForm, location,
          "closed quantity has a negative resource coefficient");
    result.resourceTerms.push_back({coefficient, key.first, key.second});
  }
  return accept(std::move(result));
}

bool integerValued(
    const ClosedQuantity &quantity,
    const std::map<std::string, ValueSort, std::less<>> &resourceSorts) {
  if (!isInteger(quantity.constant))
    return false;
  for (const ResourceMonomial &term : quantity.resourceTerms) {
    auto resource = resourceSorts.find(term.resource);
    if (resource == resourceSorts.end() ||
        resource->second != ValueSort::Integer || !isInteger(term.coefficient))
      return false;
  }
  return true;
}

Step<Polynomial> numericSemantic(const SemanticValue &value,
                                 const std::string &location) {
  std::optional<ClosedQuantity> quantity = numericQuantity(value);
  if (!quantity)
    return refuse<Polynomial>(
        RuntimePhase::QuantityValidation, RuntimeRefusalCode::SortMismatch,
        location, "quantity leaf did not resolve to a numeric value");
  return accept(polynomialOf(*quantity));
}

Step<Polynomial> contractRoundQuantity(const QuantityTemplate &quantity,
                                       const EvaluationEnvironment &environment,
                                       const std::string &location) {
  if (!environment.currentRound ||
      environment.currentRoundCase != quantity.caseName)
    return refuse<Polynomial>(
        RuntimePhase::QuantityValidation, RuntimeRefusalCode::InvalidReference,
        location, "contract-round fact is outside its lexical case binder");
  std::optional<registry::Rational> value;
  switch (quantity.contractRoundField) {
  case ContractRoundField::ChallengeSpace:
    value = environment.currentRound->challengeSpace;
    break;
  case ContractRoundField::ChallengeCount:
    value = environment.currentRound->challengeCount;
    break;
  case ContractRoundField::RoundDegree:
    value = environment.currentRound->roundDegree;
    break;
  case ContractRoundField::ChallengeSpaceLog2:
    value = environment.currentRound->challengeSpaceLog2;
    break;
  }
  if (!value)
    return refuse<Polynomial>(
        RuntimePhase::QuantityValidation, RuntimeRefusalCode::InvalidReference,
        location, "authenticated contract round lacks the selected field");
  Polynomial result;
  result.constant = *value;
  return accept(std::move(result));
}

Step<const ExtractionCoordinate *>
selectPremiseCoordinate(const QuantityTemplate &quantity,
                        const EvaluationEnvironment &environment,
                        const std::string &location) {
  auto premise = environment.premises.find(quantity.port);
  if (premise == environment.premises.end())
    return refuse<const ExtractionCoordinate *>(
        RuntimePhase::PremiseResolution, RuntimeRefusalCode::InvalidReference,
        location, "premise-coordinate selector names no specialized premise");
  const auto *extraction =
      std::get_if<ExtractionResult>(&premise->second->result);
  if (!extraction)
    return refuse<const ExtractionCoordinate *>(
        RuntimePhase::PremiseResolution,
        RuntimeRefusalCode::InvalidResultSchema, location,
        "premise-coordinate selector reads a non-extraction result");
  std::string label;
  if (!environment.currentCoordinate)
    return refuse<const ExtractionCoordinate *>(
        RuntimePhase::PremiseResolution, RuntimeRefusalCode::InvalidReference,
        location, "bound-coordinate selector is outside its coordinate binder");
  label = environment.currentCoordinate->label;
  auto found = std::find_if(extraction->coordinates.begin(),
                            extraction->coordinates.end(),
                            [&](const ExtractionCoordinate &coordinate) {
                              return coordinate.label == label;
                            });
  if (found == extraction->coordinates.end())
    return refuse<const ExtractionCoordinate *>(
        RuntimePhase::PremiseResolution, RuntimeRefusalCode::InvalidReference,
        location, "premise-coordinate selector names no exact coordinate");
  return accept(&*found);
}

Step<Polynomial> evaluateQuantity(const QuantityTemplate &quantity,
                                  const EvaluationEnvironment &environment,
                                  const std::string &location) {
  switch (quantity.kind) {
  case QuantityKind::RationalLiteral: {
    Polynomial result;
    result.constant = quantity.literal;
    return accept(std::move(result));
  }
  case QuantityKind::Parameter: {
    auto value = environment.parameters.find(quantity.name);
    if (value == environment.parameters.end())
      return refuse<Polynomial>(RuntimePhase::QuantityValidation,
                                RuntimeRefusalCode::InvalidReference, location,
                                "quantity names no resolved rule parameter");
    return numericSemantic(value->second, location);
  }
  case QuantityKind::ArtifactFact: {
    auto value = environment.facts.find(quantity.name);
    if (value == environment.facts.end())
      return refuse<Polynomial>(
          RuntimePhase::QuantityValidation,
          RuntimeRefusalCode::InvalidReference, location,
          "quantity names no resolved artifact-fact port");
    return numericSemantic(value->second, location);
  }
  case QuantityKind::ContractRoundFact:
    return contractRoundQuantity(quantity, environment, location);
  case QuantityKind::PremiseCoordinate: {
    auto coordinate = selectPremiseCoordinate(quantity, environment, location);
    if (!coordinate.accepted())
      return {std::nullopt, coordinate.refusal};
    if (quantity.premiseCoordinateField == PremiseCoordinateField::Arity)
      return accept(polynomialOf((*coordinate.value)->arity));
    if (!(*coordinate.value)->challengeSpace)
      return refuse<Polynomial>(
          RuntimePhase::PremiseResolution, RuntimeRefusalCode::InvalidPayload,
          location, "selected extraction coordinate has no challenge space");
    return accept(polynomialOf(*(*coordinate.value)->challengeSpace));
  }
  case QuantityKind::ResourceVariable: {
    auto resource = environment.resources.find(quantity.name);
    if (resource == environment.resources.end())
      return refuse<Polynomial>(
          RuntimePhase::QuantityValidation, RuntimeRefusalCode::InvalidResource,
          location, "quantity names no conclusion resource variable");
    Polynomial result;
    result.terms.emplace(std::pair{quantity.name, uint64_t(1)},
                         registry::Rational::fromInteger(1));
    return accept(std::move(result));
  }
  case QuantityKind::Add:
  case QuantityKind::Sub:
  case QuantityKind::Mul:
  case QuantityKind::Div:
  case QuantityKind::Pow:
  case QuantityKind::Pow2:
  case QuantityKind::Pow2Up:
    break;
  }

  std::vector<Polynomial> operands;
  operands.reserve(quantity.operands.size());
  for (size_t index = 0; index < quantity.operands.size(); ++index) {
    auto operand =
        evaluateQuantity(quantity.operands[index], environment,
                         location + ".operands[" + std::to_string(index) + "]");
    if (!operand.accepted())
      return operand;
    operands.push_back(std::move(*operand.value));
  }

  switch (quantity.kind) {
  case QuantityKind::Add: {
    Polynomial result;
    for (const Polynomial &operand : operands)
      result = addPolynomial(result, operand);
    return accept(std::move(result));
  }
  case QuantityKind::Sub:
    return accept(subtractPolynomial(operands[0], operands[1]));
  case QuantityKind::Mul: {
    Polynomial result;
    result.constant = registry::Rational::fromInteger(1);
    for (size_t index = 0; index < operands.size(); ++index) {
      auto product = multiplyPolynomial(result, operands[index],
                                        location + ".operands[" +
                                            std::to_string(index) + "]");
      if (!product.accepted())
        return product;
      result = std::move(*product.value);
    }
    return accept(std::move(result));
  }
  case QuantityKind::Div:
    if (!isGround(operands[1]) || operands[1].constant.isZero())
      return refuse<Polynomial>(
          RuntimePhase::QuantityValidation,
          RuntimeRefusalCode::ArithmeticDomain, location,
          "quantity divisor must be a nonzero ground rational");
    else {
      auto inverse =
          registry::Rational::fromInteger(1).div(operands[1].constant);
      if (!inverse)
        return projectionFailure<Polynomial>(
            inverse.takeError(), RuntimePhase::QuantityValidation,
            RuntimeRefusalCode::ArithmeticDomain, location);
      return accept(scalePolynomial(operands[0], *inverse));
    }
  case QuantityKind::Pow:
    if (!isGround(operands[1]) || !isInteger(operands[1].constant))
      return refuse<Polynomial>(
          RuntimePhase::QuantityValidation,
          RuntimeRefusalCode::ArithmeticDomain, location,
          "quantity exponent must be a ground exact integer");
    else {
      auto exponent = operands[1].constant.floorToInt();
      if (!exponent)
        return projectionFailure<Polynomial>(
            exponent.takeError(), RuntimePhase::QuantityValidation,
            RuntimeRefusalCode::ArithmeticDomain, location);
      return powPolynomial(operands[0], *exponent, location);
    }
  case QuantityKind::Pow2:
  case QuantityKind::Pow2Up: {
    if (!isGround(operands[0]))
      return refuse<Polynomial>(RuntimePhase::QuantityValidation,
                                RuntimeRefusalCode::UnsupportedNormalForm,
                                location, "dyadic exponent must be ground");
    if (quantity.kind == QuantityKind::Pow2Up &&
        operands[0].constant.denStr() != "1" &&
        operands[0].constant.denStr() != "2")
      return refuse<Polynomial>(RuntimePhase::QuantityValidation,
                                RuntimeRefusalCode::ArithmeticDomain, location,
                                "Pow2Up exponent is not an exact half-integer");
    llvm::Expected<int64_t> exponent = quantity.kind == QuantityKind::Pow2
                                           ? operands[0].constant.floorToInt()
                                           : operands[0].constant.ceilToInt();
    if (!exponent || (quantity.kind == QuantityKind::Pow2 &&
                      !isInteger(operands[0].constant))) {
      if (!exponent)
        return projectionFailure<Polynomial>(
            exponent.takeError(), RuntimePhase::QuantityValidation,
            RuntimeRefusalCode::ArithmeticDomain, location);
      return refuse<Polynomial>(RuntimePhase::QuantityValidation,
                                RuntimeRefusalCode::ArithmeticDomain, location,
                                "Pow2 exponent is not an exact integer");
    }
    if (*exponent < -kMaxExactExponent || *exponent > kMaxExactExponent)
      return refuse<Polynomial>(RuntimePhase::QuantityValidation,
                                RuntimeRefusalCode::ArithmeticDomain, location,
                                "dyadic exponent exceeds the v0 exact range");
    auto powered = registry::Rational::fromInteger(2).pow(*exponent);
    if (!powered)
      return projectionFailure<Polynomial>(
          powered.takeError(), RuntimePhase::QuantityValidation,
          RuntimeRefusalCode::ArithmeticDomain, location);
    Polynomial result;
    result.constant = std::move(*powered);
    return accept(std::move(result));
  }
  case QuantityKind::RationalLiteral:
  case QuantityKind::Parameter:
  case QuantityKind::ArtifactFact:
  case QuantityKind::ContractRoundFact:
  case QuantityKind::PremiseCoordinate:
  case QuantityKind::ResourceVariable:
    break;
  }
  return refuse<Polynomial>(RuntimePhase::QuantityValidation,
                            RuntimeRefusalCode::InvalidPayload, location,
                            "unknown quantity constructor");
}

Step<ClosedQuantity>
evaluateClosedQuantity(const QuantityTemplate &quantity,
                       const EvaluationEnvironment &environment,
                       const std::string &location) {
  auto polynomial = evaluateQuantity(quantity, environment, location);
  if (!polynomial.accepted())
    return {std::nullopt, polynomial.refusal};
  return closePolynomial(*polynomial.value, location);
}

struct ExternalReferenceCollector {
  std::map<std::string, ValueSort, std::less<>> references;
  std::optional<std::string> error;

  void add(const BindingValue &value, const std::string &location) {
    if (value.kind != BindingValueKind::ResolvedParameter)
      return;
    auto [found, inserted] = references.emplace(value.reference, value.sort);
    if (!inserted && found->second != value.sort)
      error = location + " resolves one external key at two sorts";
  }

  void add(const RuleBound &bound, const std::string &location) {
    if (bound.kind == RuleBoundKind::PrimitiveAdvantage)
      for (size_t index = 0; index < bound.game.instanceArguments.size();
           ++index)
        add(bound.game.instanceArguments[index],
            location + ".game.arguments[" + std::to_string(index) + "]");
    for (size_t index = 0; index < bound.operands.size(); ++index)
      add(bound.operands[index],
          location + ".operands[" + std::to_string(index) + "]");
  }

  void add(const RuleBody &body) {
    std::visit(
        [&](const auto &entry) {
          using T = std::decay_t<decltype(entry)>;
          if constexpr (std::is_same_v<T, NativeRoundByRoundEntry>) {
            for (const RoundTemplate &round : entry.rounds.rounds)
              add(round.bound, "rule.body.rounds");
            for (const ContractRoundCase &round : entry.rounds.cases)
              add(round.bound, "rule.body.contract_rounds");
          } else if constexpr (std::is_same_v<T, RoundByRoundPreservation>) {
            for (const RoundTemplate &round : entry.appendedRounds.rounds)
              add(round.bound, "rule.body.appended_rounds");
            for (const ContractRoundCase &round : entry.appendedRounds.cases)
              add(round.bound, "rule.body.appended_contract_rounds");
          } else if constexpr (std::is_same_v<T, ComputationalEntry>) {
            add(entry.failureBound, "rule.body.failure_bound");
          } else if constexpr (std::is_same_v<T, CompletenessEntry>) {
            add(entry.bound, "rule.body.bound");
          } else if constexpr (std::is_same_v<T,
                                              SpecialSoundnessPreservation>) {
            add(entry.conclusionFailureBound,
                "rule.body.conclusion_failure_bound");
          } else if constexpr (std::is_same_v<T,
                                              SpecialSoundnessToRoundByRound>) {
            add(entry.perCoordinateBound, "rule.body.per_coordinate_bound");
          } else if constexpr (std::is_same_v<
                                   T, StateRestorationToFiatShamirDuplex>) {
            add(entry.localDuplexBound, "rule.body.local_duplex_bound");
          }
        },
        body);
  }
};

void collectBindingValues(const RuleBinding &binding,
                          ExternalReferenceCollector &collector) {
  for (const auto &[name, value] : binding.parameterBindings)
    collector.add(value, "binding.parameters." + name);
  for (const auto &[name, value] : binding.factBindings)
    collector.add(value, "binding.facts." + name);
  for (const auto &[slot, values] : binding.conditionArgumentBindings)
    for (size_t index = 0; index < values.size(); ++index)
      collector.add(values[index], "binding.conditions." + slot + "[" +
                                       std::to_string(index) + "]");
  for (const auto &[slot, values] : binding.hypothesisArgumentBindings)
    for (size_t index = 0; index < values.size(); ++index)
      collector.add(values[index], "binding.hypotheses." + slot + "[" +
                                       std::to_string(index) + "]");
  for (const auto &[port, relation] : binding.premiseRelations)
    for (size_t index = 0; index < relation.externalArguments.size(); ++index)
      collector.add(relation.externalArguments[index],
                    "binding.premises." + port + ".arguments[" +
                        std::to_string(index) + "]");
}

void collectRuleValues(const SoundnessRule &rule,
                       ExternalReferenceCollector &collector) {
  for (size_t index = 0; index < rule.exactParameterPins.size(); ++index)
    collector.add(rule.exactParameterPins[index].expected,
                  "rule.exact_parameter_pins[" + std::to_string(index) +
                      "].expected");
  collector.add(rule.body);
}

RuntimeCheckResult
checkContextResolvedParameters(const SoundnessContext &context,
                               const RuleBinding &binding,
                               const SoundnessRule &rule) {
  ExternalReferenceCollector collector;
  collectBindingValues(binding, collector);
  collectRuleValues(rule, collector);
  if (collector.error)
    return refuseCheck(
        RuntimePhase::BindingResolution, RuntimeRefusalCode::SortMismatch,
        "context.resolved_parameters." + binding.ref.id, *collector.error);

  const auto &environments = context.resolvedParameters();
  auto environment = environments.find(binding.ref.id);
  if (collector.references.empty()) {
    if (environment != environments.end() &&
        !environment->second.values.empty())
      return refuseCheck(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::InvalidReference,
          "context.resolved_parameters." + binding.ref.id,
          "binding has no external parameter references but values were "
          "supplied");
    return {};
  }
  if (environment == environments.end())
    return refuseCheck(RuntimePhase::BindingResolution,
                       RuntimeRefusalCode::InvalidReference,
                       "context.resolved_parameters." + binding.ref.id,
                       "binding has unresolved external semantic parameters");
  if (environment->second.bindingRef != binding.ref)
    return refuseCheck(
        RuntimePhase::BindingResolution, RuntimeRefusalCode::InvalidReference,
        "context.resolved_parameters." + binding.ref.id + ".binding_ref",
        "external parameter environment names a different exact binding");
  if (environment->second.values.size() != collector.references.size())
    return refuseCheck(
        RuntimePhase::BindingResolution, RuntimeRefusalCode::InvalidReference,
        "context.resolved_parameters." + binding.ref.id,
        "external parameter environment is not an exact key set");

  for (const auto &[name, expectedSort] : collector.references) {
    auto value = environment->second.values.find(name);
    if (value == environment->second.values.end())
      return refuseCheck(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::InvalidReference,
          "context.resolved_parameters." + binding.ref.id + "." + name,
          "required external parameter is absent");
    if (value->second.sort != expectedSort)
      return refuseCheck(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::SortMismatch,
          "context.resolved_parameters." + binding.ref.id + "." + name,
          "external parameter has the wrong exact sort");
    RuntimeCheckResult wellFormed = checkRuntimeValueWellFormed(value->second);
    if (!wellFormed.accepted()) {
      SoundnessRefusal detail = *wellFormed.refusal;
      detail.location = "context.resolved_parameters." + binding.ref.id + "." +
                        name + "." + detail.location;
      return {std::move(detail)};
    }
  }
  return {};
}

} // namespace

namespace {

RuntimeCheckResult
checkSoundnessContextWellFormed(const SoundnessContext &context) {
  std::set<std::string, std::less<>> selectedBindingIds;
  for (const ExactRef &bindingRef : context.selectedBindingRefs()) {
    if (!validRef(bindingRef))
      return refuseCheck(RuntimePhase::BindingResolution,
                         RuntimeRefusalCode::InvalidReference,
                         "context.bindings." + bindingRef.id,
                         "selected binding reference is not exact");
    if (!selectedBindingIds.insert(bindingRef.id).second)
      return refuseCheck(RuntimePhase::BindingResolution,
                         RuntimeRefusalCode::DuplicateName,
                         "context.bindings." + bindingRef.id,
                         "selected binding id is duplicated");
    const RuleBinding *binding = context.findBinding(bindingRef);
    if (!binding)
      return refuseCheck(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::InvalidReference,
          "context.bindings." + bindingRef.id,
          "selected exact binding is absent from the immutable catalog");
    const SoundnessRule *rule = context.findRule(binding->ruleRef);
    if (!rule)
      return refuseCheck(RuntimePhase::BindingResolution,
                         RuntimeRefusalCode::InvalidReference,
                         "context.bindings." + bindingRef.id + ".rule_ref",
                         "selected binding names no exact catalog rule");
    RuleWfResult ruleWf = checkRuleWellFormed(context.schemas(), *rule);
    if (!ruleWf.accepted())
      return refuseCheck(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::InvalidPayload,
          "context.bindings." + bindingRef.id + ".rule." +
              ruleWf.refusal->location,
          std::string(ruleWfRefusalCodeName(ruleWf.refusal->code)) + ": " +
              ruleWf.refusal->detail);
    RuleWfResult bindingWf =
        checkRuleBindingWellFormed(context.schemas(), *rule, *binding);
    if (!bindingWf.accepted())
      return refuseCheck(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::InvalidPayload,
          "context.bindings." + bindingRef.id + "." +
              bindingWf.refusal->location,
          std::string(ruleWfRefusalCodeName(bindingWf.refusal->code)) + ": " +
              bindingWf.refusal->detail);
    RuntimeCheckResult parameters =
        checkContextResolvedParameters(context, *binding, *rule);
    if (!parameters.accepted())
      return parameters;
  }

  for (const auto &[id, environment] : context.resolvedParameters()) {
    if (id != environment.bindingRef.id)
      return refuseCheck(RuntimePhase::BindingResolution,
                         RuntimeRefusalCode::InvalidReference,
                         "context.resolved_parameters." + id,
                         "external parameter map key and binding reference "
                         "disagree");
    const RuleBinding *binding = context.findBinding(environment.bindingRef);
    if (!binding)
      return refuseCheck(RuntimePhase::BindingResolution,
                         RuntimeRefusalCode::InvalidReference,
                         "context.resolved_parameters." + id,
                         "external parameters name no exact selected binding");
  }
  return {};
}

} // namespace

SoundnessContextOutcome
buildSoundnessContext(const SoundnessCatalog &catalog,
                      std::vector<ExactRef> selectedBindingRefs,
                      ResolvedParameterEnvironments resolvedParameters) {
  SoundnessContext context(catalog, std::move(selectedBindingRefs),
                           std::move(resolvedParameters));
  RuntimeCheckResult check = checkSoundnessContextWellFormed(context);
  if (!check.accepted())
    return {std::nullopt, std::move(check.refusal)};
  return {std::move(context), std::nullopt};
}

namespace {

bool primitiveKeyEqual(const PrimitiveGameTerm &lhs,
                       const PrimitiveGameTerm &rhs) {
  return lhs.instance == rhs.instance &&
         lhs.resourceSubstitution == rhs.resourceSubstitution;
}

Step<ClosedBound> addClosedBounds(const ClosedBound &lhs,
                                  const ClosedBound &rhs,
                                  const std::string &location) {
  ClosedBound result;
  auto quantity = closePolynomial(
      addPolynomial(polynomialOf(lhs.quantity), polynomialOf(rhs.quantity)),
      location + ".quantity");
  if (!quantity.accepted())
    return {std::nullopt, quantity.refusal};
  result.quantity = std::move(*quantity.value);
  result.primitiveGameTerms = lhs.primitiveGameTerms;
  for (const PrimitiveGameTerm &term : rhs.primitiveGameTerms) {
    auto equal = std::find_if(result.primitiveGameTerms.begin(),
                              result.primitiveGameTerms.end(),
                              [&](const PrimitiveGameTerm &candidate) {
                                return primitiveKeyEqual(candidate, term);
                              });
    if (equal == result.primitiveGameTerms.end()) {
      result.primitiveGameTerms.push_back(term);
      continue;
    }
    equal->coefficient = equal->coefficient.add(term.coefficient);
    if (equal->coefficient.isZero())
      result.primitiveGameTerms.erase(equal);
  }
  for (const PrimitiveGameTerm &term : result.primitiveGameTerms)
    if (!isPositive(term.coefficient))
      return refuse<ClosedBound>(
          RuntimePhase::BoundValidation,
          RuntimeRefusalCode::UnsupportedNormalForm, location,
          "closed bound has a nonpositive primitive-game coefficient");
  return accept(std::move(result));
}

bool boundIsGroundQuantity(const ClosedBound &bound) {
  return bound.primitiveGameTerms.empty() &&
         bound.quantity.resourceTerms.empty();
}

Step<ClosedBound> scaleClosedBound(const ClosedQuantity &scale,
                                   const ClosedBound &bound,
                                   const std::string &location) {
  Polynomial coefficient = polynomialOf(scale);
  ClosedBound result;
  if (isGround(coefficient)) {
    if (!isNonnegative(coefficient.constant))
      return refuse<ClosedBound>(RuntimePhase::BoundValidation,
                                 RuntimeRefusalCode::ArithmeticDomain, location,
                                 "bound scale is negative");
    auto scaledQuantity = closePolynomial(
        scalePolynomial(polynomialOf(bound.quantity), coefficient.constant),
        location + ".quantity");
    if (!scaledQuantity.accepted())
      return {std::nullopt, scaledQuantity.refusal};
    result.quantity = std::move(*scaledQuantity.value);
    if (coefficient.constant.isZero())
      return accept(std::move(result));
    result.primitiveGameTerms = bound.primitiveGameTerms;
    for (PrimitiveGameTerm &term : result.primitiveGameTerms)
      term.coefficient = term.coefficient.mul(coefficient.constant);
    return accept(std::move(result));
  }

  if (!boundIsGroundQuantity(bound))
    return refuse<ClosedBound>(
        RuntimePhase::BoundValidation,
        RuntimeRefusalCode::UnsupportedNormalForm, location,
        "symbolic bound scale would multiply resource or primitive-game "
        "support");
  auto product = multiplyPolynomial(coefficient, polynomialOf(bound.quantity),
                                    location + ".quantity");
  if (!product.accepted())
    return {std::nullopt, product.refusal};
  auto closed = closePolynomial(*product.value, location + ".quantity");
  if (!closed.accepted())
    return {std::nullopt, closed.refusal};
  result.quantity = std::move(*closed.value);
  return accept(std::move(result));
}

Step<ClosedBound> maximumClosedBounds(const std::vector<ClosedBound> &bounds,
                                      const std::string &location) {
  if (bounds.empty())
    return refuse<ClosedBound>(RuntimePhase::BoundValidation,
                               RuntimeRefusalCode::EmptyCollection, location,
                               "bound maximum has no alternatives");
  const ClosedBound *maximum = nullptr;
  for (const ClosedBound &bound : bounds) {
    if (!boundIsGroundQuantity(bound))
      return refuse<ClosedBound>(
          RuntimePhase::BoundValidation,
          RuntimeRefusalCode::UnsupportedNormalForm, location,
          "v0 accepts Max only over ground statistical quantities");
    if (!maximum ||
        maximum->quantity.constant.compare(bound.quantity.constant) < 0)
      maximum = &bound;
  }
  return accept(*maximum);
}

Step<ClosedBound> closeRuleBound(const RuleBound &bound,
                                 const ApplicationEnvironment &application,
                                 EvaluationEnvironment &environment,
                                 const std::string &location) {
  switch (bound.kind) {
  case RuleBoundKind::Quantity: {
    auto quantity = evaluateClosedQuantity(bound.quantity, environment,
                                           location + ".quantity");
    if (!quantity.accepted())
      return {std::nullopt, quantity.refusal};
    ClosedBound result;
    result.quantity = std::move(*quantity.value);
    return accept(std::move(result));
  }
  case RuleBoundKind::ScalarBound: {
    auto premise = environment.premises.find(bound.premisePort);
    if (premise == environment.premises.end())
      return refuse<ClosedBound>(
          RuntimePhase::PremiseResolution, RuntimeRefusalCode::InvalidReference,
          location, "scalar-bound selector names no specialized premise");
    const auto *scalar = std::get_if<ScalarResult>(&premise->second->result);
    if (!scalar)
      return refuse<ClosedBound>(
          RuntimePhase::PremiseResolution,
          RuntimeRefusalCode::InvalidResultSchema, location,
          "scalar-bound selector reads a nonscalar premise");
    return accept(scalar->bound);
  }
  case RuleBoundKind::PrimitiveAdvantage: {
    auto definition =
        application.context.schemas().primitiveGames.find(bound.game.gameRef);
    if (definition == application.context.schemas().primitiveGames.end())
      return refuse<ClosedBound>(
          RuntimePhase::BoundValidation,
          RuntimeRefusalCode::InvalidPrimitiveGame, location,
          "primitive-advantage template names no admitted game");
    PrimitiveGameTerm term;
    term.coefficient = registry::Rational::fromInteger(1);
    term.instance.ref = definition->second.ref;
    for (size_t index = 0; index < bound.game.instanceArguments.size();
         ++index) {
      auto semantic = resolveBindingValue(
          bound.game.instanceArguments[index], application,
          location + ".instance.arguments[" + std::to_string(index) + "]");
      if (!semantic.accepted())
        return {std::nullopt, semantic.refusal};
      auto runtime = requireRuntimeValue(*semantic.value,
                                         location + ".instance.arguments[" +
                                             std::to_string(index) + "]");
      if (!runtime.accepted())
        return {std::nullopt, runtime.refusal};
      term.instance.arguments.push_back(std::move(*runtime.value));
    }
    for (const TypedDeclaration &resource : definition->second.resources) {
      auto substitution = bound.gameResourceSubstitution.find(resource.name);
      if (substitution == bound.gameResourceSubstitution.end())
        return refuse<ClosedBound>(
            RuntimePhase::BoundValidation, RuntimeRefusalCode::InvalidResource,
            location, "primitive-game resource substitution is incomplete");
      auto closed = evaluateClosedQuantity(
          substitution->second, environment,
          location + ".resource_substitution." + resource.name);
      if (!closed.accepted())
        return {std::nullopt, closed.refusal};
      if (resource.sort == ValueSort::Integer &&
          !integerValued(*closed.value, environment.resources))
        return refuse<ClosedBound>(
            RuntimePhase::BoundValidation, RuntimeRefusalCode::SortMismatch,
            location + ".resource_substitution." + resource.name,
            "integer primitive-game resource has a noninteger substitution");
      term.resourceSubstitution.emplace(resource.name,
                                        std::move(*closed.value));
    }
    ClosedBound result;
    result.primitiveGameTerms.push_back(std::move(term));
    return accept(std::move(result));
  }
  case RuleBoundKind::Add: {
    ClosedBound result;
    for (size_t index = 0; index < bound.operands.size(); ++index) {
      auto operand =
          closeRuleBound(bound.operands[index], application, environment,
                         location + ".operands[" + std::to_string(index) + "]");
      if (!operand.accepted())
        return operand;
      auto sum = addClosedBounds(result, *operand.value, location);
      if (!sum.accepted())
        return sum;
      result = std::move(*sum.value);
    }
    return accept(std::move(result));
  }
  case RuleBoundKind::Scale: {
    auto scale = evaluateClosedQuantity(bound.quantity, environment,
                                        location + ".scale");
    if (!scale.accepted())
      return {std::nullopt, scale.refusal};
    auto operand = closeRuleBound(bound.operands.front(), application,
                                  environment, location + ".operand");
    if (!operand.accepted())
      return operand;
    return scaleClosedBound(*scale.value, *operand.value, location);
  }
  case RuleBoundKind::Max: {
    std::vector<ClosedBound> alternatives;
    for (size_t index = 0; index < bound.operands.size(); ++index) {
      auto operand =
          closeRuleBound(bound.operands[index], application, environment,
                         location + ".operands[" + std::to_string(index) + "]");
      if (!operand.accepted())
        return operand;
      alternatives.push_back(std::move(*operand.value));
    }
    return maximumClosedBounds(alternatives, location);
  }
  }
  return refuse<ClosedBound>(RuntimePhase::BoundValidation,
                             RuntimeRefusalCode::InvalidPayload, location,
                             "unknown rule-bound constructor");
}

Step<ClosedQuantity> substituteQuantity(
    const ClosedQuantity &quantity,
    const std::map<std::string, ClosedQuantity, std::less<>> &substitutions,
    const std::string &location) {
  Polynomial result;
  result.constant = quantity.constant;
  for (const ResourceMonomial &term : quantity.resourceTerms) {
    auto substitution = substitutions.find(term.resource);
    if (substitution == substitutions.end())
      return refuse<ClosedQuantity>(
          RuntimePhase::ResourceSpecialization,
          RuntimeRefusalCode::InvalidResource, location,
          "premise quantity contains an unsubstituted resource variable");
    if (term.exponent > static_cast<uint64_t>(kMaxExactExponent))
      return refuse<ClosedQuantity>(
          RuntimePhase::ResourceSpecialization,
          RuntimeRefusalCode::ArithmeticDomain, location,
          "premise resource exponent exceeds the v0 exact range");
    auto powered = powPolynomial(polynomialOf(substitution->second),
                                 static_cast<int64_t>(term.exponent), location);
    if (!powered.accepted())
      return {std::nullopt, powered.refusal};
    result = addPolynomial(result,
                           scalePolynomial(*powered.value, term.coefficient));
  }
  auto closed = closePolynomial(result, location);
  if (!closed.accepted() && closed.refusal)
    closed.refusal->phase = RuntimePhase::ResourceSpecialization;
  return closed;
}

Step<ClosedBound> substituteBound(
    const ClosedBound &bound,
    const std::map<std::string, ClosedQuantity, std::less<>> &substitutions,
    const std::string &location) {
  ClosedBound result;
  auto quantity =
      substituteQuantity(bound.quantity, substitutions, location + ".quantity");
  if (!quantity.accepted())
    return {std::nullopt, quantity.refusal};
  result.quantity = std::move(*quantity.value);
  for (size_t index = 0; index < bound.primitiveGameTerms.size(); ++index) {
    PrimitiveGameTerm term = bound.primitiveGameTerms[index];
    for (auto &[name, value] : term.resourceSubstitution) {
      auto specialized = substituteQuantity(
          value, substitutions,
          location + ".primitive_game_terms[" + std::to_string(index) +
              "].resource_substitution." + name);
      if (!specialized.accepted())
        return {std::nullopt, specialized.refusal};
      value = std::move(*specialized.value);
    }
    auto existing = std::find_if(result.primitiveGameTerms.begin(),
                                 result.primitiveGameTerms.end(),
                                 [&](const PrimitiveGameTerm &candidate) {
                                   return primitiveKeyEqual(candidate, term);
                                 });
    if (existing == result.primitiveGameTerms.end()) {
      result.primitiveGameTerms.push_back(std::move(term));
      continue;
    }
    existing->coefficient = existing->coefficient.add(term.coefficient);
    if (!isPositive(existing->coefficient))
      return refuse<ClosedBound>(
          RuntimePhase::ResourceSpecialization,
          RuntimeRefusalCode::UnsupportedNormalForm, location,
          "specialized primitive-game coefficient is not positive");
  }
  RuntimeCheckResult resultCheck =
      checkClosedBoundWellFormed(result, location + ".result");
  if (!resultCheck.accepted()) {
    resultCheck.refusal->phase = RuntimePhase::ResourceSpecialization;
    return {std::nullopt, std::move(resultCheck.refusal)};
  }
  return accept(std::move(result));
}

Step<SecurityResult> substituteResult(
    const SecurityResult &result,
    const std::map<std::string, ClosedQuantity, std::less<>> &substitutions,
    const std::string &location) {
  if (const auto *extraction = std::get_if<ExtractionResult>(&result)) {
    ExtractionResult specialized;
    for (size_t index = 0; index < extraction->coordinates.size(); ++index) {
      const ExtractionCoordinate &coordinate = extraction->coordinates[index];
      ExtractionCoordinate output;
      output.label = coordinate.label;
      auto arity = substituteQuantity(coordinate.arity, substitutions,
                                      location + ".coordinates[" +
                                          std::to_string(index) + "].arity");
      if (!arity.accepted())
        return {std::nullopt, arity.refusal};
      output.arity = std::move(*arity.value);
      if (coordinate.challengeSpace) {
        auto space =
            substituteQuantity(*coordinate.challengeSpace, substitutions,
                               location + ".coordinates[" +
                                   std::to_string(index) + "].challenge_space");
        if (!space.accepted())
          return {std::nullopt, space.refusal};
        output.challengeSpace = std::move(*space.value);
      }
      specialized.coordinates.push_back(std::move(output));
    }
    if (extraction->failureBound) {
      auto bound = substituteBound(*extraction->failureBound, substitutions,
                                   location + ".failure_bound");
      if (!bound.accepted())
        return {std::nullopt, bound.refusal};
      specialized.failureBound = std::move(*bound.value);
    }
    return accept(SecurityResult(std::move(specialized)));
  }
  if (const auto *rounds = std::get_if<RoundResult>(&result)) {
    RoundResult specialized;
    for (size_t index = 0; index < rounds->rounds.size(); ++index) {
      const RoundResultEntry &round = rounds->rounds[index];
      RoundResultEntry output;
      output.roundIndex = round.roundIndex;
      auto space = substituteQuantity(
          round.challengeSpace, substitutions,
          location + ".rounds[" + std::to_string(index) + "].challenge_space");
      if (!space.accepted())
        return {std::nullopt, space.refusal};
      output.challengeSpace = std::move(*space.value);
      auto bound = substituteBound(round.bound, substitutions,
                                   location + ".rounds[" +
                                       std::to_string(index) + "].bound");
      if (!bound.accepted())
        return {std::nullopt, bound.refusal};
      output.bound = std::move(*bound.value);
      specialized.rounds.push_back(std::move(output));
    }
    return accept(SecurityResult(std::move(specialized)));
  }
  auto bound = substituteBound(std::get<ScalarResult>(result).bound,
                               substitutions, location + ".bound");
  if (!bound.accepted())
    return {std::nullopt, bound.refusal};
  return accept(SecurityResult(ScalarResult{std::move(*bound.value)}));
}

void collectQuantityResources(const ClosedQuantity &quantity,
                              std::set<std::string> &resources) {
  for (const ResourceMonomial &term : quantity.resourceTerms)
    resources.insert(term.resource);
}

void collectBoundResources(const ClosedBound &bound,
                           std::set<std::string> &resources) {
  collectQuantityResources(bound.quantity, resources);
  for (const PrimitiveGameTerm &term : bound.primitiveGameTerms)
    for (const auto &[name, substitution] : term.resourceSubstitution) {
      (void)name;
      collectQuantityResources(substitution, resources);
    }
}

void collectResultResources(const SecurityResult &result,
                            std::set<std::string> &resources) {
  if (const auto *extraction = std::get_if<ExtractionResult>(&result)) {
    for (const ExtractionCoordinate &coordinate : extraction->coordinates) {
      collectQuantityResources(coordinate.arity, resources);
      if (coordinate.challengeSpace)
        collectQuantityResources(*coordinate.challengeSpace, resources);
    }
    if (extraction->failureBound)
      collectBoundResources(*extraction->failureBound, resources);
    return;
  }
  if (const auto *rounds = std::get_if<RoundResult>(&result)) {
    for (const RoundResultEntry &round : rounds->rounds) {
      collectQuantityResources(round.challengeSpace, resources);
      collectBoundResources(round.bound, resources);
    }
    return;
  }
  collectBoundResources(std::get<ScalarResult>(result).bound, resources);
}

bool containsAssumedJudgmentMarker(const SecurityJudgment &judgment) {
  return std::any_of(judgment.hypotheses.begin(), judgment.hypotheses.end(),
                     [](const Hypothesis &hypothesis) {
                       return std::holds_alternative<AssumedJudgmentHolds>(
                           hypothesis);
                     });
}

Step<SecurityJudgment> specializeJudgment(
    const SecurityJudgment &judgment,
    const std::map<std::string, ClosedQuantity, std::less<>> &substitutions,
    const std::vector<TypedDeclaration> &conclusionResources,
    std::set<const SecurityJudgment *> &active, const std::string &location) {
  auto specializedResult =
      substituteResult(judgment.result, substitutions, location + ".result");
  if (!specializedResult.accepted())
    return {std::nullopt, specializedResult.refusal};

  SecurityJudgment specialized;
  specialized.subject = judgment.subject;
  specialized.index = judgment.index;
  specialized.result = std::move(*specializedResult.value);
  for (size_t index = 0; index < judgment.hypotheses.size(); ++index) {
    const Hypothesis &hypothesis = judgment.hypotheses[index];
    if (const auto *proposition =
            std::get_if<PropositionInstance>(&hypothesis)) {
      specialized.hypotheses.push_back(*proposition);
      continue;
    }
    const auto &asserted =
        std::get<AssumedJudgmentHolds>(hypothesis).assertedJudgment;
    if (!asserted)
      return refuse<SecurityJudgment>(
          RuntimePhase::ResourceSpecialization,
          RuntimeRefusalCode::NullRecursiveValue,
          location + ".hypotheses[" + std::to_string(index) + "]",
          "assumed-judgment marker has a null canonical assertion");
    if (!active.insert(asserted.get()).second)
      return refuse<SecurityJudgment>(
          RuntimePhase::ResourceSpecialization,
          RuntimeRefusalCode::RecursiveCycle,
          location + ".hypotheses[" + std::to_string(index) + "]",
          "assumed-judgment marker graph is cyclic");
    if (containsAssumedJudgmentMarker(*asserted)) {
      active.erase(asserted.get());
      return refuse<SecurityJudgment>(
          RuntimePhase::ResourceSpecialization,
          RuntimeRefusalCode::UnsupportedNormalForm,
          location + ".hypotheses[" + std::to_string(index) +
              "].asserted_judgment",
          "nested assumed-judgment markers are outside the v0 binder model");
    }
    auto canonical = specializeJudgment(
        *asserted, substitutions, conclusionResources, active,
        location + ".hypotheses[" + std::to_string(index) +
            "].asserted_judgment");
    active.erase(asserted.get());
    if (!canonical.accepted())
      return canonical;
    specialized.hypotheses.push_back(AssumedJudgmentHolds{
        std::make_shared<const SecurityJudgment>(std::move(*canonical.value))});
  }

  std::set<std::string> freeResources;
  collectResultResources(specialized.result, freeResources);
  for (const Hypothesis &hypothesis : specialized.hypotheses) {
    const auto *assumed = std::get_if<AssumedJudgmentHolds>(&hypothesis);
    if (!assumed || !assumed->assertedJudgment)
      continue;
    collectResultResources(assumed->assertedJudgment->result, freeResources);
  }
  for (const TypedDeclaration &resource : conclusionResources)
    if (freeResources.count(resource.name))
      specialized.resourceVariables.push_back(resource);
  return accept(std::move(specialized));
}

Step<SecurityJudgment> specializeJudgment(
    const SecurityJudgment &judgment,
    const std::map<std::string, ClosedQuantity, std::less<>> &substitutions,
    const std::vector<TypedDeclaration> &conclusionResources,
    const std::string &location) {
  std::set<const SecurityJudgment *> active;
  active.insert(&judgment);
  return specializeJudgment(judgment, substitutions, conclusionResources,
                            active, location);
}

bool boundHasResourceSupport(const ClosedBound &bound) {
  if (!bound.quantity.resourceTerms.empty())
    return true;
  return std::any_of(
      bound.primitiveGameTerms.begin(), bound.primitiveGameTerms.end(),
      [](const PrimitiveGameTerm &term) {
        return std::any_of(term.resourceSubstitution.begin(),
                           term.resourceSubstitution.end(),
                           [](const auto &entry) {
                             return !entry.second.resourceTerms.empty();
                           });
      });
}

bool resultBoundHasResourceSupport(const SecurityResult &result) {
  if (const auto *extraction = std::get_if<ExtractionResult>(&result))
    return extraction->failureBound &&
           boundHasResourceSupport(*extraction->failureBound);
  if (const auto *rounds = std::get_if<RoundResult>(&result))
    return std::any_of(rounds->rounds.begin(), rounds->rounds.end(),
                       [](const RoundResultEntry &round) {
                         return boundHasResourceSupport(round.bound);
                       });
  return boundHasResourceSupport(std::get<ScalarResult>(result).bound);
}

Step<SecuritySubject>
authorizeApplicationSite(const SealedSoundnessView &sealed,
                         const ApplicationSite &site,
                         const RuleBinding &binding) {
  auto resolvedSubject = subjectOf(sealed, site);
  if (!resolvedSubject)
    return projectionFailure<SecuritySubject>(
        resolvedSubject.takeError(), RuntimePhase::SiteResolution,
        RuntimeRefusalCode::SiteMismatch, "apply.site");
  SecuritySubject subject;
  subject.payload = std::move(*resolvedSubject);

  if (binding.subjectSchema != kProtocolClaimSchema)
    return refuse<SecuritySubject>(
        RuntimePhase::BindingResolution, RuntimeRefusalCode::BindingMismatch,
        "apply.binding.subject_schema",
        "direct application must validate the derived protocol-claim subject");

  if (const auto *reduction = std::get_if<ReductionOccurrence>(&site)) {
    if (binding.anchor.kind != ProtocolAnchorKind::ReductionContract)
      return refuse<SecuritySubject>(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::BindingMismatch,
          "apply.binding.anchor",
          "reduction occurrence requires a reduction-contract anchor");
    auto sealedReduction = sealed.reductionsByTransformerPosition.find(
        reduction->transformerPosition);
    if (sealedReduction == sealed.reductionsByTransformerPosition.end())
      return refuse<SecuritySubject>(
          RuntimePhase::SiteResolution, RuntimeRefusalCode::SiteMismatch,
          "apply.site.transformer_position",
          "reduction occurrence names no sealed transformer");
    if (binding.anchor.ref != sealedReduction->second.contractRef)
      return refuse<SecuritySubject>(
          RuntimePhase::BindingResolution, RuntimeRefusalCode::BindingMismatch,
          "apply.binding.anchor",
          "binding contract anchor differs from the sealed reduction: sealed " +
              sealedReduction->second.contractRef.sourceRevision +
              ", binding records " + binding.anchor.ref.sourceRevision);
    return accept(std::move(subject));
  }

  if (binding.anchor.kind != ProtocolAnchorKind::PathTransition)
    return refuse<SecuritySubject>(
        RuntimePhase::BindingResolution, RuntimeRefusalCode::BindingMismatch,
        "apply.binding.anchor",
        "path occurrence requires a path-transition binding anchor");
  return accept(std::move(subject));
}

// The derivation must follow the claim graph.  At a reduction occurrence,
// every consumed claim that some transformer produced must be selected by one
// of the binding's consumed-claim premise relations, and every selected input
// position must name a consumed claim.  The containment is one-sided on
// purpose: a premise about an artifact source claim is the artifact's own
// hypothesis and stays legal.  The producer map is a fold over the sealed
// view, never a stored field, and the judgment is vacuous at a path
// occurrence, which consumes nothing.
Step<bool> checkClaimCoverage(const SealedSoundnessView &sealed,
                              const ApplicationSite &site,
                              const RuleBinding &binding) {
  const auto *occurrence = std::get_if<ReductionOccurrence>(&site);
  if (!occurrence)
    return accept(true);
  auto reduction = sealed.reductionsByTransformerPosition.find(
      occurrence->transformerPosition);
  if (reduction == sealed.reductionsByTransformerPosition.end())
    return refuse<bool>(RuntimePhase::SiteResolution,
                        RuntimeRefusalCode::SiteMismatch, "apply.coverage",
                        "reduction occurrence names no sealed transformer");
  const std::vector<ClaimRef> &inputs = reduction->second.orderedInputs;

  std::set<uint64_t> selected;
  for (const auto &[port, relation] : binding.premiseRelations) {
    switch (relation.kind) {
    case SubjectRelationKind::ConsumedClaim:
      selected.insert(relation.inputIndices.begin(),
                      relation.inputIndices.end());
      break;
    case SubjectRelationKind::ConsumedClaimVector:
      if (relation.selector == ConsumedClaimSelectorKind::AllReductionInputs) {
        for (uint64_t index = 0; index < inputs.size(); ++index)
          selected.insert(index);
      } else {
        selected.insert(relation.inputIndices.begin(),
                        relation.inputIndices.end());
      }
      break;
    case SubjectRelationKind::SameSubject:
    case SubjectRelationKind::ExactExternalSubject:
      break;
    }
  }

  auto produced = [&sealed](const ClaimRef &claim) {
    for (const auto &[position, other] : sealed.reductionsByTransformerPosition)
      for (const ClaimRef &output : other.orderedOutputs)
        if (output == claim)
          return true;
    return false;
  };

  std::set<uint64_t> uncoveredClaims;
  for (uint64_t index = 0; index < inputs.size(); ++index)
    if (!selected.count(index) && produced(inputs[index]))
      uncoveredClaims.insert(inputs[index].claimIndex);
  std::set<uint64_t> unconsumedSelections;
  for (uint64_t index : selected)
    if (index >= inputs.size())
      unconsumedSelections.insert(index);
  if (uncoveredClaims.empty() && unconsumedSelections.empty())
    return accept(true);

  std::string detail =
      "the binding's premise relations do not follow the claim graph";
  if (!uncoveredClaims.empty()) {
    detail += ": produced consumed claims outside every premise relation, in "
              "canonical claim-index order:";
    for (uint64_t claim : uncoveredClaims)
      detail += " " + std::to_string(claim);
  }
  if (!unconsumedSelections.empty()) {
    detail += uncoveredClaims.empty() ? ": " : "; ";
    detail += "selected input positions beyond the consumed-claim list:";
    for (uint64_t index : unconsumedSelections)
      detail += " " + std::to_string(index);
  }
  return refuse<bool>(RuntimePhase::PremiseResolution,
                      RuntimeRefusalCode::CoverageMismatch, "apply.coverage",
                      detail);
}

Step<bool> matchPremiseRelation(const SubjectRelation &relation,
                                const SecuritySubject &actual,
                                ApplicationEnvironment &application,
                                const std::string &location) {
  switch (relation.kind) {
  case SubjectRelationKind::SameSubject:
    if (actual != application.conclusionSubject)
      return refuse<bool>(
          RuntimePhase::PremiseResolution, RuntimeRefusalCode::PremiseMismatch,
          location, "same-subject premise differs from the conclusion subject");
    return accept(true);
  case SubjectRelationKind::ConsumedClaim: {
    const auto *site = std::get_if<ReductionOccurrence>(&application.site);
    if (!site)
      return refuse<bool>(
          RuntimePhase::PremiseResolution, RuntimeRefusalCode::PremiseMismatch,
          location, "consumed-claim relation is invalid at a path occurrence");
    auto selected = resolveReductionInput(application.sealed, *site,
                                          relation.inputIndices.front());
    if (!selected)
      return projectionFailure<bool>(
          selected.takeError(), RuntimePhase::PremiseResolution,
          RuntimeRefusalCode::PremiseMismatch, location);
    SecuritySubject expected;
    expected.payload = std::move(*selected);
    if (actual != expected)
      return refuse<bool>(RuntimePhase::PremiseResolution,
                          RuntimeRefusalCode::PremiseMismatch, location,
                          "premise subject is not the selected consumed claim");
    return accept(true);
  }
  case SubjectRelationKind::ConsumedClaimVector: {
    const auto *site = std::get_if<ReductionOccurrence>(&application.site);
    if (!site)
      return refuse<bool>(
          RuntimePhase::PremiseResolution, RuntimeRefusalCode::PremiseMismatch,
          location, "consumed-vector relation is invalid at a path occurrence");
    llvm::Expected<ConsumedClaimVectorSubject> selected =
        relation.selector == ConsumedClaimSelectorKind::AllReductionInputs
            ? resolveAllReductionInputs(application.sealed, *site)
            : resolveReductionInputs(application.sealed, *site,
                                     relation.inputIndices);
    if (!selected)
      return projectionFailure<bool>(
          selected.takeError(), RuntimePhase::PremiseResolution,
          RuntimeRefusalCode::PremiseMismatch, location);
    SecuritySubject expected;
    expected.payload = std::move(*selected);
    if (actual != expected) {
      auto render = [](const ConsumedClaimVectorSubject &subject) {
        std::string text = subject.artifactId + " consumer " +
                           std::to_string(subject.consumer.claimIndex) + ":" +
                           subject.consumer.descriptorDigest + " sources";
        for (const ClaimRef &source : subject.orderedSources)
          text += " " + std::to_string(source.claimIndex) + ":" +
                  source.descriptorDigest;
        return text;
      };
      const auto *cited =
          std::get_if<ConsumedClaimVectorSubject>(&actual.payload);
      return refuse<bool>(
          RuntimePhase::PremiseResolution, RuntimeRefusalCode::PremiseMismatch,
          location,
          "premise subject is not the exact selected consumed-claim vector: "
          "selected " +
              render(std::get<ConsumedClaimVectorSubject>(expected.payload)) +
              ", cited " +
              (cited ? render(*cited)
                     : std::string("a different subject "
                                   "shape")));
    }
    return accept(true);
  }
  case SubjectRelationKind::ExactExternalSubject: {
    const auto *external =
        std::get_if<ExternalInstanceSubject>(&actual.payload);
    if (!external || external->schemaRef != relation.externalSubjectSchema ||
        external->arguments.size() != relation.externalArguments.size())
      return refuse<bool>(
          RuntimePhase::PremiseResolution, RuntimeRefusalCode::PremiseMismatch,
          location,
          "premise is not the exact declared external subject schema/arity");
    for (size_t index = 0; index < external->arguments.size(); ++index) {
      auto matched = matchBindingValue(
          relation.externalArguments[index],
          runtimeSemantic(external->arguments[index]), application,
          location + ".arguments[" + std::to_string(index) + "]");
      if (!matched.accepted())
        return matched;
    }
    return accept(true);
  }
  }
  return refuse<bool>(RuntimePhase::PremiseResolution,
                      RuntimeRefusalCode::PremiseMismatch, location,
                      "unknown premise subject relation");
}

Step<std::map<std::string, ClosedQuantity, std::less<>>>
resolveResourceSubstitution(const PremisePort &port,
                            const ApplicationEnvironment &application,
                            const std::string &location) {
  std::map<std::string, ClosedQuantity, std::less<>> result;
  for (const TypedDeclaration &resource : port.expectedResources) {
    auto expression = port.resourceSubstitution.find(resource.name);
    if (expression == port.resourceSubstitution.end())
      return refuse<std::map<std::string, ClosedQuantity, std::less<>>>(
          RuntimePhase::ResourceSpecialization,
          RuntimeRefusalCode::InvalidResource, location,
          "premise resource substitution is not total");
    auto closed =
        evaluateClosedQuantity(expression->second, application.evaluation,
                               location + "." + resource.name);
    if (!closed.accepted())
      return {std::nullopt, closed.refusal};
    if (resource.sort == ValueSort::Integer &&
        !integerValued(*closed.value, application.evaluation.resources))
      return refuse<std::map<std::string, ClosedQuantity, std::less<>>>(
          RuntimePhase::ResourceSpecialization,
          RuntimeRefusalCode::SortMismatch, location + "." + resource.name,
          "integer premise resource has a noninteger specialization");
    result.emplace(resource.name, std::move(*closed.value));
  }
  return accept(std::move(result));
}

Step<TypedPremiseJudgments>
resolvePremises(const TypedPremiseJudgments &premises,
                ApplicationEnvironment &application) {
  if (premises.size() != application.rule.premises.size())
    return refuse<TypedPremiseJudgments>(
        RuntimePhase::PremiseResolution, RuntimeRefusalCode::PremiseMismatch,
        "apply.premises",
        "premise map does not exactly cover the binding-resolved rule ports");
  TypedPremiseJudgments specialized;
  for (const PremisePort &port : application.rule.premises) {
    auto input = premises.find(port.name);
    auto relation = application.binding.premiseRelations.find(port.name);
    if (input == premises.end() ||
        relation == application.binding.premiseRelations.end())
      return refuse<TypedPremiseJudgments>(
          RuntimePhase::PremiseResolution, RuntimeRefusalCode::PremiseMismatch,
          "apply.premises." + port.name,
          "required premise port or subject relation is absent");
    RuntimeCheckResult wellFormed = checkSecurityJudgmentWellFormed(
        application.context.schemas(), input->second,
        "apply.premises." + port.name);
    if (!wellFormed.accepted())
      return {std::nullopt, wellFormed.refusal};
    if (input->second.index != port.expectedIndex ||
        resultSchemaOf(input->second.result) != port.expectedResult ||
        !declarationsEqual(input->second.resourceVariables,
                           port.expectedResources) ||
        subjectSchemaOf(input->second.subject) != port.expectedSubjectSchema)
      return refuse<TypedPremiseJudgments>(
          RuntimePhase::PremiseResolution, RuntimeRefusalCode::PremiseMismatch,
          "apply.premises." + port.name,
          "premise index, result, resources, or subject schema differs from "
          "the exact port");
    auto relationMatch = matchPremiseRelation(
        relation->second, input->second.subject, application,
        "apply.premises." + port.name + ".subject");
    if (!relationMatch.accepted())
      return {std::nullopt, relationMatch.refusal};
    auto substitution = resolveResourceSubstitution(
        port, application,
        "apply.premises." + port.name + ".resource_substitution");
    if (!substitution.accepted())
      return {std::nullopt, substitution.refusal};
    auto closed = specializeJudgment(
        input->second, *substitution.value, application.rule.resources,
        "apply.premises." + port.name + ".specialized");
    if (!closed.accepted())
      return {std::nullopt, closed.refusal};
    if (port.resultConstraints.count(
            PremiseResultConstraint::RequiresEmptyGameSupport) &&
        !gameSupport(closed.value->result).empty())
      return refuse<TypedPremiseJudgments>(
          RuntimePhase::PremiseResolution, RuntimeRefusalCode::PremiseMismatch,
          "apply.premises." + port.name + ".result",
          "specialized premise violates the empty-game-support constraint");
    if (port.resultConstraints.count(
            PremiseResultConstraint::RequiresNoBoundResourceSupport) &&
        resultBoundHasResourceSupport(closed.value->result))
      return refuse<TypedPremiseJudgments>(
          RuntimePhase::PremiseResolution, RuntimeRefusalCode::PremiseMismatch,
          "apply.premises." + port.name + ".result",
          "specialized premise has forbidden bound resource support");
    specialized.emplace(port.name, std::move(*closed.value));
  }
  return accept(std::move(specialized));
}

Step<bool> evaluateConditions(const ApplicationEnvironment &application) {
  for (const MachineConditionTemplate &condition :
       application.rule.machineConditions) {
    auto bindings =
        application.binding.conditionArgumentBindings.find(condition.slot);
    auto definition = application.context.schemas().machineDeciders.find(
        condition.predicateRef);
    if (bindings == application.binding.conditionArgumentBindings.end() ||
        definition == application.context.schemas().machineDeciders.end())
      return refuse<bool>(
          RuntimePhase::ConditionEvaluation,
          RuntimeRefusalCode::ConditionFailed,
          "apply.conditions." + condition.slot,
          "condition has no exact binding or admitted machine decider");
    std::vector<RuntimeValue> arguments;
    for (size_t index = 0; index < bindings->second.size(); ++index) {
      auto semantic =
          resolveBindingValue(bindings->second[index], application,
                              "apply.conditions." + condition.slot +
                                  ".arguments[" + std::to_string(index) + "]");
      if (!semantic.accepted())
        return {std::nullopt, semantic.refusal};
      auto runtime = requireRuntimeValue(
          *semantic.value, "apply.conditions." + condition.slot +
                               ".arguments[" + std::to_string(index) + "]");
      if (!runtime.accepted())
        return {std::nullopt, runtime.refusal};
      arguments.push_back(std::move(*runtime.value));
    }
    auto decision = evaluateMachineDecider(definition->second.kind, arguments);
    if (!decision)
      return projectionFailure<bool>(decision.takeError(),
                                     RuntimePhase::ConditionEvaluation,
                                     RuntimeRefusalCode::ConditionFailed,
                                     "apply.conditions." + condition.slot);
    if (!*decision)
      return refuse<bool>(RuntimePhase::ConditionEvaluation,
                          RuntimeRefusalCode::ConditionFailed,
                          "apply.conditions." + condition.slot,
                          "closed machine condition evaluated to false");
  }
  return accept(true);
}

Step<std::vector<Hypothesis>>
instantiateLocalHypotheses(const ApplicationEnvironment &application) {
  std::vector<Hypothesis> result;
  for (const ExternalHypothesisTemplate &hypothesis :
       application.rule.externalHypotheses) {
    auto bindings =
        application.binding.hypothesisArgumentBindings.find(hypothesis.slot);
    auto schema = application.context.schemas().propositions.find(
        hypothesis.propositionRef);
    if (bindings == application.binding.hypothesisArgumentBindings.end() ||
        schema == application.context.schemas().propositions.end())
      return refuse<std::vector<Hypothesis>>(
          RuntimePhase::HypothesisValidation,
          RuntimeRefusalCode::InvalidProposition,
          "apply.hypotheses." + hypothesis.slot,
          "local hypothesis has no exact argument binding or proposition "
          "schema");
    PropositionInstance instance;
    instance.ref = schema->second.ref;
    for (size_t index = 0; index < bindings->second.size(); ++index) {
      auto semantic =
          resolveBindingValue(bindings->second[index], application,
                              "apply.hypotheses." + hypothesis.slot +
                                  ".arguments[" + std::to_string(index) + "]");
      if (!semantic.accepted())
        return {std::nullopt, semantic.refusal};
      auto runtime = requireRuntimeValue(
          *semantic.value, "apply.hypotheses." + hypothesis.slot +
                               ".arguments[" + std::to_string(index) + "]");
      if (!runtime.accepted())
        return {std::nullopt, runtime.refusal};
      instance.arguments.push_back(std::move(*runtime.value));
    }
    result.push_back(std::move(instance));
  }
  return accept(std::move(result));
}

void insertHypothesis(std::vector<Hypothesis> &hypotheses,
                      const Hypothesis &hypothesis) {
  if (std::none_of(hypotheses.begin(), hypotheses.end(),
                   [&](const Hypothesis &existing) {
                     return hypothesisEqual(existing, hypothesis);
                   }))
    hypotheses.push_back(hypothesis);
}

Step<const ReductionContractValue *>
contractFact(const std::string &port, const ApplicationEnvironment &application,
             const std::string &location) {
  auto fact = application.evaluation.facts.find(port);
  if (fact == application.evaluation.facts.end())
    return refuse<const ReductionContractValue *>(
        RuntimePhase::RuleEvaluation, RuntimeRefusalCode::InvalidReference,
        location, "contract-derived sequence names no resolved artifact fact");
  const auto *runtime = std::get_if<RuntimeValue>(&fact->second.payload);
  if (!runtime)
    return refuse<const ReductionContractValue *>(
        RuntimePhase::RuleEvaluation, RuntimeRefusalCode::SortMismatch,
        location, "contract-derived sequence fact is not a runtime value");
  const auto *contract = std::get_if<ReductionContractValue>(&runtime->payload);
  if (!contract)
    return refuse<const ReductionContractValue *>(
        RuntimePhase::RuleEvaluation, RuntimeRefusalCode::SortMismatch,
        location, "contract-derived sequence fact is not a contract value");
  return accept(contract);
}

bool selectorMatches(const ContractRoundSelector &selector,
                     const ReductionContractRoundValue &round) {
  switch (selector.kind) {
  case ContractRoundSelectorKind::AllContractRounds:
    return true;
  case ContractRoundSelectorKind::RoundKind:
    return round.roundKind == selector.roundKind;
  case ContractRoundSelectorKind::RoundPosition:
    return round.roundIndex.str() == std::to_string(selector.position);
  }
  return false;
}

std::string
projectContractLabel(ContractLabelProjection projection,
                     llvm::StringRef sitePrefix,
                     const ReductionContractRoundValue &round,
                     const std::vector<ReductionContractRoundValue> &rounds,
                     size_t position, llvm::StringRef caseName) {
  if (projection == ContractLabelProjection::RoundIndex)
    return round.roundIndex.str();
  // A contract-local index repeats at every occurrence of that contract, so a
  // row that composes two of them needs a label that separates the two.  The
  // canonical transformer position is the occurrence's own identity, and no
  // other projection can produce it.
  if (projection == ContractLabelProjection::SiteQualifiedRoundIndex)
    return sitePrefix.str() + ":" + round.roundIndex.str();
  if (projection == ContractLabelProjection::CaseName)
    return caseName.str();
  size_t occurrence = 0;
  for (size_t index = 0; index < position; ++index)
    if (rounds[index].roundKind == round.roundKind)
      ++occurrence;
  return round.roundKind + "#" + std::to_string(occurrence);
}

/// The prefix a site-qualified label carries.  Empty at a path occurrence,
/// where a contract fact cannot resolve anyway; the caller refuses rather than
/// letting a label degenerate to a bare separator.
std::string labelSitePrefix(const ApplicationSite &site) {
  if (const auto *occurrence = std::get_if<ReductionOccurrence>(&site))
    return std::to_string(occurrence->transformerPosition);
  return {};
}

template <typename Case>
Step<std::vector<std::pair<const ReductionContractRoundValue *, const Case *>>>
matchContractCases(const ReductionContractValue &contract,
                   const std::vector<Case> &cases,
                   const std::string &location) {
  std::vector<bool> used(cases.size(), false);
  std::vector<std::pair<const ReductionContractRoundValue *, const Case *>>
      result;
  for (size_t roundIndex = 0; roundIndex < contract.rounds.size();
       ++roundIndex) {
    const ReductionContractRoundValue &round = contract.rounds[roundIndex];
    const Case *matched = nullptr;
    size_t matchedIndex = 0;
    for (size_t caseIndex = 0; caseIndex < cases.size(); ++caseIndex) {
      if (!selectorMatches(cases[caseIndex].selector, round))
        continue;
      if (matched)
        return refuse<std::vector<
            std::pair<const ReductionContractRoundValue *, const Case *>>>(
            RuntimePhase::RuleEvaluation, RuntimeRefusalCode::InvalidPayload,
            location + ".rounds[" + std::to_string(roundIndex) + "]",
            "authenticated contract round matches more than one sequence "
            "case");
      matched = &cases[caseIndex];
      matchedIndex = caseIndex;
    }
    if (!matched)
      return refuse<std::vector<
          std::pair<const ReductionContractRoundValue *, const Case *>>>(
          RuntimePhase::RuleEvaluation, RuntimeRefusalCode::InvalidPayload,
          location + ".rounds[" + std::to_string(roundIndex) + "]",
          "authenticated contract round matches no sequence case");
    used[matchedIndex] = true;
    result.emplace_back(&round, matched);
  }
  for (size_t index = 0; index < used.size(); ++index)
    if (!used[index])
      return refuse<std::vector<
          std::pair<const ReductionContractRoundValue *, const Case *>>>(
          RuntimePhase::RuleEvaluation, RuntimeRefusalCode::InvalidPayload,
          location + ".cases[" + std::to_string(index) + "]",
          "contract-derived sequence case matches no authenticated round");
  return accept(std::move(result));
}

Step<std::vector<ExtractionCoordinate>>
resolveCoordinates(const CoordinateSequence &sequence,
                   ApplicationEnvironment &application,
                   const std::string &location) {
  std::vector<ExtractionCoordinate> result;
  if (sequence.kind == CoordinateSequence::Kind::Explicit) {
    for (size_t index = 0; index < sequence.coordinates.size(); ++index) {
      const CoordinateTemplate &coordinate = sequence.coordinates[index];
      ExtractionCoordinate output;
      output.label = coordinate.label;
      auto arity = evaluateClosedQuantity(
          coordinate.arity, application.evaluation,
          location + ".coordinates[" + std::to_string(index) + "].arity");
      if (!arity.accepted())
        return {std::nullopt, arity.refusal};
      if (!integerValued(*arity.value, application.evaluation.resources))
        return refuse<std::vector<ExtractionCoordinate>>(
            RuntimePhase::RuleEvaluation, RuntimeRefusalCode::ArithmeticDomain,
            location + ".coordinates[" + std::to_string(index) + "].arity",
            "extraction arity is not integer-valued");
      output.arity = std::move(*arity.value);
      if (coordinate.challengeSpace) {
        auto space = evaluateClosedQuantity(
            *coordinate.challengeSpace, application.evaluation,
            location + ".coordinates[" + std::to_string(index) +
                "].challenge_space");
        if (!space.accepted())
          return {std::nullopt, space.refusal};
        if (!integerValued(*space.value, application.evaluation.resources))
          return refuse<std::vector<ExtractionCoordinate>>(
              RuntimePhase::RuleEvaluation,
              RuntimeRefusalCode::ArithmeticDomain,
              location + ".coordinates[" + std::to_string(index) +
                  "].challenge_space",
              "challenge space is not integer-valued");
        output.challengeSpace = std::move(*space.value);
      }
      result.push_back(std::move(output));
    }
  } else {
    auto contract = contractFact(sequence.contractFactPort, application,
                                 location + ".contract_fact");
    if (!contract.accepted())
      return {std::nullopt, contract.refusal};
    auto matches =
        matchContractCases(**contract.value, sequence.cases, location);
    if (!matches.accepted())
      return {std::nullopt, matches.refusal};
    // A site-qualified label needs the occurrence's identity.  A contract
    // fact only resolves at a reduction occurrence, so this is unreachable
    // today; without it the label would degenerate to a bare separator
    // silently, and the projector is a free function that cannot see the site.
    const std::string sitePrefix = labelSitePrefix(application.site);
    if (sitePrefix.empty() &&
        llvm::any_of(sequence.cases, [](const auto &value) {
          return value.labelProjection ==
                 ContractLabelProjection::SiteQualifiedRoundIndex;
        }))
      return refuse<std::vector<ExtractionCoordinate>>(
          RuntimePhase::RuleEvaluation, RuntimeRefusalCode::PremiseMismatch,
          location,
          "a site-qualified round index needs a reduction occurrence");
    for (size_t index = 0; index < matches.value->size(); ++index) {
      const auto &[round, selectedCase] = (*matches.value)[index];
      EvaluationEnvironment lexical = application.evaluation;
      lexical.currentRound = round;
      lexical.currentRoundCase = selectedCase->caseName;
      ExtractionCoordinate output;
      output.label = projectContractLabel(
          selectedCase->labelProjection, sitePrefix, *round,
          (*contract.value)->rounds, index, selectedCase->caseName);
      auto arity = evaluateClosedQuantity(
          selectedCase->arity, lexical,
          location + ".resolved[" + std::to_string(index) + "].arity");
      if (!arity.accepted())
        return {std::nullopt, arity.refusal};
      if (!integerValued(*arity.value, lexical.resources))
        return refuse<std::vector<ExtractionCoordinate>>(
            RuntimePhase::RuleEvaluation, RuntimeRefusalCode::ArithmeticDomain,
            location + ".resolved[" + std::to_string(index) + "].arity",
            "contract-derived extraction arity is not integer-valued");
      output.arity = std::move(*arity.value);
      if (selectedCase->challengeSpace) {
        auto space = evaluateClosedQuantity(
            *selectedCase->challengeSpace, lexical,
            location + ".resolved[" + std::to_string(index) +
                "].challenge_space");
        if (!space.accepted())
          return {std::nullopt, space.refusal};
        if (!integerValued(*space.value, lexical.resources))
          return refuse<std::vector<ExtractionCoordinate>>(
              RuntimePhase::RuleEvaluation,
              RuntimeRefusalCode::ArithmeticDomain,
              location + ".resolved[" + std::to_string(index) +
                  "].challenge_space",
              "contract-derived challenge space is not integer-valued");
        output.challengeSpace = std::move(*space.value);
      }
      result.push_back(std::move(output));
    }
  }
  if (result.empty())
    return refuse<std::vector<ExtractionCoordinate>>(
        RuntimePhase::RuleEvaluation, RuntimeRefusalCode::EmptyCollection,
        location, "coordinate sequence resolved to an empty result");
  std::set<std::string> labels;
  for (const ExtractionCoordinate &coordinate : result)
    if (coordinate.label.empty() || !labels.insert(coordinate.label).second)
      return refuse<std::vector<ExtractionCoordinate>>(
          RuntimePhase::RuleEvaluation, RuntimeRefusalCode::DuplicateName,
          location, "coordinate sequence resolved duplicate/empty labels");
  return accept(std::move(result));
}

Step<std::vector<RoundResultEntry>>
resolveRounds(const RoundSequence &sequence,
              ApplicationEnvironment &application,
              const std::string &location) {
  std::vector<RoundResultEntry> result;
  if (sequence.kind == RoundSequence::Kind::Explicit) {
    for (size_t index = 0; index < sequence.rounds.size(); ++index) {
      const RoundTemplate &round = sequence.rounds[index];
      RoundResultEntry output;
      output.roundIndex = round.roundIndex;
      auto space = evaluateClosedQuantity(
          round.challengeSpace, application.evaluation,
          location + ".rounds[" + std::to_string(index) + "].challenge_space");
      if (!space.accepted())
        return {std::nullopt, space.refusal};
      if (!integerValued(*space.value, application.evaluation.resources))
        return refuse<std::vector<RoundResultEntry>>(
            RuntimePhase::RuleEvaluation, RuntimeRefusalCode::ArithmeticDomain,
            location + ".rounds[" + std::to_string(index) + "].challenge_space",
            "round challenge space is not integer-valued");
      output.challengeSpace = std::move(*space.value);
      auto bound = closeRuleBound(
          round.bound, application, application.evaluation,
          location + ".rounds[" + std::to_string(index) + "].bound");
      if (!bound.accepted())
        return {std::nullopt, bound.refusal};
      output.bound = std::move(*bound.value);
      result.push_back(std::move(output));
    }
  } else {
    auto contract = contractFact(sequence.contractFactPort, application,
                                 location + ".contract_fact");
    if (!contract.accepted())
      return {std::nullopt, contract.refusal};
    auto matches =
        matchContractCases(**contract.value, sequence.cases, location);
    if (!matches.accepted())
      return {std::nullopt, matches.refusal};
    // A site-qualified label needs the occurrence's identity.  A contract
    // fact only resolves at a reduction occurrence, so this is unreachable
    // today; without it the label would degenerate to a bare separator
    // silently, and the projector is a free function that cannot see the site.
    const std::string sitePrefix = labelSitePrefix(application.site);
    if (sitePrefix.empty() &&
        llvm::any_of(sequence.cases, [](const auto &value) {
          return value.indexProjection ==
                 ContractLabelProjection::SiteQualifiedRoundIndex;
        }))
      return refuse<std::vector<RoundResultEntry>>(
          RuntimePhase::RuleEvaluation, RuntimeRefusalCode::PremiseMismatch,
          location,
          "a site-qualified round index needs a reduction occurrence");
    for (size_t index = 0; index < matches.value->size(); ++index) {
      const auto &[round, selectedCase] = (*matches.value)[index];
      EvaluationEnvironment lexical = application.evaluation;
      lexical.currentRound = round;
      lexical.currentRoundCase = selectedCase->caseName;
      RoundResultEntry output;
      output.roundIndex = projectContractLabel(
          selectedCase->indexProjection, sitePrefix, *round,
          (*contract.value)->rounds, index, selectedCase->caseName);
      auto space = evaluateClosedQuantity(selectedCase->challengeSpace, lexical,
                                          location + ".resolved[" +
                                              std::to_string(index) +
                                              "].challenge_space");
      if (!space.accepted())
        return {std::nullopt, space.refusal};
      if (!integerValued(*space.value, lexical.resources))
        return refuse<std::vector<RoundResultEntry>>(
            RuntimePhase::RuleEvaluation, RuntimeRefusalCode::ArithmeticDomain,
            location + ".resolved[" + std::to_string(index) +
                "].challenge_space",
            "contract-derived challenge space is not integer-valued");
      output.challengeSpace = std::move(*space.value);
      auto bound = closeRuleBound(selectedCase->bound, application, lexical,
                                  location + ".resolved[" +
                                      std::to_string(index) + "].bound");
      if (!bound.accepted())
        return {std::nullopt, bound.refusal};
      output.bound = std::move(*bound.value);
      result.push_back(std::move(output));
    }
  }
  if (result.empty())
    return refuse<std::vector<RoundResultEntry>>(
        RuntimePhase::RuleEvaluation, RuntimeRefusalCode::EmptyCollection,
        location, "round sequence resolved to an empty result");
  std::set<std::string> indices;
  for (const RoundResultEntry &round : result)
    if (round.roundIndex.empty() || !indices.insert(round.roundIndex).second)
      return refuse<std::vector<RoundResultEntry>>(
          RuntimePhase::RuleEvaluation, RuntimeRefusalCode::DuplicateName,
          location, "round sequence resolved duplicate/empty indices");
  return accept(std::move(result));
}

Step<SecurityResult> evaluateRuleBody(ApplicationEnvironment &application) {
  return std::visit(
      [&](const auto &body) -> Step<SecurityResult> {
        using T = std::decay_t<decltype(body)>;
        if constexpr (std::is_same_v<T, SpecialSoundnessEntry>) {
          auto coordinates = resolveCoordinates(body.coordinates, application,
                                                "apply.body.coordinates");
          if (!coordinates.accepted())
            return {std::nullopt, coordinates.refusal};
          return accept(SecurityResult(
              ExtractionResult{std::move(*coordinates.value), std::nullopt}));
        } else if constexpr (std::is_same_v<T, NativeRoundByRoundEntry>) {
          auto rounds =
              resolveRounds(body.rounds, application, "apply.body.rounds");
          if (!rounds.accepted())
            return {std::nullopt, rounds.refusal};
          return accept(SecurityResult(RoundResult{std::move(*rounds.value)}));
        } else if constexpr (std::is_same_v<T, ComputationalEntry>) {
          auto coordinates = resolveCoordinates(body.coordinates, application,
                                                "apply.body.coordinates");
          if (!coordinates.accepted())
            return {std::nullopt, coordinates.refusal};
          auto failure = closeRuleBound(body.failureBound, application,
                                        application.evaluation,
                                        "apply.body.failure_bound");
          if (!failure.accepted())
            return {std::nullopt, failure.refusal};
          return accept(SecurityResult(ExtractionResult{
              std::move(*coordinates.value), std::move(*failure.value)}));
        } else if constexpr (std::is_same_v<T, CompletenessEntry>) {
          auto bound =
              closeRuleBound(body.bound, application, application.evaluation,
                             "apply.body.bound");
          if (!bound.accepted())
            return {std::nullopt, bound.refusal};
          return accept(SecurityResult(ScalarResult{std::move(*bound.value)}));
        } else if constexpr (std::is_same_v<T, SpecialSoundnessPreservation>) {
          auto premise = application.evaluation.premises.find(body.sourcePort);
          if (premise == application.evaluation.premises.end())
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::InvalidReference, "apply.body.source_port",
                "preservation body names no specialized source premise");
          const auto *source =
              std::get_if<ExtractionResult>(&premise->second->result);
          if (!source || source->failureBound)
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::InvalidResultSchema,
                "apply.body.source_port",
                "preservation source is not information-theoretic special "
                "soundness");
          auto appended =
              resolveCoordinates(body.appendedCoordinates, application,
                                 "apply.body.appended_coordinates");
          if (!appended.accepted())
            return {std::nullopt, appended.refusal};
          std::vector<ExtractionCoordinate> coordinates = source->coordinates;
          coordinates.insert(coordinates.end(), appended.value->begin(),
                             appended.value->end());
          std::set<std::string> labels;
          for (const ExtractionCoordinate &coordinate : coordinates)
            if (!labels.insert(coordinate.label).second)
              return refuse<SecurityResult>(
                  RuntimePhase::RuleEvaluation,
                  RuntimeRefusalCode::DuplicateName, "apply.body.coordinates",
                  "preservation appends a duplicate extraction coordinate");
          auto failure = closeRuleBound(body.conclusionFailureBound,
                                        application, application.evaluation,
                                        "apply.body.conclusion_failure_bound");
          if (!failure.accepted())
            return {std::nullopt, failure.refusal};
          return accept(SecurityResult(ExtractionResult{
              std::move(coordinates), std::move(*failure.value)}));
        } else if constexpr (std::is_same_v<T, RoundByRoundPreservation>) {
          auto premise = application.evaluation.premises.find(body.sourcePort);
          if (premise == application.evaluation.premises.end())
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::InvalidReference, "apply.body.source_port",
                "preservation body names no round-by-round source premise");
          const auto *source =
              std::get_if<RoundResult>(&premise->second->result);
          if (!source)
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::InvalidResultSchema,
                "apply.body.source_port",
                "preservation source is not a round-by-round result");

          // The composition this body performs is stated over a transcript
          // whose components occupy contiguous blocks in spine order.  A claim
          // edge does not imply that: the spine and the claim graph are
          // independent, and bodies may interleave (docs/spec/kernel.md §1.4).
          // So both spans are checked here rather than assumed
          // (docs/spec/soundness.md §5.1).
          const auto *occurrence =
              std::get_if<ReductionOccurrence>(&application.site);
          if (!occurrence)
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::PremiseMismatch, "apply.body.rounds",
                "round-by-round preservation is invalid at a path occurrence");
          auto later = application.sealed.reductionsByTransformerPosition.find(
              occurrence->transformerPosition);
          if (later ==
                  application.sealed.reductionsByTransformerPosition.end() ||
              later->second.rounds.empty())
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::PremiseMismatch, "apply.body.rounds",
                "the conclusion occurrence contributes no rounds to compose");

          // The producing occurrence of the premise's own subject, folded out
          // of the sealed view rather than stored: the view already determines
          // it, and a second copy would be a second authority for one fact.
          const auto *premiseSubject = std::get_if<ProtocolClaimSubject>(
              &premise->second->subject.payload);
          const SealedReduction *earlier = nullptr;
          if (premiseSubject)
            for (const auto &[position, reduction] :
                 application.sealed.reductionsByTransformerPosition)
              if (llvm::is_contained(reduction.orderedOutputs,
                                     premiseSubject->claim))
                earlier = &reduction;
          if (!earlier || earlier->rounds.empty())
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::PremiseMismatch, "apply.body.rounds",
                "the premise names no producing reduction with rounds on this "
                "spine, so its transcript block is not one this composition "
                "can order");

          const uint64_t spanBegin =
              earlier->rounds.front().challengeEventPosition;
          const uint64_t spanEnd =
              later->second.rounds.back().challengeEventPosition;
          if (earlier->rounds.back().challengeEventPosition >=
              later->second.rounds.front().challengeEventPosition)
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::PremiseMismatch, "apply.body.rounds",
                "the premise occurrence does not precede the conclusion "
                "occurrence in the spine");

          // Every challenge inside the composed span belongs to one of the two
          // occurrences.  An unowned challenge between them is one the
          // composed error function does not index, and leaving it uncounted
          // would price a protocol that is not the one composed.
          if (!application.sealed.duplex)
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::ConditionFailed, "apply.body.rounds",
                "composing round-by-round spans needs the artifact's squeeze "
                "facts, which this artifact does not carry");
          std::set<uint64_t> composed;
          for (const SealedRoundFact &round : earlier->rounds)
            composed.insert(round.challengeEventPosition);
          for (const SealedRoundFact &round : later->second.rounds)
            composed.insert(round.challengeEventPosition);
          for (const SealedChallengeCodecFact &challenge :
               application.sealed.duplex->challenges)
            if (challenge.eventPosition >= spanBegin &&
                challenge.eventPosition <= spanEnd &&
                !composed.count(challenge.eventPosition))
              return refuse<SecurityResult>(
                  RuntimePhase::RuleEvaluation,
                  RuntimeRefusalCode::ConditionFailed, "apply.body.rounds",
                  "a challenge inside the composed span belongs to neither "
                  "occurrence, so the composed error function does not index "
                  "it");

          auto appended = resolveRounds(body.appendedRounds, application,
                                        "apply.body.appended_rounds");
          if (!appended.accepted())
            return {std::nullopt, appended.refusal};
          std::vector<RoundResultEntry> rounds = source->rounds;
          rounds.insert(rounds.end(), appended.value->begin(),
                        appended.value->end());
          std::set<std::string> indices;
          for (const RoundResultEntry &round : rounds)
            if (!indices.insert(round.roundIndex).second)
              return refuse<SecurityResult>(
                  RuntimePhase::RuleEvaluation,
                  RuntimeRefusalCode::DuplicateName, "apply.body.rounds",
                  "preservation appends a duplicate round index; a row that "
                  "composes two occurrences of one contract needs a "
                  "site-qualified index projection");
          return accept(SecurityResult(RoundResult{std::move(rounds)}));
        } else if constexpr (std::is_same_v<T, RoundScaling>) {
          auto premise =
              application.evaluation.premises.find(body.roundByRoundPort);
          if (premise == application.evaluation.premises.end())
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::InvalidReference,
                "apply.body.round_by_round_port",
                "round-scaling body names no specialized premise");
          const auto *source =
              std::get_if<RoundResult>(&premise->second->result);
          if (!source)
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::InvalidResultSchema,
                "apply.body.round_by_round_port",
                "round-scaling source is not a round result");
          std::optional<size_t> selectedPosition;
          std::string selectedLabel;
          if (body.selectedRound.kind == RoundSelectorKind::ByRoundIndex) {
            selectedLabel = body.selectedRound.exactRoundIndex;
          } else {
            auto fact = application.evaluation.facts.find(
                body.selectedRound.adjacencyFactPort);
            if (fact == application.evaluation.facts.end())
              return refuse<SecurityResult>(
                  RuntimePhase::RuleEvaluation,
                  RuntimeRefusalCode::InvalidReference,
                  "apply.body.selected_round",
                  "adjacent selector names no authenticated fact");
            auto runtime =
                requireRuntimeValue(fact->second, "apply.body.selected_round");
            if (!runtime.accepted())
              return {std::nullopt, runtime.refusal};
            const auto *adjacency =
                std::get_if<RoundAdjacencyValue>(&runtime.value->payload);
            if (!adjacency)
              return refuse<SecurityResult>(
                  RuntimePhase::RuleEvaluation,
                  RuntimeRefusalCode::SortMismatch, "apply.body.selected_round",
                  "adjacent selector fact is not round adjacency");
            const auto *premiseSubject = std::get_if<ProtocolClaimSubject>(
                &premise->second->subject.payload);
            if (!premiseSubject ||
                premiseSubject->artifactId != application.sealed.artifactId ||
                premiseSubject->claim != adjacency->premiseClaim)
              return refuse<SecurityResult>(
                  RuntimePhase::RuleEvaluation,
                  RuntimeRefusalCode::PremiseMismatch,
                  "apply.body.selected_round",
                  "authenticated adjacency is not tied to the exact consumed "
                  "round-by-round premise");
            if (adjacency->premiseRoundPosition >= source->rounds.size())
              return refuse<SecurityResult>(
                  RuntimePhase::RuleEvaluation,
                  RuntimeRefusalCode::InvalidReference,
                  "apply.body.selected_round",
                  "authenticated predecessor-round ordinal is out of range");
            // The ordinal is a position in the premise reduction's own contract
            // round list, so it selects the intended round only while the
            // premise result is that reduction's rounds one for one.  A
            // composed premise is longer, the range check above passes, and the
            // scale would land on some other component's round in silence
            // (docs/spec/soundness.md, the round-scaling body).
            auto premiseOccurrence =
                application.sealed.reductionsByTransformerPosition.find(
                    adjacency->premiseTransformerPosition);
            if (premiseOccurrence ==
                    application.sealed.reductionsByTransformerPosition.end() ||
                premiseOccurrence->second.rounds.size() !=
                    source->rounds.size())
              return refuse<SecurityResult>(
                  RuntimePhase::RuleEvaluation,
                  RuntimeRefusalCode::PremiseMismatch,
                  "apply.body.selected_round",
                  "the adjacency ordinal needs a premise result that is the "
                  "premise reduction's own rounds one for one");
            selectedPosition =
                static_cast<size_t>(adjacency->premiseRoundPosition);
          }
          auto scale = evaluateClosedQuantity(
              body.scale, application.evaluation, "apply.body.scale");
          if (!scale.accepted())
            return {std::nullopt, scale.refusal};
          RoundResult result = *source;
          size_t selectedCount = 0;
          if (selectedPosition) {
            auto scaled = scaleClosedBound(
                *scale.value, result.rounds[*selectedPosition].bound,
                "apply.body.scaled_round");
            if (!scaled.accepted())
              return {std::nullopt, scaled.refusal};
            result.rounds[*selectedPosition].bound = std::move(*scaled.value);
            selectedCount = 1;
          } else {
            for (RoundResultEntry &round : result.rounds) {
              if (round.roundIndex != selectedLabel)
                continue;
              ++selectedCount;
              auto scaled = scaleClosedBound(*scale.value, round.bound,
                                             "apply.body.scaled_round");
              if (!scaled.accepted())
                return {std::nullopt, scaled.refusal};
              round.bound = std::move(*scaled.value);
            }
          }
          if (selectedCount != 1)
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::InvalidReference,
                "apply.body.selected_round",
                "round selector did not resolve exactly one premise round");
          return accept(SecurityResult(std::move(result)));
        } else if constexpr (std::is_same_v<T,
                                            SpecialSoundnessToRoundByRound>) {
          auto premise =
              application.evaluation.premises.find(body.specialSoundnessPort);
          if (premise == application.evaluation.premises.end())
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::InvalidReference,
                "apply.body.special_soundness_port",
                "SS-to-RBR body names no specialized premise");
          const auto *source =
              std::get_if<ExtractionResult>(&premise->second->result);
          if (!source)
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::InvalidResultSchema,
                "apply.body.special_soundness_port",
                "SS-to-RBR source is not an extraction result");
          RoundResult result;
          for (size_t index = 0; index < source->coordinates.size(); ++index) {
            const ExtractionCoordinate &coordinate = source->coordinates[index];
            if (!coordinate.challengeSpace)
              return refuse<SecurityResult>(
                  RuntimePhase::RuleEvaluation,
                  RuntimeRefusalCode::InvalidPayload,
                  "apply.body.coordinates[" + std::to_string(index) + "]",
                  "SS-to-RBR source coordinate has no challenge space");
            EvaluationEnvironment lexical = application.evaluation;
            lexical.currentCoordinate = &coordinate;
            auto bound = closeRuleBound(
                body.perCoordinateBound, application, lexical,
                "apply.body.coordinates[" + std::to_string(index) + "].bound");
            if (!bound.accepted())
              return {std::nullopt, bound.refusal};
            result.rounds.push_back({coordinate.label,
                                     *coordinate.challengeSpace,
                                     std::move(*bound.value)});
          }
          return accept(SecurityResult(std::move(result)));
        } else if constexpr (std::is_same_v<T,
                                            RoundByRoundToStateRestoration>) {
          auto premise =
              application.evaluation.premises.find(body.roundByRoundPort);
          if (premise == application.evaluation.premises.end())
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::InvalidReference,
                "apply.body.round_by_round_port",
                "RBR-to-SR body names no specialized premise");
          const auto *source =
              std::get_if<RoundResult>(&premise->second->result);
          if (!source)
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::InvalidResultSchema,
                "apply.body.round_by_round_port",
                "RBR-to-SR source is not a round result");
          std::vector<ClosedBound> bounds;
          for (const RoundResultEntry &round : source->rounds)
            bounds.push_back(round.bound);
          auto maximum =
              maximumClosedBounds(bounds, "apply.body.round_maximum");
          if (!maximum.accepted())
            return {std::nullopt, maximum.refusal};
          auto budget =
              evaluateClosedQuantity(body.moveBudget, application.evaluation,
                                     "apply.body.move_budget");
          if (!budget.accepted())
            return {std::nullopt, budget.refusal};
          auto scaled = scaleClosedBound(*budget.value, *maximum.value,
                                         "apply.body.scalar_bound");
          if (!scaled.accepted())
            return {std::nullopt, scaled.refusal};
          return accept(SecurityResult(ScalarResult{std::move(*scaled.value)}));
        } else {
          auto premise =
              application.evaluation.premises.find(body.stateRestorationPort);
          if (premise == application.evaluation.premises.end())
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::InvalidReference,
                "apply.body.state_restoration_port",
                "SR-to-FS body names no specialized premise");
          const auto *source =
              std::get_if<ScalarResult>(&premise->second->result);
          if (!source)
            return refuse<SecurityResult>(
                RuntimePhase::RuleEvaluation,
                RuntimeRefusalCode::InvalidResultSchema,
                "apply.body.state_restoration_port",
                "SR-to-FS source is not a scalar result");
          auto local = closeRuleBound(body.localDuplexBound, application,
                                      application.evaluation,
                                      "apply.body.local_duplex_bound");
          if (!local.accepted())
            return {std::nullopt, local.refusal};
          auto sum = addClosedBounds(source->bound, *local.value,
                                     "apply.body.scalar_bound");
          if (!sum.accepted())
            return {std::nullopt, sum.refusal};
          return accept(SecurityResult(ScalarResult{std::move(*sum.value)}));
        }
      },
      application.rule.body);
}

const SecurityJudgment &conclusionOf(const EvaluatedDerivation &derivation) {
  if (const auto *assumed = std::get_if<EvaluatedAssumption>(&derivation.node))
    return assumed->conclusion;
  return std::get<EvaluatedApplication>(derivation.node).conclusion;
}

Step<EvaluatedDerivation>
evaluatePlanNode(const SoundnessContext &context,
                 const SealedSoundnessView &sealed, const DerivationPlan &plan,
                 std::set<const DerivationPlan *> &active,
                 const std::string &location) {
  if (!active.insert(&plan).second)
    return refuse<EvaluatedDerivation>(
        RuntimePhase::Derivation, RuntimeRefusalCode::RecursiveCycle, location,
        "derivation plan graph contains an active-pointer cycle");

  if (const auto *assumption =
          std::get_if<ExternalJudgmentAssumption>(&plan.node)) {
    if (containsAssumedJudgmentMarker(assumption->assertedJudgment)) {
      active.erase(&plan);
      return refuse<EvaluatedDerivation>(
          RuntimePhase::Derivation, RuntimeRefusalCode::InvalidPayload,
          location + ".assumption.input.hypotheses",
          "an external assumption input must be marker-free; only DERIVE may "
          "synthesize AssumedJudgmentHolds");
    }
    RuntimeCheckResult wellFormed = checkSecurityJudgmentWellFormed(
        context.schemas(), assumption->assertedJudgment,
        location + ".assumption.input");
    if (!wellFormed.accepted()) {
      active.erase(&plan);
      return {std::nullopt, wellFormed.refusal};
    }
    SecurityJudgment conclusion = assumption->assertedJudgment;
    Hypothesis marker = AssumedJudgmentHolds{
        std::make_shared<const SecurityJudgment>(assumption->assertedJudgment)};
    insertHypothesis(conclusion.hypotheses, marker);
    RuntimeCheckResult conclusionCheck = checkSecurityJudgmentWellFormed(
        context.schemas(), conclusion, location + ".assumption.conclusion");
    if (!conclusionCheck.accepted()) {
      active.erase(&plan);
      return {std::nullopt, conclusionCheck.refusal};
    }
    EvaluatedDerivation result;
    result.node = EvaluatedAssumption{assumption->assertedJudgment,
                                      std::move(conclusion)};
    active.erase(&plan);
    return accept(std::move(result));
  }

  const auto &application = std::get<ApplyDerivationPlan>(plan.node);
  TypedPremiseJudgments judgments;
  std::map<std::string, std::shared_ptr<const EvaluatedDerivation>, std::less<>>
      evaluatedPremises;
  for (const auto &[port, child] : application.premises) {
    if (!child) {
      active.erase(&plan);
      return refuse<EvaluatedDerivation>(
          RuntimePhase::Derivation, RuntimeRefusalCode::NullRecursiveValue,
          location + ".premises." + port,
          "derivation plan contains a null premise child");
    }
    auto evaluated = evaluatePlanNode(context, sealed, *child, active,
                                      location + ".premises." + port);
    if (!evaluated.accepted()) {
      active.erase(&plan);
      return evaluated;
    }
    judgments.emplace(port, conclusionOf(*evaluated.value));
    evaluatedPremises.emplace(port, std::make_shared<const EvaluatedDerivation>(
                                        std::move(*evaluated.value)));
  }
  ApplyOutcome applied = applySoundnessRule(context, sealed, application.site,
                                            application.bindingRef, judgments);
  if (!applied.accepted()) {
    active.erase(&plan);
    return {std::nullopt, applied.refusal};
  }
  EvaluatedDerivation result;
  result.node = EvaluatedApplication{application.site, application.bindingRef,
                                     std::move(evaluatedPremises),
                                     std::move(applied.applied->conclusion)};
  active.erase(&plan);
  return accept(std::move(result));
}

ClosedBoundOperationResult
finishClosedBoundOperation(Step<ClosedBound> operation,
                           const std::string &location) {
  if (!operation.accepted())
    return {std::move(operation.value), std::move(operation.refusal)};
  RuntimeCheckResult check =
      checkClosedBoundWellFormed(*operation.value, location + ".result");
  if (!check.accepted())
    return {std::nullopt, std::move(check.refusal)};
  return {std::move(operation.value), std::nullopt};
}

} // namespace

ClosedBoundOperationResult closedBoundSpecialize(
    const ClosedBound &bound,
    const std::map<std::string, ClosedQuantity, std::less<>> &substitutions,
    std::string location) {
  RuntimeCheckResult boundCheck =
      checkClosedBoundWellFormed(bound, location + ".input");
  if (!boundCheck.accepted())
    return {std::nullopt, boundCheck.refusal};
  for (const auto &[resource, quantity] : substitutions) {
    if (resource.empty())
      return {std::nullopt,
              makeRefusal(RuntimePhase::ResourceSpecialization,
                          RuntimeRefusalCode::InvalidResource,
                          location + ".substitutions",
                          "resource substitution has an empty source name")};
    RuntimeCheckResult quantityCheck = checkClosedQuantityWellFormed(
        quantity, location + ".substitutions." + resource);
    if (!quantityCheck.accepted())
      return {std::nullopt, quantityCheck.refusal};
  }
  Step<ClosedBound> specialized =
      substituteBound(bound, substitutions, location);
  return finishClosedBoundOperation(std::move(specialized), location);
}

ClosedBoundOperationResult closedBoundAdd(const ClosedBound &lhs,
                                          const ClosedBound &rhs,
                                          std::string location) {
  RuntimeCheckResult left = checkClosedBoundWellFormed(lhs, location + ".left");
  if (!left.accepted())
    return {std::nullopt, left.refusal};
  RuntimeCheckResult right =
      checkClosedBoundWellFormed(rhs, location + ".right");
  if (!right.accepted())
    return {std::nullopt, right.refusal};
  Step<ClosedBound> sum = addClosedBounds(lhs, rhs, location);
  return finishClosedBoundOperation(std::move(sum), location);
}

ClosedBoundOperationResult
closedBoundMaximum(const std::vector<ClosedBound> &bounds,
                   std::string location) {
  for (size_t index = 0; index < bounds.size(); ++index) {
    RuntimeCheckResult check = checkClosedBoundWellFormed(
        bounds[index], location + ".operands[" + std::to_string(index) + "]");
    if (!check.accepted())
      return {std::nullopt, check.refusal};
  }
  Step<ClosedBound> maximum = maximumClosedBounds(bounds, location);
  return finishClosedBoundOperation(std::move(maximum), location);
}

ClosedBoundOperationResult closedBoundScale(const ClosedQuantity &scale,
                                            const ClosedBound &bound,
                                            std::string location) {
  RuntimeCheckResult scaleCheck =
      checkClosedQuantityWellFormed(scale, location + ".factor");
  if (!scaleCheck.accepted())
    return {std::nullopt, scaleCheck.refusal};
  RuntimeCheckResult boundCheck =
      checkClosedBoundWellFormed(bound, location + ".operand");
  if (!boundCheck.accepted())
    return {std::nullopt, boundCheck.refusal};
  Step<ClosedBound> scaled = scaleClosedBound(scale, bound, location);
  return finishClosedBoundOperation(std::move(scaled), location);
}

ClosedBoundComparisonResult closedBoundLeq(const ClosedBound &candidate,
                                           const ClosedBound &ceiling,
                                           std::string location) {
  RuntimeCheckResult candidateCheck =
      checkClosedBoundWellFormed(candidate, location + ".candidate");
  if (!candidateCheck.accepted())
    return {std::nullopt, candidateCheck.refusal};
  RuntimeCheckResult ceilingCheck =
      checkClosedBoundWellFormed(ceiling, location + ".ceiling");
  if (!ceilingCheck.accepted())
    return {std::nullopt, ceilingCheck.refusal};

  if (candidate.quantity.constant.compare(ceiling.quantity.constant) > 0)
    return {false, std::nullopt};
  using QuantityKey = std::pair<std::string, uint64_t>;
  std::map<QuantityKey, registry::Rational> ceilingCoefficients;
  for (const ResourceMonomial &term : ceiling.quantity.resourceTerms)
    ceilingCoefficients.emplace(QuantityKey{term.resource, term.exponent},
                                term.coefficient);
  for (const ResourceMonomial &term : candidate.quantity.resourceTerms) {
    auto found =
        ceilingCoefficients.find(QuantityKey{term.resource, term.exponent});
    const registry::Rational allowed = found == ceilingCoefficients.end()
                                           ? registry::Rational()
                                           : found->second;
    if (term.coefficient.compare(allowed) > 0)
      return {false, std::nullopt};
  }
  for (const PrimitiveGameTerm &term : candidate.primitiveGameTerms) {
    auto found = std::find_if(ceiling.primitiveGameTerms.begin(),
                              ceiling.primitiveGameTerms.end(),
                              [&](const PrimitiveGameTerm &allowed) {
                                return primitiveKeyEqual(term, allowed);
                              });
    const registry::Rational allowed = found == ceiling.primitiveGameTerms.end()
                                           ? registry::Rational()
                                           : found->coefficient;
    if (term.coefficient.compare(allowed) > 0)
      return {false, std::nullopt};
  }
  return {true, std::nullopt};
}

ApplyOutcome applySoundnessRule(const SoundnessContext &context,
                                const SealedSoundnessView &sealed,
                                const ApplicationSite &site,
                                const ExactRef &bindingRef,
                                const TypedPremiseJudgments &premises) {
  const RuleBinding *binding = context.findBinding(bindingRef);
  if (!binding)
    return {std::nullopt, makeRefusal(RuntimePhase::BindingResolution,
                                      RuntimeRefusalCode::BindingMismatch,
                                      "apply.binding_ref",
                                      "APPLY names no exact selected binding")};
  const SoundnessRule *rule = context.findRule(binding->ruleRef);
  if (!rule)
    return {std::nullopt,
            makeRefusal(RuntimePhase::BindingResolution,
                        RuntimeRefusalCode::BindingMismatch, "apply.rule_ref",
                        "selected binding names no exact catalog rule")};
  auto subject = authorizeApplicationSite(sealed, site, *binding);
  if (!subject.accepted())
    return {std::nullopt, subject.refusal};
  auto coverage = checkClaimCoverage(sealed, site, *binding);
  if (!coverage.accepted())
    return {std::nullopt, coverage.refusal};

  ApplicationEnvironment application{
      context, sealed, site, *rule, *binding, std::move(*subject.value), {}};
  for (const TypedDeclaration &resource : rule->resources)
    application.evaluation.resources.emplace(resource.name, resource.sort);

  auto parameters = resolveNamedBindings(
      binding->parameterBindings, rule->parameters, application,
      application.evaluation.parameters, "apply.parameters");
  if (!parameters.accepted())
    return {std::nullopt, parameters.refusal};
  auto facts = resolveNamedBindings(binding->factBindings, rule->artifactFacts,
                                    application, application.evaluation.facts,
                                    "apply.facts");
  if (!facts.accepted())
    return {std::nullopt, facts.refusal};

  auto specialized = resolvePremises(premises, application);
  if (!specialized.accepted())
    return {std::nullopt, specialized.refusal};
  for (auto &[port, judgment] : *specialized.value)
    application.evaluation.premises.emplace(port, &judgment);

  auto pins = checkExactParameterPins(*rule, application);
  if (!pins.accepted())
    return {std::nullopt, pins.refusal};
  auto conditions = evaluateConditions(application);
  if (!conditions.accepted())
    return {std::nullopt, conditions.refusal};
  auto localHypotheses = instantiateLocalHypotheses(application);
  if (!localHypotheses.accepted())
    return {std::nullopt, localHypotheses.refusal};
  auto result = evaluateRuleBody(application);
  if (!result.accepted())
    return {std::nullopt, result.refusal};

  SecurityJudgment conclusion;
  conclusion.subject = application.conclusionSubject;
  conclusion.index = rule->conclusionIndex;
  conclusion.result = std::move(*result.value);
  conclusion.resourceVariables = rule->resources;
  for (const PremisePort &port : rule->premises) {
    const SecurityJudgment &premise =
        specialized.value->find(port.name)->second;
    for (const Hypothesis &hypothesis : premise.hypotheses)
      insertHypothesis(conclusion.hypotheses, hypothesis);
  }
  for (const Hypothesis &hypothesis : *localHypotheses.value)
    insertHypothesis(conclusion.hypotheses, hypothesis);

  RuntimeCheckResult conclusionCheck = checkSecurityJudgmentWellFormed(
      context.schemas(), conclusion, "apply.conclusion");
  if (!conclusionCheck.accepted())
    return {std::nullopt, conclusionCheck.refusal};
  AppliedJudgment applied;
  applied.site = site;
  applied.bindingRef = bindingRef;
  applied.specializedPremises = std::move(*specialized.value);
  applied.conclusion = std::move(conclusion);
  return {std::move(applied), std::nullopt};
}

DeriveOutcome deriveSoundness(const SoundnessContext &context,
                              const SealedSoundnessView &sealed,
                              const DerivationTarget &target,
                              const DerivationPlan &plan) {
  if (std::holds_alternative<ExternalJudgmentAssumption>(plan.node))
    return {
        std::nullopt,
        makeRefusal(RuntimePhase::Derivation,
                    RuntimeRefusalCode::PremiseMismatch, "derive.root",
                    "a protocol derivation root must be Apply, not Assume")};
  RuntimeCheckResult targetSubject =
      checkSecuritySubjectWellFormed(target.subject, "derive.target.subject");
  if (!targetSubject.accepted())
    return {std::nullopt, targetSubject.refusal};

  std::set<const DerivationPlan *> active;
  auto root = evaluatePlanNode(context, sealed, plan, active, "derive.root");
  if (!root.accepted())
    return {std::nullopt, root.refusal};
  const SecurityJudgment &conclusion = conclusionOf(*root.value);
  if (conclusion.subject != target.subject ||
      conclusion.index != target.index ||
      !declarationsEqual(conclusion.resourceVariables,
                         target.resourceVariables))
    return {std::nullopt,
            makeRefusal(RuntimePhase::Derivation,
                        RuntimeRefusalCode::PremiseMismatch, "derive.target",
                        "derived root does not equal the exact requested "
                        "subject/index/resource target")};
  DerivationResult result;
  result.artifactId = sealed.artifactId;
  result.target = target;
  result.root = std::move(*root.value);
  return {std::move(result), std::nullopt};
}

} // namespace zkc::soundness
