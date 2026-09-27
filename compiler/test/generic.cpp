#include "zkc/Contracts/Generic.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Variant.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc::generic;
using zkc::requirements::Predicate;

namespace {
void require(bool condition, StringRef why) {
  if (!condition) {
    errs() << why << '\n';
    std::exit(1);
  }
}
template <typename T> T accept(Expected<T> value) {
  if (!value) {
    errs() << toString(value.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*value);
}
template <typename T> void refuse(Expected<T> value, StringRef expected) {
  require(!value, "expected refusal");
  require(toString(value.takeError()) == expected, "wrong refusal");
}

void constantKinds() {
  auto variant = zkc::protocol::encodeVariant(
      {std::string(160, 'x'), {{"value", {"bool"}}}});
  require(bool(variant), "long Type fixture refused");
  std::string spelling = "fixed_vector<" + *variant + ",4>";
  require(spelling.size() > 255 && spelling.size() <= 4096,
          "Type fixture does not distinguish the constant bounds");
  accept(zkc::protocol::parseBoundType(spelling, false));
  Signature signature{{{{"Element", std::nullopt}, {"Length", std::nullopt}},
                       {"Type", "Nat"},
                       {{0, spelling}, {1, "1048576"}}},
                      {{"fixed_vector", {0, 1}}},
                      {{"fixed_vector", {0, 1}}},
                      {}};
  const std::vector<TypeConstructor> constructors{
      {"fixed_vector", {"Type", "Nat"}}};
  auto instantiated = accept(instantiate(signature, {}, {}));
  require(instantiated.scope.constants.at(0) == spelling,
          "Type constant lost its complete identity");
  accept(check(Function{instantiated, {}, {0}}, constructors, {}, {}));
  auto again = accept(instantiate(signature, {}, instantiated.scope));
  require(again.scope.terms.size() == 2,
          "complete Type constant was not interned");
  for (const auto &invalid :
       {spelling.substr(0, spelling.size() - 1),
        std::string("fixed_vector<bool,04>"),
        std::string("field:koala-bear@plonky3.koala-bear/1"),
        std::string(4097, 'x')}) {
    auto bad = signature;
    bad.scope.constants[0] = invalid;
    refuse(instantiate(bad, {}, {}), "generic-constant-type");
  }
  auto largeVariant = zkc::protocol::encodeVariant(
      {std::string(2100, 'x'), {{"value", {"bool"}}}});
  require(bool(largeVariant), "large variant fixture refused");
  auto tooLarge = "fixed_vector<" + *largeVariant + ",4>";
  require(tooLarge.size() > 4096, "structural bound fixture too small");
  auto bad = signature;
  bad.scope.constants[0] = tooLarge;
  refuse(instantiate(bad, {}, {}), "generic-constant-type");
  // Variant carriers retain their independently bounded canonical spelling.
  bad.scope.constants[0] = *largeVariant;
  accept(instantiate(bad, {}, {}));
  bad.scope.constants[0] =
      "variant:" + std::string(zkc::protocol::VariantSpellingBytes, '0');
  refuse(instantiate(bad, {}, {}), "generic-constant-type");
  for (StringRef natural : {"04", "1048577", "-1"}) {
    bad = signature;
    bad.scope.constants[1] = natural.str();
    refuse(instantiate(bad, {}, {}), "generic-constant-nat");
  }
  Signature domain{
      {{{"D", std::nullopt}}, {"domain"}, {{0, std::string(255, 'x')}}},
      {},
      {},
      {}};
  accept(instantiate(domain, {}, {}));
  domain.scope.constants[0].push_back('x');
  refuse(instantiate(domain, {}, {}), "generic-constant-scope");
}

void kindedApplications() {
  const std::vector<TypeConstructor> types{{"bool", {}},
                                           {"index", {}},
                                           {"field", {"domain"}},
                                           {"rng", {"domain"}, true},
                                           {"fixed_vector", {"Type", "Nat"}}};
  Scope scope{{{"F", std::nullopt},
               {"N", std::nullopt},
               {"field", std::nullopt, std::vector<unsigned>{0}},
               {"fixed_vector", std::nullopt, std::vector<unsigned>{2, 1}}},
              {"domain", "Nat", "Type", "Type"}};
  Type vector{"fixed_vector", {2, 1}};
  Signature signature{
      scope, {vector}, {vector}, {Predicate::holds("Element", {3, 2})}};
  accept(check(Function{signature, {}, {0}}, types, {}, {}));

  // Substitution follows the DAG, and only F and N are formal arguments.
  Scope caller{
      {{"Zero", std::nullopt}, {"K", std::nullopt}, {"Four", std::nullopt}},
      {"Nat", "domain", "Nat"},
      {{0, "0"}, {2, "4"}}};
  auto zero = accept(instantiate(signature, {1, 0}, caller));
  require(zero.scope.terms.size() == 5 &&
              zero.inputs[0].arguments == std::vector<unsigned>({3, 0}) &&
              zero.scope.terms[3].arguments == std::vector<unsigned>{1} &&
              zero.scope.terms[4].arguments == std::vector<unsigned>({3, 0}) &&
              zero.scope.sorts[4] == "Type" &&
              zero.requirements[0].arguments == std::vector<unsigned>({4, 3}),
          "nested application or obligation not substituted");
  auto repeated = accept(instantiate(signature, {1, 0}, zero.scope));
  require(repeated.scope.terms.size() == zero.scope.terms.size() &&
              repeated.inputs[0].arguments == zero.inputs[0].arguments &&
              repeated.requirements == zero.requirements,
          "identical applications not interned");
  auto four = accept(instantiate(signature, {1, 2}, repeated.scope));
  require(four.scope.terms.size() == 6 &&
              four.inputs[0].arguments == std::vector<unsigned>({3, 2}) &&
              four.scope.terms[5].arguments == std::vector<unsigned>({3, 2}) &&
              caller.terms.size() == 3 && signature.scope.terms.size() == 4,
          "Nat actuals aliased or original scopes mutated");
  refuse(instantiate(signature, {1}, caller), "generic-static-arity");
  refuse(instantiate(signature, {1, 0, 2, 2}, caller), "generic-static-arity");
  refuse(instantiate(signature, {0, 1}, caller), "generic-static-sort");

  // A Type formal can select a caller application directly. No conversion to
  // an opaque domain identity is involved.
  Signature typeParameter{
      {{{"T", std::nullopt}, {"N", std::nullopt}}, {"Type", "Nat"}},
      {{"fixed_vector", {0, 1}}},
      {},
      {}};
  auto selectedType = accept(instantiate(typeParameter, {3, 0}, zero.scope));
  require(selectedType.inputs[0].arguments == zero.inputs[0].arguments &&
              selectedType.scope.terms.size() == zero.scope.terms.size(),
          "Type actual application not bound as a root actual");
  refuse(instantiate(typeParameter, {1, 0}, zero.scope), "generic-static-sort");

  // Associated projections and applications share the same substitution map.
  auto projected = signature;
  projected.scope.terms[2] = {"Scalar", 0};
  projected.scope.sorts[2] = "domain";
  projected.scope.terms[3] = {"field", std::nullopt, std::vector<unsigned>{2}};
  projected.inputs[0].arguments = {3, 1};
  projected.outputs = projected.inputs;
  auto selectedProjection = accept(instantiate(projected, {1, 2}, caller));
  require(selectedProjection.scope.terms.size() == 5 &&
              selectedProjection.scope.terms[3].parent == 1 &&
              selectedProjection.scope.terms[4].arguments ==
                  std::vector<unsigned>{3} &&
              selectedProjection.inputs[0].arguments ==
                  std::vector<unsigned>({4, 2}),
          "application of mapped associated projection detached");
  accept(check(Function{selectedProjection, {}, {0}}, types, {}, {}));

  // Empty argument lists still denote applications, never formal roots.
  Signature nullary{
      {{{"bool", std::nullopt, std::vector<unsigned>{}}, {"N", std::nullopt}},
       {"Type", "Nat"}},
      {{"fixed_vector", {0, 1}}},
      {},
      {}};
  auto nullaryInstance = accept(instantiate(nullary, {2}, caller));
  require(nullaryInstance.scope.terms.size() == 4 &&
              nullaryInstance.scope.terms[3].arguments &&
              nullaryInstance.scope.terms[3].arguments->empty() &&
              nullaryInstance.inputs[0].arguments ==
                  std::vector<unsigned>({3, 2}),
          "nullary application treated as a formal root");
  accept(infer(Function{nullary, {}, {}}, types, {}));
  refuse(instantiate(nullary, {1, 2}, caller), "generic-static-arity");

  // Installed head, arity, argument kinds, and Type result sort all matter,
  // even for unused applications and unused installed operation signatures.
  for (const auto &arguments :
       std::vector<std::vector<unsigned>>{{}, {0, 1}, {1}}) {
    auto bad = signature;
    bad.scope.terms[2].arguments = arguments;
    refuse(infer(Function{bad, {}, {0}}, types, {}), "generic-application");
  }
  auto bad = signature;
  bad.scope.terms[3].arguments = std::vector<unsigned>{1, 2};
  refuse(infer(Function{bad, {}, {0}}, types, {}), "generic-application");
  bad = signature;
  bad.scope.terms[2].name = "source_invented_constructor";
  refuse(infer(Function{bad, {}, {0}}, types, {}), "generic-application");
  refuse(infer(Function{{}, {}, {}}, types, {{"unused", bad}}),
         "generic-application");
  auto ambiguous = types;
  ambiguous.push_back({"field", {"domain"}, true});
  refuse(infer(Function{signature, {}, {0}}, ambiguous, {}),
         "generic-application");
  for (StringRef sort : {"Nat", "domain"}) {
    bad = signature;
    bad.scope.sorts[2] = sort.str();
    refuse(infer(Function{bad, {}, {0}}, types, {}), "generic-application");
    refuse(instantiate(signature, {0, 1}, bad.scope), "generic-application");
  }
  bad = signature;
  bad.scope.terms[2].parent = 0;
  refuse(instantiate(bad, {1, 0}, caller), "generic-application");
  bad = signature;
  bad.scope.constants.emplace(2, "field:koala-bear");
  refuse(instantiate(bad, {1, 0}, caller), "generic-constant-scope");
  for (unsigned reference : {2, 3, 99}) {
    bad = signature;
    bad.scope.terms[2].arguments = std::vector<unsigned>{reference};
    refuse(infer(Function{bad, {}, {0}}, types, {}), "requirements-term");
  }
  bad = signature;
  bad.scope.terms.push_back(bad.scope.terms[2]);
  bad.scope.sorts.push_back("Type");
  refuse(infer(Function{bad, {}, {0}}, types, {}), "requirements-term");
  bad = signature;
  bad.scope.terms[2].arguments = std::vector<unsigned>(17, 0);
  refuse(infer(Function{bad, {}, {0}}, types, {}), "requirements-term");
  bad = signature;
  bad.inputs[0].arguments = {1, 2};
  refuse(infer(Function{bad, {}, {0}}, types, {}), "generic-type");
  bad = signature;
  bad.requirements = {Predicate::equal(1, 2)};
  refuse(infer(Function{bad, {}, {0}}, types, {}), "generic-equality-sort");

  // Existing congruence proves equality through two nested Type applications;
  // distinct natural constants do not gain an equality or arithmetic rule.
  Scope congruent{{{"F", std::nullopt},
                   {"G", std::nullopt},
                   {"N", std::nullopt},
                   {"field", std::nullopt, std::vector<unsigned>{0}},
                   {"field", std::nullopt, std::vector<unsigned>{1}},
                   {"fixed_vector", std::nullopt, std::vector<unsigned>{3, 2}},
                   {"fixed_vector", std::nullopt, std::vector<unsigned>{4, 2}}},
                  {"domain", "domain", "Nat", "Type", "Type", "Type", "Type"}};
  Signature equivalent{congruent,
                       {{"fixed_vector", {5, 2}}},
                       {{"fixed_vector", {6, 2}}},
                       {Predicate::equal(0, 1)}};
  auto proved = accept(check(Function{equivalent, {}, {0}}, types, {}, {}));
  require(!proved.derivation.goals.empty(), "application equality not checked");
  equivalent.requirements.clear();
  refuse(check(Function{equivalent, {}, {0}}, types, {}, {}),
         "generic-public-requirement");
  auto distinctNaturals = four;
  distinctNaturals.inputs = zero.inputs;
  refuse(check(Function{distinctNaturals, {}, {0}}, types, {}, {}),
         "generic-public-requirement");

  // Constructor base affinity composes with Type arguments, through arbitrary
  // nesting. Domain and Nat arguments do not themselves make values affine.
  auto duplicate = signature;
  duplicate.outputs.push_back(vector);
  accept(check(Function{duplicate, {}, {0, 0}}, types, {}, {}));
  duplicate.scope.terms[2].name = "rng";
  refuse(check(Function{duplicate, {}, {0, 0}}, types, {}, {}),
         "generic-resource-reuse");
  duplicate.inputs = {{"fixed_vector", {3, 1}}};
  duplicate.outputs = {duplicate.inputs[0], duplicate.inputs[0]};
  refuse(check(Function{duplicate, {}, {0, 0}}, types, {}, {}),
         "generic-resource-reuse");
  duplicate.scope.terms[2].name = "field";
  accept(check(Function{duplicate, {}, {0, 0}}, types, {}, {}));
  auto affineContainer = types;
  affineContainer.back().affine = true;
  refuse(check(Function{duplicate, {}, {0, 0}}, affineContainer, {}, {}),
         "generic-resource-reuse");

  Scope unknown{{{"T", std::nullopt}, {"N", std::nullopt}}, {"Type", "Nat"}};
  Type unknownVector{"fixed_vector", {0, 1}};
  Signature unknownSignature{
      unknown, {unknownVector}, {unknownVector, unknownVector}, {}};
  refuse(check(Function{unknownSignature, {}, {0, 0}}, types, {}, {}),
         "generic-resource-reuse");
  unknownSignature.outputs.pop_back();
  accept(check(Function{unknownSignature, {}, {0}}, types, {}, {}));
  unknownSignature.scope.constants.emplace(0, "field:koala-bear");
  unknownSignature.outputs.push_back(unknownVector);
  refuse(check(Function{unknownSignature, {}, {0, 0}}, types, {}, {}),
         "generic-resource-reuse");
  auto projectedPermission = signature;
  projectedPermission.scope.terms[2] = {"Element", 0};
  projectedPermission.outputs.push_back(vector);
  refuse(check(Function{projectedPermission, {}, {0, 0}}, types, {}, {}),
         "generic-resource-reuse");

  // Permission propagation also covers terms introduced by a call, not only
  // applications already present in the enclosing public signature.
  auto producer = signature;
  producer.inputs.clear();
  producer.requirements.clear();
  auto consumer = producer;
  consumer.inputs = {vector, vector};
  consumer.outputs.clear();
  Function calls{
      {{{{"F", std::nullopt}, {"N", std::nullopt}}, {"domain", "Nat"}},
       {},
       {},
       {}},
      {{"make", "make", {0, 1}, {}}, {"consume", "consume", {0, 1}, {0, 0}}},
      {}};
  accept(check(calls, types, {{"make", producer}, {"consume", consumer}}, {}));
  producer.scope.terms[2].name = "rng";
  consumer.scope.terms[2].name = "rng";
  refuse(check(calls, types, {{"make", producer}, {"consume", consumer}}, {}),
         "generic-resource-reuse");

  // A Type argument selected at the call keeps the caller application's known
  // permission. Equalities do not upgrade an otherwise unknown Type root.
  auto typeConsumer = typeParameter;
  typeConsumer.inputs.push_back(typeConsumer.inputs[0]);
  Function typedCall{zero, {{"consume", "consume", {3, 0}, {0, 0}}}, {}};
  typedCall.signature.outputs.clear();
  accept(check(typedCall, types, {{"consume", typeConsumer}}, {}));
  typedCall.signature.scope.terms[3].name = "rng";
  refuse(check(typedCall, types, {{"consume", typeConsumer}}, {}),
         "generic-resource-reuse");
  auto assumedPermission = signature;
  assumedPermission.scope.terms.push_back({"Unknown", std::nullopt});
  assumedPermission.scope.sorts.push_back("Type");
  assumedPermission.requirements.push_back(Predicate::equal(4, 2));
  assumedPermission.inputs = {{"fixed_vector", {4, 1}}};
  assumedPermission.outputs = {assumedPermission.inputs[0],
                               assumedPermission.inputs[0]};
  refuse(check(Function{assumedPermission, {}, {0, 0}}, types, {}, {}),
         "generic-resource-reuse");

  Signature loopSignature{
      unknown, {{"index", {}}, {"index", {}}, unknownVector}, {}, {}};
  Call loop{"loop", "", {}, {0, 1, 2}};
  loop.kind = Call::Kind::For;
  refuse(check(Function{loopSignature, {loop}, {}}, types, {}, {}),
         "local-control-capture");

  // Constants are rigid and intern by kind plus identity, independently of
  // display labels. Generated labels cannot capture an ordinary caller root.
  Signature constants{{{{"Count", std::nullopt},
                        {"Domain", std::nullopt},
                        {"Element", std::nullopt}},
                       {"Nat", "domain", "Type"},
                       {{0, "4"}, {1, "4"}, {2, "bool"}}},
                      {},
                      {},
                      {}};
  Scope collision{{{"$constant1", std::nullopt}}, {"Nat"}};
  auto fixed = accept(instantiate(constants, {}, collision));
  require(fixed.scope.terms.size() == 4 && fixed.scope.constants.size() == 3 &&
              fixed.scope.sorts[1] == "Nat" &&
              fixed.scope.sorts[2] == "domain" &&
              fixed.scope.sorts[3] == "Type" && !fixed.scope.constants.count(0),
          "constant kind erased or caller root captured");
  auto fixedAgain = accept(instantiate(constants, {}, fixed.scope));
  require(fixedAgain.scope.terms.size() == fixed.scope.terms.size(),
          "kinded constants not interned");
  refuse(instantiate(constants, {0}, collision), "generic-static-arity");
  auto ambiguousConstant = constants;
  ambiguousConstant.scope.sorts[1] = "Nat";
  refuse(instantiate(ambiguousConstant, {}, {}), "generic-constant-scope");
  for (StringRef identity : {"0", "4", "1048576"}) {
    auto natural = constants;
    natural.scope.constants[0] = identity.str();
    accept(instantiate(natural, {}, {}));
  }
  for (StringRef identity :
       {"00", "04", "+4", "-1", " 4", "4 ", "4.0", "4e0", "0x4", "1048577",
        "999999999999999999999", "four"}) {
    auto natural = constants;
    natural.scope.constants[0] = identity.str();
    refuse(instantiate(natural, {}, {}), "generic-constant-nat");
    refuse(instantiate(Signature{}, {}, natural.scope), "generic-constant-nat");
  }
  for (const std::string &identity : {std::string{}, std::string(256, '4')}) {
    auto natural = constants;
    natural.scope.constants[0] = identity;
    refuse(instantiate(natural, {}, {}), "generic-constant-scope");
  }
  for (const std::string &identity :
       {std::string("4\0", 2), std::string("\xef\xbc\x94")}) {
    auto natural = constants;
    natural.scope.constants[0] = identity;
    refuse(instantiate(natural, {}, {}), "generic-constant-nat");
  }

  auto fixedVector = signature;
  fixedVector.scope.constants.emplace(1, "4");
  auto selectedFixed = accept(instantiate(fixedVector, {1}, caller));
  require(selectedFixed.inputs[0].arguments == four.inputs[0].arguments &&
              selectedFixed.scope.constants.size() == caller.constants.size(),
          "fixed Nat root not interned with caller constant");

  // Re-interning at the bound is allowed; allocating the 129th term is not.
  Scope full;
  for (unsigned i = 0; i < 127; ++i) {
    full.terms.push_back({"N" + std::to_string(i), std::nullopt});
    full.sorts.push_back("Nat");
  }
  Signature oneApplication{
      {{{"bool", std::nullopt, std::vector<unsigned>{}}}, {"Type"}},
      {},
      {},
      {}};
  auto atLimit = accept(instantiate(oneApplication, {}, full));
  require(atLimit.scope.terms.size() == 128, "application limit off by one");
  auto atLimitAgain = accept(instantiate(oneApplication, {}, atLimit.scope));
  require(atLimitAgain.scope.terms.size() == 128,
          "re-interning at limit allocated a term");
  oneApplication.scope.terms[0].name = "index";
  refuse(instantiate(oneApplication, {}, atLimit.scope), "requirements-limit");
}
} // namespace

int main() {
  constantKinds();
  kindedApplications();
  Scope application{{{"Component", std::nullopt, std::vector<unsigned>{}}},
                    {"domain"}};
  refuse(instantiate(Signature{application, {}, {}, {}}, {}, application),
         "generic-application");
  Predicate invalidKind{static_cast<Predicate::Kind>(99), "Field", {0}};
  refuse(
      zkc::requirements::derive({{"F", std::nullopt}}, {invalidKind}, {}, {}),
      "requirements-predicate");
  refuse(
      zkc::requirements::derive({{"F", std::nullopt}}, {}, {}, {invalidKind}),
      "requirements-predicate");
  std::vector<TypeConstructor> types = {{"bool", {}},
                                        {"table", {"domain"}},
                                        {"round", {"domain"}},
                                        {"field", {"domain"}},
                                        {"group", {"group"}}};
  Scope field{{{"F", std::nullopt}}, {"domain"}};
  Type table{"table", {0}}, round{"round", {0}};
  Signature roundSignature{
      field, {table, table}, {round}, {Predicate::holds("CommRing", {0})}};
  std::vector<Operation> operations{{"product_round", roundSignature}};
  std::vector<zkc::requirements::Implication> rules{{"Field", "CommRing"}};
  Function polynomial{
      roundSignature, {{"round", "product_round", {0}, {0, 1}}}, {2}};
  auto checked = accept(check(polynomial, types, operations, rules));
  require(checked.inferred.values.size() == 3 &&
              checked.derivation.goals.size() == 1,
          "round obligations missing");

  // Inferring a stronger requirement never silently changes a public promise.
  auto broken = polynomial;
  broken.signature.requirements.clear();
  require(accept(infer(broken, types, operations)).obligations.size() == 1,
          "private inference lost body need");
  refuse(check(broken, types, operations, rules), "generic-public-requirement");
  broken.signature.requirements = {Predicate::holds("Field", {0})};
  accept(check(broken, types, operations, rules));
  auto fast = operations;
  fast.push_back({"interpolated_round", roundSignature});
  fast.back().signature.requirements.push_back(
      Predicate::holds("OddCharacteristic", {0}));
  accept(check(polynomial, types, fast, rules));
  broken.body[0].operation = "interpolated_round";
  refuse(check(broken, types, fast, rules), "generic-public-requirement");

  // Separate caller selections extend copies, leaving the shared template and
  // both caller scopes untouched. Two parameters can select one identity.
  Scope caller{{{"Fr", std::nullopt}, {"Binary", std::nullopt}},
               {"domain", "domain"}};
  auto first = accept(instantiate(roundSignature, {0}, caller));
  auto second = accept(instantiate(roundSignature, {1}, caller));
  require(first.inputs[0].arguments == std::vector<unsigned>{0} &&
              second.inputs[0].arguments == std::vector<unsigned>{1} &&
              roundSignature.scope.terms[0].name == "F" &&
              caller.terms.size() == 2,
          "instance mutation or binding alias");
  refuse(instantiate(roundSignature, {}, caller), "generic-static-arity");
  refuse(instantiate(roundSignature, {9}, caller), "generic-static-sort");

  // The same static machinery handles a group/scalar-action signature.
  Scope group{{{"G", std::nullopt}, {"Scalar", 0}}, {"group", "domain"}};
  Signature scale{group,
                  {{"group", {0}}, {"field", {1}}},
                  {{"group", {0}}},
                  {Predicate::holds("ScalarAction", {0, 1})}};
  operations.push_back({"scale", scale});
  Function groupFunction{scale, {{"scale", "scale", {0}, {0, 1}}}, {2}};
  accept(check(groupFunction, types, operations, rules));
  Scope curve{{{"Curve", std::nullopt}}, {"group"}};
  auto selected = accept(instantiate(scale, {0}, curve));
  require(selected.scope.terms.size() == 2 && curve.terms.size() == 1 &&
              selected.scope.terms[1].parent == 0 &&
              selected.scope.terms[1].name == "Scalar",
          "associated identity not substituted");
  refuse(instantiate(scale, {0}, caller), "generic-static-sort");
  auto badSort = curve;
  badSort.terms.push_back({"Scalar", 0});
  badSort.sorts.push_back("group");
  refuse(instantiate(scale, {0}, badSort), "generic-associated-sort");

  // A configured root is fixed, never captured by a caller argument with the
  // same sort. Its associated types follow that root; repeated use shares the
  // nominal constant without mutating either original scope.
  auto fixedScale = scale;
  fixedScale.scope.constants.emplace(0, "curve-one");
  auto fixed = accept(instantiate(fixedScale, {}, curve));
  require(fixed.inputs[0].arguments == std::vector<unsigned>{1} &&
              fixed.inputs[1].arguments == std::vector<unsigned>{2} &&
              fixed.scope.terms[2].parent == 1 && curve.terms.size() == 1,
          "fixed identity captured or associated member detached");
  auto repeated = accept(instantiate(fixedScale, {}, fixed.scope));
  require(repeated.scope.terms.size() == fixed.scope.terms.size(),
          "fixed identity not shared");
  refuse(instantiate(fixedScale, {0}, curve), "generic-static-arity");
  for (const auto &[index, identity] :
       std::vector<std::pair<unsigned, std::string>>{
           {9, "curve-one"},
           {1, "scalar-one"},
           {0, ""},
           {0, std::string(256, 'x')}}) {
    auto malformed = scale;
    malformed.scope.constants.emplace(index, identity);
    refuse(instantiate(malformed, {}, curve), "generic-constant-scope");
  }

  // Nullary operations still receive explicit static arguments; they cannot
  // recover an environment by inspecting runtime operands.
  Signature constant{
      field, {}, {{"field", {0}}}, {Predicate::holds("CommRing", {0})}};
  operations.push_back({"constant", constant});
  Function nullary{constant, {{"constant", "constant", {0}, {}}}, {0}};
  accept(check(nullary, types, operations, rules));
  nullary.body[0].staticArguments.clear();
  refuse(check(nullary, types, operations, rules), "generic-static-arity");

  Signature independent{{}, {{"bool", {}}}, {{"bool", {}}}, {}};
  accept(check(Function{independent, {}, {0}}, types, operations, rules));

  broken = polynomial;
  broken.body[0].inputs[0] = 2;
  refuse(check(broken, types, operations, rules), "generic-value-reference");
  broken = polynomial;
  broken.returns = {0};
  refuse(check(broken, types, operations, rules), "generic-signature");
  broken = polynomial;
  broken.body.push_back(broken.body[0]);
  refuse(check(broken, types, operations, rules), "generic-site");
  broken = polynomial;
  broken.body[0].operation = "unknown";
  refuse(check(broken, types, operations, rules), "generic-operation");
  broken = polynomial;
  broken.signature.inputs[0].constructor = "group";
  refuse(check(broken, types, operations, rules), "generic-type");
  outs() << "generic signature inference and immutable instantiation passed\n";
}
