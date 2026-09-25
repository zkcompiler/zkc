#include "zkc/Compiler/Generic.h"
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
} // namespace

int main() {
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
